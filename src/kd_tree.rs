use std::cell::Cell;
use std::cmp::Ordering;

use replace_with::replace_with_or_abort;

/// Implementation of the classical data structure k-dimensional tree for
/// multidimensional indexing.
///
/// Entry is the value stored in the leafs. Node data is some data built bottom
/// up the user may store in each branch node to help in the search.
pub struct KDTree<O: DataOperations> {
    ops: O,
    num_dimensions: usize,
    num_elems: usize,
    root: Option<Node<O>>,
}

impl<O: DataOperations> KDTree<O> {
    /// Creates a new KD-Tree with a given dimension.
    ///
    /// # Arguments:
    ///
    /// * `num_dimensions` - Number of dimensions of the indexed data.
    /// * `elems` - The elements to build the tree from.
    /// * `data_operations` - An object implementing DataOperations trait that
    ///   is stored for the whole lifetime of the KDTree.
    pub fn new(num_dimensions: usize, elems: Vec<O::Entry>, data_operations: O) -> Self {
        let num_elems = elems.len();
        let root = if num_elems > 0 {
            Some(Node::new(&data_operations, elems))
        } else {
            None
        };

        Self {
            ops: data_operations,
            num_dimensions,
            num_elems,
            root,
        }
    }

    /// Insert a new element and update all the node data up to the tree root.
    ///
    /// # Arguments
    ///
    /// * `new_entry` - The new entry to be inserted.
    pub fn insert(&mut self, new_entry: O::Entry) {
        self.num_elems += 1;
        if let Some(root) = &mut self.root {
            let new_node_data = self.ops.map(&new_entry);
            root.insert(&self.ops, new_entry, &new_node_data);
        } else {
            self.root = Some(Node::new(&self.ops, vec![new_entry]));
        }
    }

    /// Perform a tree search, where the user must provide the function telling
    /// which branch of the tree to search, and a function to process every
    /// entry found (which returns true if the search must continue, false
    /// otherwise).
    ///
    /// This function may actually modify the structure: if a searched leaf is
    /// bigger than some limit, it will be broken down into new branches.
    ///
    /// # Arguments
    ///
    /// * `discriminator` - A function that tells, from the KeyElem and
    ///   NodeData, which branches of a node must be searched.
    /// * `processor` - A function that is called for every leaf node reached.
    ///   Must return true if the search is to continue.
    pub fn search(
        &self,
        discriminator: &impl Fn(&<O::Entry as Entry>::KeyElem, &O::NodeData) -> SearchPath,
        processor: &mut impl FnMut(&O::Entry) -> bool,
    ) {
        if let Some(root) = &self.root {
            root.search(&self, 0, discriminator, processor);
        }
    }

    /// Return the number of entries.
    pub fn len(&self) -> usize {
        self.num_elems
    }

    /// Moves all the elements into a new Vec<E>, leaving the tree empty.
    ///
    /// It would be nice to implement a proper iterator, but that is too hard,
    /// would require up traversal in the tree, and just a Vec<E> is sufficient
    /// for now.
    pub fn to_vec(self) -> Vec<O::Entry> {
        let mut result = Vec::with_capacity(self.num_elems);

        if let Some(root) = self.root {
            result.reserve(self.num_elems);
            root.to_vec(&mut result);
        }

        result
    }
}

/// A leaf is actually a Vec with entries, that if bigger than this limit, will
/// be broken down upon searching.
const MAX_LEAF_SIZE: usize = 64;

/// What side of the branch a search must take.
#[derive(PartialEq, Eq)]
pub enum SearchPath {
    None,
    LessThan,
    GreaterOrEqualThan,
    Both,
}

struct Node<O: DataOperations> {
    node_data: O::NodeData,
    /// Either a leaf or the two children of a binary tree. This must be a Cell
    /// because during a query/search, a leaf may be broken down into branch if
    /// it is too big.
    path: Cell<NodePath<O>>,
}

/// The possible kinds of tree nodes.
enum NodePath<O: DataOperations> {
    Branch(Box<Bifurcation<O>>),
    Leaf(Vec<O::Entry>),
}
struct Bifurcation<O: DataOperations> {
    split_value: <O::Entry as Entry>::KeyElem,
    less_branch: Node<O>,
    greater_or_equal_branch: Node<O>,
}

impl<O: DataOperations> Node<O> {
    fn new(ops: &O, elems: Vec<O::Entry>) -> Self {
        let mut iter = elems.iter().map(|e| ops.map(e));
        let init = iter.next().unwrap();
        let node_data = iter.fold(init, |a, b| ops.accum(a, &b));
        Node {
            node_data,
            path: Cell::new(NodePath::Leaf(elems)),
        }
    }

    fn insert(&mut self, ops: &O, new_elem: O::Entry, new_node_data: &O::NodeData) {
        replace_with_or_abort(&mut self.node_data, |node_data| {
            ops.accum(node_data, new_node_data)
        });
        match self.path.get_mut() {
            NodePath::Branch(b) => {
                let path = match new_elem.cmp_dim(&b.split_value) {
                    Ordering::Less => &mut b.less_branch,
                    _ => &mut b.greater_or_equal_branch,
                };

                path.insert(ops, new_elem, new_node_data);
            }
            NodePath::Leaf(elems) => elems.push(new_elem),
        }
    }

    fn search(
        &self,
        kd: &KDTree<O>,
        next_dim: usize,
        discriminator: &impl Fn(&<O::Entry as Entry>::KeyElem, &O::NodeData) -> SearchPath,
        processor: &mut impl FnMut(&O::Entry) -> bool,
    ) -> bool {
        // Take the path out of the Cell, temporarily replacing with an
        // empty one (I hope this to be optimized away).
        let path = self.path.replace(NodePath::Leaf(Vec::new()));

        let (result, new_path) = match path {
            NodePath::Branch(bifurcation) => (
                self.branch_search(kd, &bifurcation, discriminator, processor),
                NodePath::Branch(bifurcation),
            ),
            NodePath::Leaf(elems) => {
                if elems.len() <= MAX_LEAF_SIZE {
                    (elems.iter().all(processor), NodePath::Leaf(elems))
                } else {
                    // The leaf is too big and must be broken up.
                    let bifurcation = Self::bifurcate(&kd.ops, next_dim, kd.num_dimensions, elems);

                    // Do the search on the newly generated branches:
                    let result = self.branch_search(kd, &bifurcation, discriminator, processor);

                    (result, NodePath::Branch(bifurcation))
                }
            }
        };

        self.path.set(new_path);

        result
    }

    fn branch_search(
        &self,
        kd: &KDTree<O>,
        bifurcation: &Bifurcation<O>,
        discriminator: &impl Fn(&<O::Entry as Entry>::KeyElem, &O::NodeData) -> SearchPath,
        processor: &mut impl FnMut(&O::Entry) -> bool,
    ) -> bool {
        let next_dim = bifurcation.split_value.dim_index() + 1;
        match discriminator(&bifurcation.split_value, &self.node_data) {
            SearchPath::None => true,
            SearchPath::LessThan => {
                bifurcation
                    .less_branch
                    .search(kd, next_dim, discriminator, processor)
            }
            SearchPath::GreaterOrEqualThan => {
                bifurcation
                    .greater_or_equal_branch
                    .search(kd, next_dim, discriminator, processor)
            }
            SearchPath::Both => {
                bifurcation
                    .less_branch
                    .search(kd, next_dim, discriminator, processor)
                    && bifurcation.greater_or_equal_branch.search(
                        kd,
                        next_dim,
                        discriminator,
                        processor,
                    )
            }
        }
    }

    fn bifurcate(
        ops: &O,
        next_dim: usize,
        num_dimensions: usize,
        mut elems: Vec<O::Entry>,
    ) -> Box<Bifurcation<O>> {
        // Attempt attempt to bifurcate on every dimension, starting from
        // next_dim, until we find one that partition the vector in two. It will
        // most likely succeed on the first iteration.
        for i in 0..num_dimensions {
            let dim = (next_dim + i) % num_dimensions;

            let mut iter = elems.iter();
            let mut max = iter.next().unwrap();
            let mut min = max;
            for e in iter {
                let key = e.get_key_elem(dim);
                if let Ordering::Greater = min.cmp_dim(&key) {
                    min = e;
                }
                if let Ordering::Less = max.cmp_dim(&key) {
                    max = e;
                }
            }

            match min.cmp_dim(&max.get_key_elem(dim)) {
                Ordering::Less => {
                    // Fist element is different from the last at this dimension, so
                    // we can use this dim for partitioning.
                    let avg_filter = min.average_filter(max, dim);

                    let less_than: Vec<_> = elems.drain_filter(|e| avg_filter.is_less(e)).collect();
                    // TODO: maybe elems.shrink_to_fit() ? If doing it, it would be
                    // better to do it after all the recursive splits.
                    //elems.shrink_to_fit();

                    let split_value = match avg_filter.into_key() {
                        Some(key) => key,
                        None => {
                            // Use as partition key the smallest element in the equal or greater side.
                            let mut iter = elems.iter();
                            let split_value = iter.next().unwrap();
                            let mut key = split_value.get_key_elem(dim);
                            for e in iter {
                                if let Ordering::Less = e.cmp_dim(&key) {
                                    key = e.get_key_elem(dim);
                                }
                            }
                            key
                        }
                    };

                    return Box::new(Bifurcation {
                        split_value,
                        less_branch: Node::new(ops, less_than),
                        greater_or_equal_branch: Node::new(ops, elems),
                    });
                }
                Ordering::Equal => {
                    // This dimension can't be used for partitioning, continue
                    // the loop to use the next.
                }
                Ordering::Greater => unreachable!(),
            }
        }

        panic!("this k-d tree implementation does not support repeated elements");
    }

    fn to_vec(self, vec: &mut Vec<O::Entry>) {
        match self.path.into_inner() {
            NodePath::Branch(bifurcation) => {
                bifurcation.less_branch.to_vec(vec);
                bifurcation.greater_or_equal_branch.to_vec(vec);
            }
            NodePath::Leaf(mut elems) => vec.append(&mut elems),
        }
    }
}

/// Filter that tell if entries are less than some KeyElem.
pub trait PartitionFilter: Sized {
    type Entry: Entry;

    /// Returns true if entry is less.
    fn is_less(&self, e: &Self::Entry) -> bool;

    /// Turn the filter into a key that is greater than all elements that would
    /// have been classified as less, and only them.
    ///
    /// If None, the classification must be sound: all the less elements must be
    /// smaller than the greater elements.
    fn into_key(self) -> Option<<Self::Entry as Entry>::KeyElem>;
}

/// A k-dimensional vector entry for the k-dimensional tree.
///
/// This will be moved a lot.
pub trait Entry {
    type KeyElem: KeyElem;
    type PartitionFilter: PartitionFilter<Entry = Self>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem;

    /// Returns a partition filter that splits elements at dim, on the average
    /// between `self` and `other`.
    ///
    /// `self` and `other` are guaranteed to be distinct, and the resulting
    /// filter must classify `self` as less and `other` as not less.
    ///
    /// The closer the filter splits the space at the average between `self` and
    /// `other`, the more balanced the tree will be.
    fn average_filter(&self, other: &Self, dim: usize) -> Self::PartitionFilter;

    /// Compares the corresponding key element inside this entry with the
    /// provided key element.
    fn cmp_dim(&self, other: &Self::KeyElem) -> Ordering;
}

/// One element of the k-dimensional key.
pub trait KeyElem {
    /// The index of this key element inside the KDEntry.
    fn dim_index(&self) -> usize;
}

/// Trait defining the data types and operations to build the tree nodes.
///
/// Unlike Rust's std collections, this is an actual object passed to the
/// kD-tree, which allows for greater flexibility (this is one thing Rust did
/// worse than C++, not having comparator objects for the data structures).
pub trait DataOperations {
    /// The entry this node data is built from.
    type Entry: Entry;

    /// The user defined data stored in every Node to help in the search. It is
    /// built from the entries stored below the node, using the functions
    /// defined in this trait.
    type NodeData: Clone;

    /// Translates an Entry to a NodeData.
    fn map(&self, entry: &Self::Entry) -> Self::NodeData;

    /// Commutative and associative function to accumulate two NodeData into
    /// one, so that the data from a node is build as the accumulation of all
    /// NodeData below it.
    fn accum(&self, a: Self::NodeData, other: &Self::NodeData) -> Self::NodeData;
}

#[cfg(test)]
mod tests {

    use std::marker::PhantomData;

    use itertools::Itertools;
    use rand::{
        distributions::{Alphanumeric, DistString},
        rngs::StdRng,
        Rng, SeedableRng,
    };

    use super::*;

    /// Characters used in the string part of the key:
    const CHARS: &[u8] = b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

    const fn alphanumeric_rev_map() -> [char; CHARS.len() + 1] {
        let mut ret = ['\0'; CHARS.len() + 1];

        let mut i = 0;
        while i < CHARS.len() {
            ret[i + 1] = CHARS[i] as char;
            i += 1;
        }

        ret
    }

    /// Maps characters used in the key to ints in order to calculate average.
    const fn alphanumeric_map() -> [u8; 'z' as usize + 1] {
        let mut ret = [0; 'z' as usize + 1];

        let mut i = 0;
        while i < CHARS.len() {
            ret[CHARS[i] as usize] = i as u8 + 1;
            i += 1;
        }

        ret
    }

    /// Defines a 10 dimensional value with 1 string and 9 integers.
    type TestValue = (String, [i8; 9]);

    /// The entry actually inserted is a reference into the value.
    type TestEntry<'a> = &'a TestValue;

    /// The key element is either a pointer to the string or one of the integers.
    pub enum TestKeyElement<'a> {
        Str(&'a str),
        Int { dim: u8, val: i8 },
    }

    /// The implementation of DataOperation trait.
    struct TestOps<'a>(PhantomData<&'a ()>);

    impl<'a> DataOperations for TestOps<'a> {
        type Entry = TestEntry<'a>;

        type NodeData = ();

        fn map(&self, _: &Self::Entry) -> Self::NodeData {}

        fn accum(&self, _: Self::NodeData, _: &Self::NodeData) -> Self::NodeData {}
    }

    pub enum TestFilter<'a> {
        Str(String, PhantomData<&'a ()>),
        Int { dim: u8, val: i8 },
    }

    impl<'a> PartitionFilter for TestFilter<'a> {
        type Entry = TestEntry<'a>;

        fn is_less(&self, e: &Self::Entry) -> bool {
            match self {
                TestFilter::Str(s, _) => e.0 < *s,
                TestFilter::Int { dim, val } => e.1[(dim - 1) as usize] < *val,
            }
        }

        fn into_key(self) -> Option<<Self::Entry as Entry>::KeyElem> {
            match self {
                TestFilter::Str(_, _) => None,
                TestFilter::Int { dim, val } => Some(TestKeyElement::Int { dim, val }),
            }
        }
    }

    type TestKDTree<'a> = KDTree<TestOps<'a>>;

    impl<'a> Entry for TestEntry<'a> {
        type KeyElem = TestKeyElement<'a>;
        type PartitionFilter = TestFilter<'a>;

        fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
            if dim == 0 {
                TestKeyElement::Str(&self.0)
            } else {
                TestKeyElement::Int {
                    dim: dim as u8,
                    val: self.1[dim - 1],
                }
            }
        }

        fn average_filter(&self, other: &Self, dim: usize) -> Self::PartitionFilter {
            if dim == 0 {
                // To average 2 substrings find the common prefix (it will be
                // part of the result) then average the next different
                // character.
                const MAP: [u8; 123] = alphanumeric_map();
                const REV_MAP: [char; 63] = alphanumeric_rev_map();

                let iter = self.0.chars().zip_longest(other.0.chars());
                let mut avg_str = String::with_capacity(iter.size_hint().0);

                for pair in iter {
                    let (a, b) = match pair {
                        itertools::EitherOrBoth::Both(a, b) => {
                            if a == b {
                                avg_str.push(a);
                                continue;
                            } else {
                                (MAP[a as usize], MAP[b as usize])
                            }
                        }
                        itertools::EitherOrBoth::Right(b) => (0, MAP[b as usize]),
                        itertools::EitherOrBoth::Left(_) => unreachable!(),
                    };

                    let avg = (a + b + 1) / 2;
                    assert!(avg > 0);
                    avg_str.push(REV_MAP[avg as usize]);
                    break;
                }
                TestFilter::Str(avg_str, PhantomData {})
            } else {
                let lower = self.1[dim - 1];
                let higher = other.1[dim - 1];

                TestFilter::Int {
                    dim: dim as u8,
                    val: div_up(lower + higher, 2),
                }
            }
        }

        fn cmp_dim(&self, other: &Self::KeyElem) -> Ordering {
            match other {
                TestKeyElement::Str(other) => self.0.as_str().cmp(other),
                TestKeyElement::Int { dim, val } => self.1[(dim - 1) as usize].cmp(val),
            }
        }
    }

    fn div_up(a: i8, b: i8) -> i8 {
        (a + (b - 1)) / b
    }

    impl<'a> KeyElem for TestKeyElement<'a> {
        fn dim_index(&self) -> usize {
            match self {
                TestKeyElement::Str(_) => 0,
                TestKeyElement::Int { dim, val: _ } => *dim as usize,
            }
        }
    }

    fn rand_string<R: Rng>(rng: &mut R) -> String {
        let size = rng.gen_range(2usize..=10);
        Alphanumeric.sample_string(rng, size)
    }

    #[test]
    fn build_and_query() {
        let mut rng = StdRng::seed_from_u64(42);

        // Generate 10000 elements to be inserted into the k-d tree.
        // Just hope they are distinct for the seed given.
        let mut elem_vec = Vec::new();
        while elem_vec.len() < 10000 {
            let mut new_elem = (rand_string(&mut rng), [0i8; 9]);
            for e in new_elem.1.iter_mut() {
                *e = rng.gen_range(-50..=50);
            }
            elem_vec.push(new_elem);
        }

        // Build the k-d tree with only the first 8000 elements and run the
        // query test.
        let originals = &elem_vec[..8000];
        let mut kdtree = TestKDTree::new(10, originals.iter().collect(), TestOps(PhantomData {}));
        query_test(&kdtree, originals);

        // Insert the remaining elements and redo the query test.
        for e in elem_vec[8000..].iter() {
            kdtree.insert(e);
        }
        query_test(&kdtree, &elem_vec);
    }

    fn query_test(kdtree: &TestKDTree, elems: &[TestValue]) {
        // Search all elements less than or equal the reference:
        let reference: TestValue = ("Q".into(), [-12, 0, -7, 18, 40, -3, -39, 30, 30]);

        let is_less_or_equal = |e: &TestEntry| {
            (0usize..10).all(|dim| e.cmp_dim(&(&reference).get_key_elem(dim)) != Ordering::Greater)
        };

        let mut tree_found = Vec::new();
        kdtree.search(
            &|key, _| match (&reference).cmp_dim(key) {
                Ordering::Less => SearchPath::LessThan,
                Ordering::Equal => SearchPath::Both,
                Ordering::Greater => SearchPath::Both,
            },
            &mut |e| {
                if is_less_or_equal(e) {
                    tree_found.push(*e);
                }
                true
            },
        );
        tree_found.sort();

        // Linearly filter from the total set of elements, for comparison:
        let mut filtered_found: Vec<TestEntry> = elems.iter().filter(is_less_or_equal).collect();
        filtered_found.sort();
        assert!(tree_found == filtered_found);

        for (a, b) in tree_found.iter().zip(filtered_found.iter()) {
            println!("{:?}, {:?}", **a, **b);
        }
        println!("{}, {}", tree_found.len(), filtered_found.len());
    }
}
