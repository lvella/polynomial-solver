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

/// Given an slice ordered by some dimension, searches for the point that best
/// divides the slice in two in the most balanced way, so that all equal keys
/// remains together.
///
/// I.e: `[aabbbc]` is split into `[aa]` and `[bbbc]`, which is better than
/// `[aabbb]` and `[c]`.
fn optimal_partition_value<E: Entry>(dim: usize, sorted_list: &[E]) -> (usize, E::KeyElem) {
    // Find the splitting point. Start from the middle
    // and search for the splitting point that best balance
    // both sides of the tree.
    let middle = sorted_list.len() / 2;
    let middle_elem = sorted_list[middle].get_key_elem(dim);

    // The default value for split_idx is for when there is an odd number of
    // elements, and all the elements are equal except for the last.
    let mut split_idx = sorted_list.len() - 1;
    for (low, high) in (0..middle).rev().zip(middle..) {
        match sorted_list[low].cmp_dim(&middle_elem) {
            Ordering::Less => {
                split_idx = low + 1;
                break;
            }
            Ordering::Equal => {}
            Ordering::Greater => unreachable!(),
        }

        match sorted_list[high].cmp_dim(&middle_elem) {
            Ordering::Less => unreachable!(),
            Ordering::Equal => {}
            Ordering::Greater => {
                split_idx = high;
                break;
            }
        }
    }
    drop(middle_elem);

    let split_value = sorted_list[split_idx].get_key_elem(dim);
    assert!(
        sorted_list[split_idx - 1].cmp_dim(&split_value) == Ordering::Less,
        "bug: k-d tree splitting point is at the wrong place"
    );

    (split_idx, split_value)
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

            elems.sort_unstable_by(|a, b| a.cmp_dim(&b.get_key_elem(dim)));
            if elems[0].cmp_dim(&elems.last().unwrap().get_key_elem(dim)) != Ordering::Equal {
                // Fist element is different from the last at this dimension, so
                // we can use this dim for partitioning.
                let (split_point, split_value) = optimal_partition_value(dim, &elems);

                let gt_eq = elems.split_off(split_point);
                // TODO: maybe elems.shrink_to_fit() ? If doing it, it would be
                // better to do it after all the recursive splits.
                //elems.shrink_to_fit();

                return Box::new(Bifurcation {
                    split_value,
                    less_branch: Node::new(ops, elems),
                    greater_or_equal_branch: Node::new(ops, gt_eq),
                });
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

/// A k-dimensional vector entry for the k-dimensional tree.
///
/// This will be copied a lot, so make sure it is a small object.
pub trait Entry: Clone {
    type KeyElem: KeyElem;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem;

    /// Returns a key element in dimension dim in the range defined by
    /// (self, other], i.e. at dimension dim it must be greater than self
    /// and less than or equal other, preferably the average between the two.
    ///
    /// `other.get_key_elem(dim);` is always a valid implementation, but if
    /// averaging is possible between key elements, it will give a slightly more
    /// balanced tree.
    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem;

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

    use rand::{
        distributions::{Alphanumeric, DistString},
        rngs::StdRng,
        Rng, SeedableRng,
    };

    use super::*;

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

    type TestKDTree<'a> = KDTree<TestOps<'a>>;

    impl<'a> Entry for TestEntry<'a> {
        type KeyElem = TestKeyElement<'a>;

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

        fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem {
            if dim == 0 {
                // Too hard to average two strings, just return the bigger one.
                other.get_key_elem(0)
            } else {
                let lower = self.1[dim - 1];
                let higher = other.1[dim - 1];

                TestKeyElement::Int {
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
