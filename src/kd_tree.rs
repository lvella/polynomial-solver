use std::cmp::Ordering;

/// Implementation of the classical data structure k-dimensional tree for
/// multidimensional indexing.
pub struct KDTree<T: Entry> {
    num_dimensions: usize,
    root: Node<T>,
}

impl<T: Entry> KDTree<T> {
    pub fn new(num_dimensions: usize, elems: Vec<T>) -> Self {
        Self {
            num_dimensions,
            root: Node::new(num_dimensions, elems),
        }
    }

    pub fn insert(&mut self, new_entry: T) {
        if let Node::Empty = self.root {
            self.root = Node::Entry(new_entry);
        } else {
            self.root.insert(&new_entry, self.num_dimensions, 0);
        }
    }
}

enum Node<T: Entry> {
    Empty,
    Bifurcation {
        split_value: T::KeyElem,
        less_branch: Box<Self>,
        greater_or_equal_branch: Box<Self>,
    },
    Entry(T),
}

impl<T: Entry> Node<T> {
    fn new(num_dimensions: usize, elems: Vec<T>) -> Self {
        if elems.is_empty() {
            return Self::Empty;
        }

        // Sort the elements by each dimension of the key vector.
        let mut sorted_by_dim = Vec::new();
        sorted_by_dim.resize(num_dimensions, elems);
        for (idx, s) in sorted_by_dim.iter_mut().enumerate() {
            s.sort_unstable_by(|a, b| a.cmp(&b.get_key_elem(idx)));
        }

        // Recursively build the tree.
        let sorted_by_dim: Vec<(usize, &mut [T])> = sorted_by_dim
            .iter_mut()
            .enumerate()
            .map(|(dim, v)| (dim, &mut v[..]))
            .collect();
        Self::build_tree(sorted_by_dim)
    }

    /// Gets the set of elements to be inserted on the list sorted by each one
    /// of the key dimension and build the tree.
    fn build_tree(sorted_by_dim: Vec<(usize, &mut [T])>) -> Self {
        let mut iter = sorted_by_dim.into_iter();
        let (dim, working_list) = iter.next().unwrap();

        // Handle leaf case
        if working_list.len() == 1 {
            return Node::Entry(working_list[0]);
        }

        // Maybe eliminate this dimension if the elements are all equal on it.
        if working_list
            .first()
            .unwrap()
            .cmp(&working_list.last().unwrap().get_key_elem(dim))
            == Ordering::Equal
        {
            // All the elements have the same key on this dimension, so there is
            // no point indexing by it. Recurse with only the other dimensions.
            return Self::build_tree(iter.collect());
        }

        // Find the splitting point. Start from the middle
        // and search for the splitting point that best balance
        // both sides of the tree.
        let middle = working_list.len() / 2;
        let middle_elem = working_list[middle].get_key_elem(dim);

        // The default value for split_idx is for when there is an odd number of
        // elements, and all the elements are equal except for the last.
        let mut split_idx = working_list.len() - 1;
        for (low, high) in (0..middle).rev().zip(middle..) {
            match working_list[low].cmp(&middle_elem) {
                Ordering::Less => {
                    split_idx = low + 1;
                    break;
                }
                Ordering::Equal => {}
                Ordering::Greater => unreachable!(),
            }

            match working_list[high].cmp(&middle_elem) {
                Ordering::Less => unreachable!(),
                Ordering::Equal => {}
                Ordering::Greater => {
                    split_idx = high;
                    break;
                }
            }
        }
        drop(middle_elem);

        let split_value = working_list[split_idx].get_key_elem(dim);
        assert!(
            working_list[split_idx - 1].cmp(&split_value) == Ordering::Less,
            "bug: k-d tree splitting point is at the wrong place"
        );

        // Stable partition each sorted list by split_value
        let (mut less, mut greater_or_equal): (Vec<_>, Vec<_>) = iter
            .map(|(sorted_dim, sorted_list)| {
                let (less, greater_or_equal) =
                    stable_partition(sorted_list, |e| e.cmp(&split_value) == Ordering::Less);
                assert!(less.len() == split_idx);
                ((sorted_dim, less), (sorted_dim, greater_or_equal))
            })
            .unzip();

        // Insert current dimension split at the end, so to be thes last to be
        // processed again.
        let (l, ge) = working_list.split_at_mut(split_idx);
        less.push((dim, l));
        greater_or_equal.push((dim, ge));

        Node::Bifurcation {
            split_value,
            less_branch: Box::new(Self::build_tree(less)),
            greater_or_equal_branch: Box::new(Self::build_tree(greater_or_equal)),
        }
    }

    fn insert(&mut self, new_elem: &T, num_dimensions: usize, last_dim: usize) {
        match self {
            Node::Empty => unreachable!(),
            Node::Bifurcation {
                split_value,
                less_branch,
                greater_or_equal_branch,
            } => {
                let path = match new_elem.cmp(split_value) {
                    Ordering::Less => less_branch,
                    Ordering::Equal => greater_or_equal_branch,
                    Ordering::Greater => greater_or_equal_branch,
                };
                path.insert(new_elem, num_dimensions, split_value.dim_index());
            }
            Node::Entry(existing_elem) => {
                for i in 0..num_dimensions {
                    let dim = (i + last_dim) % num_dimensions;
                    let (l, ge): (&T, &T) = match existing_elem.cmp(&new_elem.get_key_elem(dim)) {
                        Ordering::Less => (existing_elem, new_elem),
                        Ordering::Equal => {
                            // Can't distinguish the elements by this dimension.
                            continue;
                        }
                        Ordering::Greater => (new_elem, existing_elem),
                    };

                    *self = Node::Bifurcation {
                        split_value: l.average_key_elem(ge, dim),
                        less_branch: Box::new(Node::Entry(*l)),
                        greater_or_equal_branch: Box::new(Node::Entry(*ge)),
                    };
                    return;
                }
                panic!("this k-d tree implementation does not support repeated elements");
            }
        }
    }
}

/// Partition a slice in two according to a predicate, preserving the relative
/// order. Returns two slices, the first with the elements matching the
/// predicate, and the second with the elements not matching.
fn stable_partition<T: Copy, P: Fn(&T) -> bool>(
    list: &mut [T],
    predicate: P,
) -> (&mut [T], &mut [T]) {
    let mut tmp = Vec::new();

    let mut src = 0;
    let mut dst = 0;
    while src < list.len() {
        if predicate(&list[src]) {
            list[dst] = list[src];
            dst += 1;
        } else {
            tmp.push(list[src]);
        }
        src += 1;
    }

    let (matching, unmatching) = list.split_at_mut(list.len() - tmp.len());
    unmatching.copy_from_slice(&tmp[..]);

    (matching, unmatching)
}

/// A k-dimensional vector entry for the k-dimensional tree.
///
/// This will be copied a lot, so make sure it is a small object.
pub trait Entry: Copy {
    type KeyElem: KeyElem;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem;

    /// Returns an key element in dimension dim in the range (self, other], i.e.
    /// at dimension dim it must be greater than self and less than or equal
    /// other, preferably the average between the two.
    ///
    /// `other.get_key_elem(dim);` is always a valid implementation, but if
    /// averaging is possible between key elements, it will give a slightly more
    /// balanced tree.
    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem;

    /// Compares the corresponding key element inside this entry with the
    /// provided key element.
    fn cmp(&self, other: &Self::KeyElem) -> Ordering;
}

/// One element of the k-dimensional key.
pub trait KeyElem {
    /// The index of this key element inside the KDEntry.
    fn dim_index(&self) -> usize;
}
