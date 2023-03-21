use std::{cell::Cell, marker::PhantomData, rc::Rc};

use crate::{
    kd_tree::{self, DataOperations, KDTree, SearchPath},
    polynomial::{
        divmask::DivMaskTestResult,
        monomial_ordering::Ordering,
        signature_basis::{get_var_exp_from_monomial, DivMap, MaskedMonomialRef},
        Id, VariablePower,
    },
};

use super::{make_dense_monomial, MaskedMonomial, SignedExponent};

/// Optimization parameter: ideally, this should be the size where linear searching the large vector for
/// a divisor outweighs the increased cost of inserting on a kD-tree.
const MAX_VEC_SIZE: usize = 2048;

/// Optimization parameter: ideally, this should be the size where log searching
/// the kD-tree becomes faster than linear searching a vector.
///
/// TODO: maybe this optimization should be implemented inside the kD-tree, and
/// only split a Vec node when searching.
const MIN_VEC_SIZE: usize = 128;

/// Optimization parameter: ideally, this should be the minimum number of
/// searches per each insertion that makes it faster to use a kD-tree instead of
/// a plain vector.
const MIN_SEARCHES_PER_INSERTIONS: i64 = 10;

impl<O: Ordering, I: Id, E: SignedExponent> kd_tree::Entry for MaskedMonomial<O, I, E> {
    type KeyElem = VariablePower<I, E>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
        let id = I::from_idx(dim);
        let power = get_var_exp_from_monomial(&self.monomial, &id);
        VariablePower { id, power }
    }

    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem {
        let id = I::from_idx(dim);

        let exp_a = get_var_exp_from_monomial(&self.monomial, &id);
        let exp_b = get_var_exp_from_monomial(&other.monomial, &id);
        let avg = (exp_a + exp_b + E::one()) / E::from(2);
        VariablePower { id, power: avg }
    }

    fn cmp_dim(&self, other: &Self::KeyElem) -> std::cmp::Ordering {
        get_var_exp_from_monomial(&self.monomial, &other.id).cmp(&other.power)
    }
}

impl<I: Id, E: SignedExponent> kd_tree::KeyElem for VariablePower<I, E> {
    fn dim_index(&self) -> usize {
        self.id.to_idx()
    }
}

/// Struct implementing the operations needed on building the kD-Tree.
struct Operations<O: Ordering, I: Id, E: SignedExponent> {
    div_map: Rc<DivMap<E>>,
    _phantom: PhantomData<(O, I)>,
}

impl<O: Ordering, I: Id, E: SignedExponent> DataOperations for Operations<O, I, E> {
    type Entry = MaskedMonomial<O, I, E>;

    type NodeData = MaskedMonomial<O, I, E>;

    /// Creates a monomial mask from the leading monomial of the entry.
    fn map(&self, entry: &Self::Entry) -> Self::NodeData {
        entry.clone()
    }

    /// GCD between NodeData
    fn accum(&self, a: Self::NodeData, other: &Self::NodeData) -> Self::NodeData {
        a.gcd(other, &self.div_map)
    }
}

/// Alternative implementations of monomial index. For performance reasons, it
/// starts as a flat Vec<>, and only upon the first search a kD-tree is built
/// from the Vec<> elements.
enum Alternatives<O: Ordering, I: Id, E: SignedExponent> {
    Empty,
    Flat {
        /// The weighted balance between insertions and lookups, so that when it is
        /// positive, it should be more worth to use a tree instead of a vec.
        usage_balance: i64,
        vec: Vec<MaskedMonomial<O, I, E>>,
    },
    Tree(kd_tree::KDTree<Operations<O, I, E>>),
}

impl<O: Ordering, I: Id, E: SignedExponent> Default for Alternatives<O, I, E> {
    fn default() -> Self {
        Self::Empty
    }
}

/// A collection of signatures with search for a divisor accelerated with
/// KD-tree. Useful for implementing signature criterion.
///
/// The tree is lazily created upon first usage.
pub struct MonomialIndex<O: Ordering, I: Id, E: SignedExponent>(Cell<Alternatives<O, I, E>>);

impl<O: Ordering, I: Id, E: SignedExponent> MonomialIndex<O, I, E> {
    /// Creates a new lazy tree index from known elements.
    pub(in crate::polynomial::signature_basis) fn new(elems: Vec<MaskedMonomial<O, I, E>>) -> Self {
        Self(Cell::new(Alternatives::Flat {
            usage_balance: -MIN_SEARCHES_PER_INSERTIONS,
            vec: elems,
        }))
    }

    pub(in crate::polynomial::signature_basis) fn insert(&mut self, elem: MaskedMonomial<O, I, E>) {
        match self.0.get_mut() {
            Alternatives::Flat { vec, usage_balance } => {
                *usage_balance -= MIN_SEARCHES_PER_INSERTIONS;
                vec.push(elem);
            }
            Alternatives::Tree(tree) => tree.insert(elem),
            Alternatives::Empty => self.0.set(Alternatives::Flat {
                vec: vec![elem],
                usage_balance: -MIN_SEARCHES_PER_INSERTIONS,
            }),
        }
    }

    pub(in crate::polynomial::signature_basis) fn contains_divisor(
        &self,
        div_map: &Rc<DivMap<E>>,
        num_dimensions: usize,
        monomial: MaskedMonomialRef<O, I, E>,
    ) -> bool {
        let alts = self.0.take();
        let tree = match alts {
            Alternatives::Empty => return false,
            Alternatives::Flat { vec, usage_balance } => {
                let len = vec.len();
                if len > MIN_VEC_SIZE && (len > MAX_VEC_SIZE || usage_balance > 0) {
                    KDTree::new(
                        num_dimensions,
                        vec,
                        Operations {
                            div_map: div_map.clone(),
                            _phantom: PhantomData {},
                        },
                    )
                } else {
                    let result = vec.iter().any(|elem| elem.divides(&monomial));
                    self.0.set(Alternatives::Flat {
                        vec,
                        usage_balance: usage_balance + 1,
                    });
                    return result;
                }
            }
            Alternatives::Tree(tree) => tree,
        };

        let dense_monomial = make_dense_monomial(monomial.1);
        let mut found_divisor = false;

        tree.search(
            &|key, inner_gcd| {
                // TODO: is it worth to do a full divisibility test here, instead of only the divmask???
                if let DivMaskTestResult::NotDivisible = inner_gcd.divmask.divides(monomial.0) {
                    return SearchPath::None;
                }

                if let Some(exp) = dense_monomial.get(key.id.to_idx()) {
                    if *exp < key.power {
                        return SearchPath::LessThan;
                    }
                }

                SearchPath::Both
            },
            &mut |entry| {
                if entry.divides(&monomial) {
                    found_divisor = true;

                    // Stop search:
                    false
                } else {
                    // Continue search:
                    true
                }
            },
        );

        self.0.set(Alternatives::Tree(tree));

        found_divisor
    }

    pub fn len(&self) -> usize {
        let alts = self.0.take();
        let len = match &alts {
            Alternatives::Empty => 0,
            Alternatives::Flat {
                vec,
                usage_balance: _,
            } => vec.len(),
            Alternatives::Tree(tree) => tree.len(),
        };
        self.0.set(alts);

        len
    }

    pub(in crate::polynomial::signature_basis) fn to_vec(
        &mut self,
    ) -> Vec<MaskedMonomial<O, I, E>> {
        let alts = self.0.take();
        match alts {
            Alternatives::Empty => vec![],
            Alternatives::Flat {
                vec,
                usage_balance: _,
            } => vec,
            Alternatives::Tree(tree) => tree.to_vec(),
        }
    }
}
