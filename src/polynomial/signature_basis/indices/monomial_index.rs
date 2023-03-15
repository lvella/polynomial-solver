use std::cell::Cell;

use crate::{
    kd_tree::{self, KDTree, SearchPath},
    polynomial::{
        divmask::DivMaskTestResult,
        monomial_ordering::Ordering,
        signature_basis::{get_var_exp_from_monomial, DivMap, MaskedMonomialRef},
        Id, VariablePower,
    },
};

use super::{make_dense_monomial, node_data_builder, MaskedMonomial, SignedExponent};

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

/// Alternative implementations of monomial index. For performance reasons, it
/// starts as a flat Vec<>, and only upon the first search a kD-tree is built
/// from the Vec<> elements.
enum Alternatives<O: Ordering, I: Id, E: SignedExponent> {
    Empty,
    Flat(Vec<MaskedMonomial<O, I, E>>),
    Tree(kd_tree::KDTree<MaskedMonomial<O, I, E>, MaskedMonomial<O, I, E>>),
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
        Self(Cell::new(Alternatives::Flat(elems)))
    }

    pub(in crate::polynomial::signature_basis) fn insert(
        &mut self,
        div_map: &DivMap<E>,
        elem: MaskedMonomial<O, I, E>,
    ) {
        match self.0.get_mut() {
            Alternatives::Flat(vec) => vec.push(elem),
            Alternatives::Tree(tree) => tree.insert(elem, &|e| e.clone(), &|a, b| {
                node_data_builder(div_map, a, b)
            }),
            Alternatives::Empty => self.0.set(Alternatives::Flat(vec![elem])),
        }
    }

    pub(in crate::polynomial::signature_basis) fn contains_divisor(
        &self,
        div_map: &DivMap<E>,
        num_dimensions: usize,
        monomial: MaskedMonomialRef<O, I, E>,
    ) -> bool {
        let alts = self.0.take();
        let tree = match alts {
            Alternatives::Empty => return false,
            Alternatives::Flat(vec) => {
                KDTree::new(num_dimensions, vec, &|entry| entry.clone(), &|a, b| {
                    node_data_builder(div_map, a, b)
                })
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
            Alternatives::Flat(vec) => vec.len(),
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
            Alternatives::Flat(vec) => vec,
            Alternatives::Tree(tree) => tree.to_vec(),
        }
    }
}
