use crate::{
    kd_tree::{self, SearchPath},
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

/// A collection of signatures with search for a divisor accelerated with
/// KD-tree. Useful for implementing signature criterion.
pub struct MonomialIndex<O: Ordering, I: Id, E: SignedExponent>(
    kd_tree::KDTree<MaskedMonomial<O, I, E>, MaskedMonomial<O, I, E>>,
);

impl<O: Ordering, I: Id, E: SignedExponent> MonomialIndex<O, I, E> {
    /// Creates a (somewhat balanced) new tree index from known elements.
    pub(in crate::polynomial::signature_basis) fn new(
        num_dimensions: usize,
        div_map: &DivMap<E>,
        elems: Vec<MaskedMonomial<O, I, E>>,
    ) -> Self {
        Self(kd_tree::KDTree::new(
            num_dimensions,
            elems,
            &|entry| entry.clone(),
            &|a, b| node_data_builder(div_map, a, b),
        ))
    }

    pub(in crate::polynomial::signature_basis) fn insert(
        &mut self,
        div_map: &DivMap<E>,
        elem: MaskedMonomial<O, I, E>,
    ) {
        self.0.insert(elem, &|e| e.clone(), &|a, b| {
            node_data_builder(div_map, a, b)
        })
    }

    pub(in crate::polynomial::signature_basis) fn contains_divisor(
        &self,
        monomial: MaskedMonomialRef<O, I, E>,
    ) -> bool {
        let dense_monomial = make_dense_monomial(monomial.1);

        let mut found_divisor = false;

        self.0.search(
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

        found_divisor
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub(in crate::polynomial::signature_basis) fn to_vec(
        &mut self,
    ) -> Vec<MaskedMonomial<O, I, E>> {
        self.0.to_vec()
    }
}
