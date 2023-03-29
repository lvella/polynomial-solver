use std::{marker::PhantomData, rc::Rc};

use crate::{
    kd_tree::{self, DataOperations, Entry, KDTree, SearchPath},
    polynomial::{
        divmask::DivMaskTestResult,
        monomial_ordering::Ordering,
        signature_basis::{get_var_exp_from_monomial, DivMap, MaskedMonomialRef},
        Id, VariablePower,
    },
};

use super::{make_dense_monomial, MaskedMonomial, SignedExponent};

impl<O: Ordering, I: Id, E: SignedExponent> kd_tree::Entry for MaskedMonomial<O, I, E> {
    type KeyElem = VariablePower<I, E>;
    type PartitionFilter = PartitionFilter<O, I, E>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
        let id = I::from_idx(dim);
        let power = get_var_exp_from_monomial(&self.monomial, &id);
        VariablePower { id, power }
    }

    fn average_filter(&self, other: &Self, dim: usize) -> Self::PartitionFilter {
        let id = I::from_idx(dim);

        let exp_a = get_var_exp_from_monomial(&self.monomial, &id);
        let exp_b = get_var_exp_from_monomial(&other.monomial, &id);
        let avg = (exp_a + exp_b + E::one()) / E::from(2);
        PartitionFilter(VariablePower { id, power: avg }, PhantomData {})
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

/// The partition filter is just a wrapper around VariablePower, plus a
/// PhantomData to contain the extra needed generic arguments.
pub(in crate::polynomial::signature_basis) struct PartitionFilter<
    O: Ordering,
    I: Id,
    E: SignedExponent,
>(VariablePower<I, E>, PhantomData<O>);

impl<O: Ordering, I: Id, E: SignedExponent> kd_tree::PartitionFilter for PartitionFilter<O, I, E> {
    type Entry = MaskedMonomial<O, I, E>;

    fn is_less(&self, e: &Self::Entry) -> bool {
        e.cmp_dim(&self.0) == std::cmp::Ordering::Less
    }

    fn into_key(self) -> Option<<Self::Entry as kd_tree::Entry>::KeyElem> {
        Some(self.0)
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

    /// Calculate the GCD among all given entries.
    fn make(&self, entries: &[Self::Entry]) -> Self::NodeData {
        MaskedMonomial::gcd_all(entries.iter().map(|e| &e.monomial), &self.div_map).unwrap()
    }

    /// Update a node_data with the GCD of itself and the new entry.
    fn update(&self, node_data: &mut Self::NodeData, new_entry: &Self::Entry) {
        node_data.gcd_update(&new_entry.monomial, &self.div_map);
    }
}

/// A collection of signatures with search for a divisor accelerated with
/// KD-tree. Useful for implementing signature criterion.
pub struct MonomialIndex<O: Ordering, I: Id, E: SignedExponent>(
    kd_tree::KDTree<Operations<O, I, E>>,
);

impl<O: Ordering, I: Id, E: SignedExponent> MonomialIndex<O, I, E> {
    /// Creates a new tree index from known elements.
    pub(in crate::polynomial::signature_basis) fn new(
        num_variables: usize,
        div_map: Rc<DivMap<E>>,
        elems: Vec<MaskedMonomial<O, I, E>>,
    ) -> Self {
        Self(KDTree::new(
            num_variables,
            elems,
            Operations {
                div_map: div_map.clone(),
                _phantom: PhantomData {},
            },
        ))
    }

    pub(in crate::polynomial::signature_basis) fn insert(&mut self, elem: MaskedMonomial<O, I, E>) {
        self.0.insert(elem)
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

    pub(in crate::polynomial::signature_basis) fn to_vec(self) -> Vec<MaskedMonomial<O, I, E>> {
        self.0.to_vec()
    }
}
