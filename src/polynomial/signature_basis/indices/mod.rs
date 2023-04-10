//! Indices used to accelerate searches in the signature basis algorithm.

use replace_with::replace_with_or_abort;
use std::ops::Deref;

use crate::polynomial::{monomial_ordering::Ordering, Id, Monomial};

use super::{DivMap, Masked, SignedExponent};

pub(crate) mod monomial_index;
pub(crate) mod ratio_monomial_index;

impl<'a, O: Ordering + 'a, I: Id + 'a, E: SignedExponent + 'a> Masked<Monomial<O, I, E>> {
    /// Creates masked monomial from GCD of all given monomials.
    ///
    /// Returns None if input iter is empty.
    pub(super) fn gcd_all(
        mut iter: impl Iterator<Item = impl Deref<Target = Monomial<O, I, E>>>,
        div_map: &DivMap<E>,
    ) -> Option<Self> {
        let start = iter.next()?.clone();

        let monomial = iter.fold(start, |a, b| a.gcd(&b));

        Some(Masked {
            divmask: div_map.map(&monomial),
            value: monomial,
        })
    }

    /// Updates itself with the GCD of self and the given monomial.
    pub(super) fn gcd_update(&mut self, other: &Monomial<O, I, E>, div_map: &DivMap<E>) {
        replace_with_or_abort(&mut self.value, |old_value| old_value.gcd(other));
        self.divmask = div_map.map(&self.value);
    }
}

/// Makes a dense vector with the exponents of a monomial, up to the largest
/// variable id.
fn make_dense_monomial<O: Ordering, I: Id, E: SignedExponent>(
    monomial: &Monomial<O, I, E>,
) -> Vec<E> {
    let largest_id = monomial.product.get(0).map_or(0, |var| var.id.to_idx());
    let mut dense_monomial = Vec::new();
    dense_monomial.resize(largest_id + 1, E::zero());
    for var in monomial.product.iter() {
        dense_monomial[var.id.to_idx()] = var.power.clone();
    }

    dense_monomial
}
