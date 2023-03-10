//! Indices used to accelerate searches in the signature basis algorithm.

use crate::polynomial::{divmask::DivMaskTestResult, monomial_ordering::Ordering, Id, Monomial};

use super::{DivMap, DivMask, MaskedMonomialRef, SignedExponent};

pub(crate) mod monomial_index;
pub(crate) mod ratio_monomial_index;

/// Wraps together a divmask and a corresponding monomial, allowing for
/// accelerated divisibility test.
#[derive(Debug, Clone)]
pub(super) struct MaskedMonomial<O: Ordering, I: Id, E: SignedExponent> {
    pub divmask: DivMask,
    pub monomial: Monomial<O, I, E>,
}

impl<O: Ordering, I: Id, E: SignedExponent> MaskedMonomial<O, I, E> {
    pub(super) fn divides<'a>(&self, other: &MaskedMonomialRef<'a, O, I, E>) -> bool {
        match self.divmask.divides(other.0) {
            DivMaskTestResult::NotDivisible => false,
            DivMaskTestResult::Unsure => self.monomial.divides(other.1),
        }
    }
}

/// Maps a tree entry to its NodeData.
fn node_data_builder<O: Ordering, I: Id, E: SignedExponent>(
    div_map: &DivMap<E>,
    a: MaskedMonomial<O, I, E>,
    b: &MaskedMonomial<O, I, E>,
) -> MaskedMonomial<O, I, E> {
    let gcd = a.monomial.gcd(&b.monomial);
    let divmask = div_map.map(&gcd);
    MaskedMonomial {
        divmask,
        monomial: gcd,
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
