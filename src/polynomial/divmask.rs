//! Divmasks allows for quick probabilistic test if one monomial divides
//! another. False positives are possible (i.e. a monomial may not be divisible
//! even if the divmask test pass), but negatives are always correct.
//!
//! In some exceptionally rare cases, divmask can prove a positive, but it is so
//! rare that probably it is not worth to handle it. TODO: test if it make a
//! difference to handle definitely positive cases.

use bitvec::macros::internal::funty::Unsigned;
use std::marker::PhantomData;

use super::{Id, Monomial, Power, VariablePower};

/// Divmap is the function used to generate the divmask from a monomial.
/// Divmasks are only compatible if generated from the same divmap. The
/// statistics of a set of monomials are used to generate a mapping that is most
/// useful in finding non-visibility, so the divmap should be regenerated if the
/// statistics changes too much.
#[derive(Debug, Clone)]
pub struct DivMap<T: Unsigned, P: Power> {
    // Vector indexed by variable id. Each entry has a bit index of the first
    // bit for the variable, and a vector with the cutoffs for that variable,
    // each uses one bit starting from the bit index.
    cutoffs: Vec<(u8, Vec<P>)>,
    _basic_type: PhantomData<T>,
}

impl<T: Unsigned, P: Power> DivMap<T, P> {
    pub fn new(tracker: &MaximumExponentsTracker<P>) -> Self {
        // Every variable will have at least this many cutoffs...
        let num_cutoffs = (T::BITS as usize / tracker.len()) as u8;
        // ...but this many variables will have one more:
        let extra_bits = T::BITS as usize % tracker.len();

        let mut first_unused_bit = 0;
        let cutoffs = tracker
            .max_exponents
            .iter()
            .enumerate()
            .map(|(var_idx, exp)| {
                let num_bits = num_cutoffs + if var_idx < extra_bits { 1 } else { 0 };
                let partitions = P::from(num_bits + 1);

                let cutoffs_list = (1..=num_bits)
                    .map(|part| P::from(part) * exp / &partitions)
                    .collect();

                let first_bit = first_unused_bit;
                first_unused_bit += num_bits;

                (first_bit, cutoffs_list)
            })
            .collect();

        DivMap {
            cutoffs,
            _basic_type: PhantomData,
        }
    }

    pub fn map<O, I: super::Id>(&self, monomial: &Monomial<O, I, P>) -> DivMask<T> {
        let mut ret = T::ZERO;
        for var in monomial.product.iter() {
            let (first_bit, cutoff_list) = &self.cutoffs[var.id.to_idx()];
            for (idx, cutoff) in cutoff_list.iter().enumerate() {
                if var.power > *cutoff {
                    ret |= T::ONE << (first_bit + idx as u8);
                }
            }
        }

        DivMask(ret)
    }
}

/// The divmask created by an specific divmap for an specific monomial. Can be
/// used to definitely tell if the monomial for other divmask does not divides
/// this one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DivMask<T: Unsigned>(T);

impl<T: Unsigned> DivMask<T> {
    pub fn divides(&self, other: &DivMask<T>) -> DivMaskTestResult {
        let neg_other = !other.0;
        if self.0 & neg_other != T::ZERO {
            DivMaskTestResult::NotDivisible
        } else if self.0 == T::ZERO && neg_other == T::ZERO {
            // TODO: This is so rare that it is probably not worth checking.
            DivMaskTestResult::Divisible
        } else {
            DivMaskTestResult::Unsure
        }
    }
}

pub enum DivMaskTestResult {
    NotDivisible,
    Unsure,
    Divisible,
}

pub struct MaximumExponentsTracker<P: Power> {
    max_exponents: Vec<P>,
    total: P,
    prev_total: P,
}

/// Tracks the maximum exponent seen for each variable.
///
/// Uses a vector indexed by variable id, so it is assumed that every id up to
/// maximum id is used (i.e. ids are a dense enumeration of all variables).
impl<P: Power> MaximumExponentsTracker<P> {
    pub fn new() -> Self {
        Self {
            max_exponents: Vec::new(),
            total: P::zero(),
            prev_total: P::zero(),
        }
    }

    /// Number of variables seen.
    pub fn len(&self) -> usize {
        self.max_exponents.len()
    }

    pub fn add_var<I: Id>(&mut self, var: &VariablePower<I, P>) {
        let idx = var.id.to_idx();
        if self.len() <= idx {
            self.max_exponents.resize(idx + 1, P::zero());
        } else if self.max_exponents[idx] >= var.power {
            return;
        }
        let mut delta = var.power.clone();
        delta -= &self.max_exponents[idx];
        self.total += delta;

        self.max_exponents[idx] = var.power.clone();
    }

    pub fn has_grown_beyond_percentage(&self, percentage: u8) -> bool {
        if self.prev_total.is_zero() {
            return !self.total.is_zero();
        }

        let mut delta = self.total.clone();
        delta -= &self.prev_total;
        let growth = delta * P::from(100) / &self.total;

        growth > P::from(percentage)
    }

    pub fn reset_tracking(&mut self) {
        self.prev_total = self.total.clone();
    }
}
