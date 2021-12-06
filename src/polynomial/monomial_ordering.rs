use super::Monomial;
use std::cmp::Ordering as CmpOrd;

pub trait Ordering: core::fmt::Debug {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Ord,
        P: Ord;
}

/// Lexicographical ordering.
#[derive(Debug)]
pub struct Lex;

impl Ordering for Lex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Ord,
        P: Ord,
    {
        for (a, b) in a.product.iter().zip(b.product.iter()) {
            let id_cmp = a.id.cmp(&b.id);
            if id_cmp != CmpOrd::Equal {
                return id_cmp;
            }

            let power_cmp = a.power.cmp(&b.power);
            if power_cmp != CmpOrd::Equal {
                return power_cmp;
            }
        }

        // If all the leading powers are equal, the one with most powers is bigger
        a.product.len().cmp(&b.product.len())
    }
}

/// Graded reverse lexicographical ordering.

#[derive(Debug)]
pub struct Grevlex;

impl Ordering for Grevlex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Ord,
        P: Ord,
    {
        match a.total_power.cmp(&b.total_power) {
            CmpOrd::Equal => (),
            cmp => {
                return cmp;
            }
        }

        for (a, b) in a.product.iter().zip(b.product.iter()).rev() {
            let id_cmp = b.id.cmp(&a.id);
            if id_cmp != CmpOrd::Equal {
                return id_cmp;
            }

            let power_cmp = b.power.cmp(&a.power);
            if power_cmp != CmpOrd::Equal {
                return power_cmp;
            }
        }

        // If all the leading powers are equal, the one with most powers is lower
        b.product.len().cmp(&a.product.len())
    }
}
