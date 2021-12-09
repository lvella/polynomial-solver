use super::{Id, Monomial, Power};
use std::cmp::Ordering as CmpOrd;

pub trait Ordering: core::fmt::Debug {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Power;
}

/// Lexicographical ordering.
#[derive(Debug)]
pub struct Lex;

impl Ordering for Lex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Power,
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
        I: Id,
        P: Power,
    {
        match a.total_power.cmp(&b.total_power) {
            CmpOrd::Equal => (),
            cmp => {
                return cmp;
            }
        }

        for (a, b) in a.product.iter().rev().zip(b.product.iter().rev()) {
            let id_cmp = a.id.cmp(&b.id);
            if id_cmp != CmpOrd::Equal {
                return id_cmp;
            }

            let power_cmp = b.power.cmp(&a.power);
            if power_cmp != CmpOrd::Equal {
                return power_cmp;
            }
        }

        // It can only get here if all variables and powers matches,
        // and both must have the same number of variables because the
        // total power also matches, so they must be equal.
        CmpOrd::Equal
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;
    use rand::prelude::SliceRandom;

    use crate::polynomial::Polynomial;

    use super::*;

    pub type GrevlexPoly = Polynomial<Grevlex, u8, i32, u16>;

    #[test]
    fn test_grevlex_ordering() {
        let [z, y, x]: [GrevlexPoly; 3] = GrevlexPoly::new_variables([0u8, 1u8, 2u8])
            .try_into()
            .unwrap();

        let ordered = [
            x.clone().pow(3u8),
            y.clone() * x.clone().pow(2u8),
            y.clone().pow(3u8),
            z.clone() * x.clone().pow(2u8),
            z.clone() * y.clone() * x.clone(),
            z.clone() * y.clone().pow(2u8),
            z.clone().pow(2u8) * y.clone(),
            z.clone().pow(3u8),
            GrevlexPoly::new_constant(1),
        ];

        let mut sorted = ordered.clone();
        sorted.shuffle(&mut rand::thread_rng());

        sorted.sort();

        assert_eq!(sorted.len(), ordered.len());
        for (orig_t, sort_t) in ordered.into_iter().zip(sorted.into_iter().rev()) {
            assert_eq!(orig_t, sort_t);
        }
    }
}
