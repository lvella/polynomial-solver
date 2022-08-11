use itertools::{EitherOrBoth, Itertools};

use super::{Exponent, Id, Monomial, PolyTypes};
use std::cmp::Ordering as CmpOrd;

pub trait Ordering: core::fmt::Debug + Clone + Eq + Ord {
    fn ord<P: PolyTypes>(a: &Monomial<P>, b: &Monomial<P>) -> CmpOrd;
}

/// Compare two variables' power as if they where in the same position in the
/// ordered monomial list, where zeros are omitted.
fn power_cmp<P: Exponent>(id_cmp: CmpOrd, a: &P, b: &P) -> CmpOrd {
    match id_cmp {
        CmpOrd::Equal => a.cmp(b),
        // To accommodate for the possibility of exponent being negative, which
        // is used in signature Gröbner Basis, we must assume the same variable
        // on the other monomial is zero, so we invert the result depending
        // wether the power of the most significant variable is negative.
        CmpOrd::Less => P::zero().cmp(b),
        CmpOrd::Greater => a.cmp(&P::zero()),
    }
}

/// Lexicographical ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lex;

impl Ordering for Lex {
    fn ord<P: PolyTypes>(a: &Monomial<P>, b: &Monomial<P>) -> CmpOrd {
        for pair in a.product.iter().zip_longest(b.product.iter()) {
            match pair {
                EitherOrBoth::Both(a, b) => {
                    let var_cmp = power_cmp(a.id.cmp(&b.id), &a.power, &b.power);
                    if var_cmp != CmpOrd::Equal {
                        return var_cmp;
                    }
                }
                EitherOrBoth::Left(a) => return a.power.cmp(&P::zero()),
                EitherOrBoth::Right(b) => return P::zero().cmp(&b.power),
            }
        }

        CmpOrd::Equal
    }
}

/// Graded reverse lexicographical ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Grevlex;

impl Ordering for Grevlex {
    fn ord<P: PolyTypes>(a: &Monomial<P>, b: &Monomial<P>) -> CmpOrd {
        match a.total_power.cmp(&b.total_power) {
            CmpOrd::Equal => (),
            cmp => {
                return cmp;
            }
        }

        for (a, b) in a.product.iter().rev().zip(b.product.iter().rev()) {
            let var_cmp = power_cmp(a.id.cmp(&b.id), &b.power, &a.power);
            if var_cmp != CmpOrd::Equal {
                return var_cmp;
            }
        }

        // It can only get here if all tested variables and powers matches, and
        // both must have the same number of variables because the total power
        // also matches, so they must be equal.
        CmpOrd::Equal
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;
    use rand::prelude::SliceRandom;

    use crate::polynomial::PolyTypesImpl;

    use super::*;

    pub type LexPoly = PolyTypesImpl<Lex, u8, i32, u16>;
    pub type GrevlexPoly = PolyTypesImpl<Grevlex, u8, i32, u16>;

    #[test]
    fn test_lex_ordering() {
        let [z, y, x]: [LexPoly; 3] = LexPoly::new_variables([0u8, 1u8, 2u8]).try_into().unwrap();

        let ordered = [
            x.clone().pow(3u8),
            y.clone() * x.clone().pow(2u8),
            z.clone() * x.clone().pow(2u8),
            z.clone() * y.clone() * x.clone(),
            y.clone().pow(3u8),
            z.clone() * y.clone().pow(2u8),
            z.clone().pow(2u8) * y.clone(),
            z.clone().pow(3u8),
            LexPoly::new_constant(1),
        ];

        let mut sorted = ordered.clone();
        sorted.shuffle(&mut rand::thread_rng());

        sorted.sort();

        assert_eq!(sorted.len(), ordered.len());
        for (orig_t, sort_t) in ordered.into_iter().zip(sorted.into_iter().rev()) {
            assert_eq!(orig_t, sort_t);
        }
    }

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
