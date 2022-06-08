use itertools::{EitherOrBoth, Itertools};

use super::{Id, Monomial, Power, VariablePower};
use std::cmp::Ordering as CmpOrd;

pub trait Ordering: core::fmt::Debug + Clone + Eq + Ord {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Power;
}

/// Compare two variables' power as if they where in the same position in the
/// ordered monomial list, where zeros are omitted.
fn power_cmp<I: Id, P: Power>(
    id_cmp: CmpOrd,
    a: &VariablePower<I, P>,
    b: &VariablePower<I, P>,
) -> CmpOrd {
    match id_cmp {
        CmpOrd::Equal => a.power.cmp(&b.power),
        // To accommodate for the possibility of exponent being negative, which
        // is used in signature Gröbner Basis, we must assume the same variable
        // on the other monomial is zero, so we invert the result depending
        // wether the power of the most significant variable is negative.
        CmpOrd::Less => P::zero().cmp(&b.power),
        CmpOrd::Greater => a.power.cmp(&P::zero()),
    }
}

/// Lexicographical ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lex;

impl Ordering for Lex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Power,
    {
        for pair in a.product.iter().zip_longest(b.product.iter()) {
            match pair {
                EitherOrBoth::Both(a, b) => {
                    let var_cmp = power_cmp(a.id.cmp(&b.id), a, b);
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

        for pair in a.product.iter().zip_longest(b.product.iter()) {
            match pair {
                EitherOrBoth::Both(a, b) => {
                    let var_cmp = power_cmp(b.id.cmp(&a.id), a, b);
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
