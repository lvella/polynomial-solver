use itertools::{EitherOrBoth, Itertools};

use super::{Exponent, Id, Monomial};
use std::{cmp::Ordering as CmpOrd, hash::Hash};

pub trait Ordering: core::fmt::Debug + Clone + Eq + Ord + Hash {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Exponent;

    fn cocoa_name() -> &'static str;
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lex;

impl Ordering for Lex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Exponent,
    {
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

    fn cocoa_name() -> &'static str {
        "lex"
    }
}

/// Graded reverse lexicographical ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Grevlex;

impl Ordering for Grevlex {
    fn ord<I, P>(a: &Monomial<Self, I, P>, b: &Monomial<Self, I, P>) -> CmpOrd
    where
        I: Id,
        P: Exponent,
    {
        match a.total_power.cmp(&b.total_power) {
            CmpOrd::Equal => (),
            cmp => {
                return cmp;
            }
        }

        for pair in a.product.iter().rev().zip_longest(b.product.iter().rev()) {
            match pair {
                EitherOrBoth::Both(a, b) => {
                    let var_cmp = power_cmp(a.id.cmp(&b.id), &b.power, &a.power);
                    if var_cmp != CmpOrd::Equal {
                        return var_cmp;
                    }
                }
                EitherOrBoth::Left(a) => return P::zero().cmp(&a.power),
                EitherOrBoth::Right(b) => return b.power.cmp(&P::zero()),
            }
        }

        CmpOrd::Equal
    }

    fn cocoa_name() -> &'static str {
        "DegRevLex"
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;
    use rand::{prelude::SliceRandom, rngs::StdRng, Rng, SeedableRng};
    use std::{iter::Sum, marker::PhantomData};

    use crate::polynomial::{Polynomial, VariablePower};

    use super::*;

    pub type LexPoly = Polynomial<Lex, u8, i32, u16>;
    pub type GrevlexPoly = Polynomial<Grevlex, u8, i32, u16>;

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

    trait DenseOrdering {
        fn cmp<T: Sum<T> + Ord + Clone, const LEN: usize>(a: &[T; LEN], b: &[T; LEN]) -> CmpOrd;
    }

    impl DenseOrdering for Lex {
        fn cmp<T: Sum<T> + Ord + Clone, const LEN: usize>(a: &[T; LEN], b: &[T; LEN]) -> CmpOrd {
            a.cmp(b)
        }
    }

    impl DenseOrdering for Grevlex {
        fn cmp<T: Sum<T> + Ord + Clone, const LEN: usize>(a: &[T; LEN], b: &[T; LEN]) -> CmpOrd {
            match a
                .iter()
                .cloned()
                .sum::<T>()
                .cmp(&b.iter().cloned().sum::<T>())
            {
                CmpOrd::Equal => {
                    let rev_a: Vec<_> = a.iter().cloned().rev().collect();
                    let rev_b: Vec<_> = b.iter().cloned().rev().collect();
                    rev_b.cmp(&rev_a)
                }
                c => c,
            }
        }
    }

    fn dense_to_sparse<O: Ordering>(dense: &[i16]) -> Monomial<O, u8, i16> {
        let mut total_power = 0i16;
        let product = (0..dense.len() as u8)
            .rev()
            .zip(dense)
            .filter_map(|(id, exp)| {
                if *exp == 0 {
                    None
                } else {
                    total_power += *exp;
                    Some(VariablePower { id, power: *exp })
                }
            })
            .collect();

        Monomial {
            product,
            total_power,
            _phantom_ordering: PhantomData,
        }
    }

    fn impl_test_negative_exponent<O: Ordering + DenseOrdering>() {
        let mut rng = StdRng::seed_from_u64(42);

        // Generate 10000 10-elements vectors, with values ranging to -8 to 8,
        // with 40% of chance of being zero. These are the exponents of the test
        // monomials to be ordered.
        let mut dense_vec = Vec::new();
        let mut sparse_vec = Vec::new();
        while dense_vec.len() < 10000 {
            let mut new_elem = [0i16; 10];
            for e in new_elem.iter_mut() {
                if rng.gen_bool(1.0 - 0.4) {
                    *e = rng.gen_range(1..=8);
                    if rng.gen_bool(0.5) {
                        *e = -*e;
                    }
                }
            }
            sparse_vec.push(dense_to_sparse::<O>(&new_elem[..]));
            dense_vec.push(new_elem);
        }

        sparse_vec.sort_unstable_by(|a, b| <O as Ordering>::ord(a, b));
        dense_vec.sort_unstable_by(|a, b| <O as DenseOrdering>::cmp(a, b));

        assert!(sparse_vec.len() == dense_vec.len());
        for (s, d) in sparse_vec.iter().zip(dense_vec.iter()) {
            assert!(*s == dense_to_sparse::<O>(d));
        }
    }

    #[test]
    fn test_negative_exponent() {
        impl_test_negative_exponent::<Lex>();
        impl_test_negative_exponent::<Grevlex>();
    }
}
