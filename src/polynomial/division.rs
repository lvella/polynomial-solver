use super::{monomial_ordering::Ordering, Coefficient, Id, Polynomial, Power, Term};

pub trait InvertibleCoefficient
where
    Self: Coefficient
        + Ord
        + for<'a> std::ops::Mul<&'a Self, Output = Self>
        + num_traits::ops::inv::Inv<Output = Self>,
{
    /// Calculate elimination factor, so that self - factor*rhs = 0, and rhs_inv = 1/rhs.
    fn elimination_factor(self, rhs_inv: &Self) -> Self {
        let mut factor = Self::zero();
        factor -= self * rhs_inv;
        factor
    }
}

impl<O, I, C, P> Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    /// Calculates the quotient and remainder of the division of self by divisor.
    pub fn div_rem(mut self, divisor: &Self) -> Option<(Self, Self)> {
        let lt = divisor.terms.get(0)?;
        let lt_inv = lt.coefficient.clone().inv();

        let mut neg_quot = Polynomial { terms: Vec::new() };
        let mut rem = Polynomial { terms: Vec::new() };

        'outer: loop {
            // Search for a term in self to be eliminated by divisor leading term:
            let mut iter = self.terms.into_iter();
            while let Some(t) = iter.next() {
                if let Some(monomial) = t.monomial.clone().whole_division(&lt.monomial) {
                    // Term can be eliminated, calculate the eliminating coefficient:
                    let factor = Term {
                        coefficient: t.coefficient.elimination_factor(&lt_inv),
                        monomial,
                    };

                    let difference = divisor.terms[1..]
                        .iter()
                        .map(|t| t.clone() * factor.clone());
                    self.terms = Polynomial::sum_terms(iter, difference);

                    neg_quot.terms.push(factor);

                    continue 'outer;
                } else {
                    rem.terms.push(t);
                }
            }

            break;
        }

        Some((-neg_quot, rem))
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use crate::polynomial::Polynomial;
    use num::Rational32;
    use num_traits::{One, Pow, Zero};

    impl Coefficient for Rational32 {}
    impl InvertibleCoefficient for Rational32 {}
    pub type QPoly = Polynomial<crate::polynomial::monomial_ordering::Lex, u8, Rational32, u32>;

    pub fn r<T>(v: T) -> Rational32
    where
        Rational32: From<T>,
    {
        Rational32::from(v)
    }

    #[test]
    fn simple_multivariate_divisions() {
        let [x, y]: [QPoly; 2] = QPoly::new_variables([1u8, 0u8]).try_into().unwrap();

        let f = x.clone().pow(2u8) + x.clone() * y.clone() + r(1);
        let g = x.clone() * y.clone() - x.clone();

        println!("f: {}\ng: {}", &f, &g);

        let (q, rem) = f.div_rem(&g).unwrap();

        println!("f/g: {}\nf%g: {}\n", &q, &rem);

        assert!(q.is_constant());
        assert!(q.terms[0].coefficient.is_one());

        let expected_rem = x.clone().pow(2u8) + x.clone() + r(1);
        assert_eq!(rem, expected_rem);

        let f = x.clone().pow(3u8) - y.clone().pow(3u8);
        let g = x.clone() - y.clone();

        println!("f: {}\ng: {}", &f, &g);

        let (q, rem) = f.div_rem(&g).unwrap();

        println!("f/g: {}\nf%g: {}\n", &q, &rem);

        let expected_q = x.clone().pow(2u8) + x.clone() * y.clone() + y.clone().pow(2u8);
        assert_eq!(q, expected_q);
        assert!(rem.is_zero());
    }

    #[test]
    fn simple_univariate_divisions() {
        let x = QPoly::new_monomial_term(r(1), 0, 1);

        let f = &x.clone().pow(3u8) * r(2) - &x.clone().pow(2u8) * r(3) + &x.clone() * r(4) + r(5);
        let g = x.clone() + r(2);
        println!("f: {}\ng: {}", &f, &g);

        let (q, rem) = f.div_rem(&g).unwrap();

        println!("f/g: {}\nf%g: {}\n", &q, &rem);

        let expected_q = &x.clone().pow(2u8) * r(2) - &x.clone() * r(7) + r(18);
        assert_eq!(q, expected_q);

        assert!(rem.is_constant());
        assert_eq!(rem.terms[0].coefficient, r(-31));

        let f = &x.clone().pow(4u8) * r(4) + &x.clone().pow(3u8) * r(3) + &x.clone() * r(2) + r(1);
        let g = x.clone().pow(2u8) + x.clone() + r(2);
        println!("f: {}\ng: {}", &f, &g);

        let (q, rem) = f.div_rem(&g).unwrap();

        println!("f/g: {}\nf%g: {}\n", &q, &rem);

        let expected_q = &x.clone().pow(2u8) * r(4) - x.clone() - r(7);
        assert_eq!(q, expected_q);

        let expected_rem = &x.clone() * r(11) + r(15);
        assert_eq!(rem, expected_rem);
    }
}
