use crate::field::Field;

use super::{monomial_ordering::Ordering, Exponent, Id, Polynomial, Term};

pub trait TermAccumulator<O, I, C, P>: Default {
    fn push(&mut self, t: Term<O, I, C, P>);
}

impl<O, I, C, P> Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: Field,
    P: Exponent,
{
    /// Test if one polynomial is divisible by another
    pub fn is_divisible_by(&self, divisor: &Self) -> bool {
        let lm = if let Some(term) = divisor.terms.get(0) {
            &term.monomial
        } else {
            return false;
        };

        'terms_loop: for t in self.terms.iter() {
            if t.monomial > *lm {
                // there is no chance lm will divide any other term,
                // stop searching
                break;
            }

            let mut vars = t.monomial.product.iter();
            'lm_vars_loop: for div_var in lm.product.iter() {
                while let Some(var) = vars.next() {
                    if var.id == div_var.id {
                        if var.power >= div_var.power {
                            // At least this variable of the term is divisible by lm,
                            // proceed to next lm variable:
                            continue 'lm_vars_loop;
                        } else {
                            // lm can not divide this term because lm var has higher
                            // power than curremt var, proceed to next term:
                            continue 'terms_loop;
                        }
                    }
                }
                // lm can not divide this term because there are lm vars not in this term,
                // proceed to next term:
                continue 'terms_loop;
            }
            // lm divides this term, so we can stop:
            return true;
        }

        // no term is divisible:
        false
    }

    /// Calculates the quotient and remainder of the division of self by divisor.
    pub fn long_division<Q: TermAccumulator<O, I, C, P>, R: TermAccumulator<O, I, C, P>>(
        mut self,
        divisor: &Self,
    ) -> Option<(Q, R)> {
        let lt = divisor.terms.get(0)?;
        let lt_inv = lt.coefficient.clone().inv();

        let mut quot: Q = Default::default();
        let mut rem: R = Default::default();

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
                    self.terms = Vec::new();
                    Polynomial::sum_terms(iter, difference, &mut self.terms);

                    quot.push(-factor);

                    continue 'outer;
                } else {
                    // Since we could not divide, see if we can stop testing.
                    // If leading monomial is bigger than the term's monomial, all
                    // other terms will also be smaller, so there is no point in
                    // continuing.
                    let can_stop = lt.monomial > t.monomial;

                    rem.push(t);

                    if can_stop {
                        for e in iter {
                            rem.push(e);
                        }
                        break;
                    }
                }
            }

            break;
        }

        Some((quot, rem))
    }

    pub fn div_rem(self, divisor: &Self) -> Option<(Self, Self)> {
        self.long_division::<PolyBuilder<_, _, _, _>, PolyBuilder<_, _, _, _>>(divisor)
            .map(|(quot, div)| (quot.polynomial, div.polynomial))
    }

    // Divide all coefficients by the leading coefficient.
    pub fn normalized_by_coefs(mut self) -> Self {
        let mut iter = self.terms.iter_mut();
        if let Some(lt) = iter.next() {
            let inv_coef = std::mem::replace(&mut lt.coefficient, C::one()).inv();

            for t in iter {
                t.coefficient *= &inv_coef;
            }
        }

        self
    }
}

pub struct PolyBuilder<O, I, C, P> {
    pub polynomial: Polynomial<O, I, C, P>,
}

impl<O, I, C, P> Default for PolyBuilder<O, I, C, P> {
    fn default() -> Self {
        Self {
            polynomial: Polynomial { terms: Vec::new() },
        }
    }
}

impl<O, I, C, P> TermAccumulator<O, I, C, P> for PolyBuilder<O, I, C, P> {
    fn push(&mut self, t: Term<O, I, C, P>) {
        self.polynomial.terms.push(t);
    }
}

#[derive(Default)]
struct Discarder {}

impl<O, I, C, P> TermAccumulator<O, I, C, P> for Discarder {
    fn push(&mut self, _: Term<O, I, C, P>) {}
}

impl<'a, O, I, C, P> std::ops::Div<&'a Self> for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: Field,
    P: Exponent,
{
    type Output = Self;

    fn div(self, rhs: &Self) -> Self {
        self.long_division::<PolyBuilder<O, I, C, P>, Discarder>(rhs)
            .unwrap()
            .0
            .polynomial
    }
}

impl<'a, O, I, C, P> std::ops::Rem<&'a Self> for Polynomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: Field,
    P: Exponent,
{
    type Output = Self;

    fn rem(self, rhs: &Self) -> Self {
        self.long_division::<Discarder, PolyBuilder<O, I, C, P>>(rhs)
            .unwrap()
            .1
            .polynomial
    }
}

#[cfg(test)]
pub mod tests {

    use super::*;
    use crate::{field::CommutativeRing, polynomial::Polynomial};
    use num_rational::Rational32;
    use num_traits::{One, Pow};

    impl CommutativeRing for Rational32 {}
    impl Field for Rational32 {}
    pub type QPoly = Polynomial<crate::polynomial::monomial_ordering::Lex, u8, Rational32, i16>;

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
