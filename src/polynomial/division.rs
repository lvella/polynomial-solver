use std::collections::BinaryHeap;

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

struct OrdByMonomial<O, I, C, P>(Term<O, I, C, P>);

impl<O, I, C, P> PartialEq for OrdByMonomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.monomial == other.0.monomial
    }
}

impl<O, I, C, P> Eq for OrdByMonomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
}

impl<O, I, C, P> PartialOrd for OrdByMonomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.monomial.partial_cmp(&other.0.monomial)
    }
}

impl<O, I, C, P> Ord for OrdByMonomial<O, I, C, P>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.monomial.cmp(&other.0.monomial)
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

        let mut neg_quot_terms = BinaryHeap::new();

        'outer: loop {
            let rem_terms = Vec::with_capacity(self.terms.len());
            let mut iter = self.terms.into_iter();
            self.terms = rem_terms;

            // Search for a term in self to be eliminated by divisor leading term:
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
                    self.terms.extend(Polynomial::sum_terms(iter, difference));

                    neg_quot_terms.push(OrdByMonomial(factor));

                    continue 'outer;
                } else {
                    self.terms.push(t);
                }
            }

            break;
        }

        // Coalesce the quotient.
        // I am assuming that in a multivariate division, it may be that the quotient
        // terms do not end up neatly ordered and unique by monomial, so I must manually
        // sum the terms of same monomial and insert them in descending order.
        let mut neg_quot = Polynomial {
            terms: Vec::with_capacity(neg_quot_terms.len()),
        };

        if let Some(OrdByMonomial(mut prev)) = neg_quot_terms.pop() {
            while let Some(OrdByMonomial(next)) = neg_quot_terms.pop() {
                if next.monomial == prev.monomial {
                    prev.coefficient += next.coefficient;
                } else {
                    if !prev.coefficient.is_zero() {
                        neg_quot.terms.push(prev);
                    }
                    prev = next;
                }
            }

            if !prev.coefficient.is_zero() {
                neg_quot.terms.push(prev);
            }
        }

        Some((-neg_quot, self))
    }
}
