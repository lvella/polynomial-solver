use crate::{
    ordered_sum,
    polynomial::{Coefficient, Id, Monomial, Polynomial, Power, Term},
};
use num_traits::Zero;
use std::collections::{BinaryHeap, VecDeque};

trait InvertibleCoefficient: Coefficient + num_traits::ops::inv::Inv<Output = Self> {}

struct IniSortedPolynomial<I, C, P> {
    /// If p has no terms (is zero), this may panic.
    p: Polynomial<I, C, P>,
}

impl<I, C, P> PartialEq for IniSortedPolynomial<I, C, P>
where
    I: PartialEq,
    P: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.p.terms[0].monomial == other.p.terms[0].monomial
    }
}

impl<I, C, P> Eq for IniSortedPolynomial<I, C, P>
where
    I: Eq,
    P: Eq,
{
}

impl<I, C, P> PartialOrd for IniSortedPolynomial<I, C, P>
where
    I: Ord,
    P: Power,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.p
            .terms
            .get(0)?
            .monomial
            .partial_cmp(&other.p.terms.get(0)?.monomial)
    }
}

impl<I, C, P> Ord for IniSortedPolynomial<I, C, P>
where
    I: Ord,
    P: Power,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Reduce one polynomial with respect to another.
/// This is kind of a multi-variable division, and the return is the remainder.
fn reduction_step<I, C, P>(p: &mut Polynomial<I, C, P>, reference: &Polynomial<I, C, P>) -> bool
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let ini_p = p.terms.get(0);

    let mut ref_iter = reference.terms.iter();
    let ini_ref = ref_iter.next();

    if let (Some(ini_p), Some(ini_ref)) = (ini_p, ini_ref) {
        // Find the quotient between the monomial ini(p) and ini(ref),
        // so that p - c*quot*ref eliminates the first term in p:
        let quot = match ini_p.monomial.clone().whole_division(&ini_ref.monomial) {
            Some(quot) => quot,
            None => {
                return false;
            }
        };

        let mut p_iter = std::mem::take(&mut p.terms).into_iter();
        let ini_p = p_iter.next().unwrap();

        // Calculate elimination factor, so that p + factor*ref eliminates the first term in p:
        let mut coefficient = C::zero();
        coefficient -= ini_p.coefficient * ini_ref.coefficient.clone().inv();
        let factor = Term {
            coefficient,
            monomial: quot,
        };

        // Apply the coefficient to all the remaining terms of reference
        let difference: Vec<_> = ref_iter.map(|t| factor.clone() * t.clone()).collect();

        // Sum the remaining terms into a new polinomial:
        p.terms = ordered_sum::ordered_sum(p_iter, difference.into_iter());
        true
    } else {
        false
    }
}

/// g must be sorted in increasing order;
/// all polynomials in g must be != 0
fn reduce<I, C, P>(p: &mut Polynomial<I, C, P>, g: &Vec<IniSortedPolynomial<I, C, P>>) -> bool
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let mut was_reduced = false;
    'outer: loop {
        // Find the last element in the g whose ini(g) <= ini(p):
        let pos = {
            let p_ini = if let Some(t) = p.terms.get(0) {
                &t.monomial
            } else {
                // p is zero, so it can't be reduced
                break;
            };

            g.binary_search_by(|gp| gp.p.terms[0].monomial.cmp(p_ini))
        };

        let pos = match pos {
            Err(0) => {
                // ini(p) is smaller than all ini(g), so can't be reduced
                break;
            }
            Err(n) => n - 1,
            Ok(n) => n,
        };

        // Try to reduce using every polynomial in g in decreasing order:
        for gp in g[..=pos].iter().rev() {
            if reduction_step(p, &gp.p) {
                was_reduced = true;
                continue 'outer;
            }
        }

        // Could not reduced with any polynomial in g, so stop:
        break;
    }

    was_reduced
}

fn autoreduce_step<I, C, P>(
    mut outer: Vec<Polynomial<I, C, P>>,
    mut inner: Vec<IniSortedPolynomial<I, C, P>>,
) -> (Vec<Polynomial<I, C, P>>, Vec<IniSortedPolynomial<I, C, P>>)
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    // here is a better version of this algorithm where the inner side is reduced before
    // the outer side, so there is less outer by inner reductions.
    // TODO: Implement it.

    // Reduce every outer relative to everey inner:
    let mut next_inner: BinaryHeap<_> = outer
        .drain_filter(|p| reduce(p, &inner))
        .map(|p| IniSortedPolynomial { p })
        .collect();

    // Reduce every inner relative to smaller inners.
    // If reduced to zero, it is discarded,
    // if reduced to non-zero it goes to next_inner,
    // if not reduced, it goes to outer:
    while let Some(IniSortedPolynomial { mut p }) = inner.pop() {
        if reduce(&mut p, &inner) {
            if !p.is_zero() {
                next_inner.push(IniSortedPolynomial { p });
            }
        } else {
            outer.push(p);
        }
    }

    (outer, next_inner.into_sorted_vec())
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;

    use super::*;

    impl Coefficient for f32 {}
    impl InvertibleCoefficient for f32 {}
    type FloatPoly = Polynomial<u8, f32, u32>;

    #[test]
    fn reduction_step_test() {
        // Can't use SmallPoly because i32 is not invertible
        let [x, y]: [FloatPoly; 2] = FloatPoly::new_variables([1u8, 0u8]).try_into().unwrap();

        let p = &(x.clone().pow(5u8) * y.clone().pow(3u8)) * 4.0;

        let r = &x.clone().pow(3u8) * 2.0 - y.clone() * x.clone() + &y.clone() * 2.0 - 3.0;

        let mut reduced = p.clone();
        reduction_step(&mut reduced, &r);
        println!("{}", reduced);

        let reconstructed_p = reduced + &(x.pow(2u8) * y.pow(3u8)) * 2.0 * r;

        assert_eq!(reconstructed_p, p);
    }
}
