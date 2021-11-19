use crate::{
    ordered_sum,
    polynomial::{Coefficient, Id, Polynomial, Power, Term},
};
use std::collections::{BinaryHeap, VecDeque};

trait InvertibleCoefficient: Coefficient + num_traits::ops::inv::Inv<Output = Self> {}

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
fn reduce<I, C, P>(p: &mut Polynomial<I, C, P>, g: Vec<Polynomial<I, C, P>>) -> bool
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let mut was_reduced = false;
    let ret = 'outer: loop {
        // Find the last element in the g whose ini(g) <= ini(p):
        let pos = {
            let p_ini = if let Some(t) = p.terms.get(0) {
                &t.monomial
            } else {
                // p is zero, so it can't be reduced
                break p;
            };

            g.binary_search_by(|gp| gp.terms[0].monomial.cmp(p_ini))
        };

        let pos = match pos {
            Err(0) => {
                // ini(p) is smaller than all ini(g), so can't be reduced
                break p;
            }
            Err(n) => n - 1,
            Ok(n) => n,
        };

        // Try to reduce using every polynomial in g in decreasing order:
        for gp in g[..=pos].iter().rev() {
            if reduction_step(p, gp) {
                was_reduced = true;
                continue 'outer;
            }
        }

        // Could not reduced with any polynomial in g, so stop:
        break p;
    };

    was_reduced
}

/// outer doesn't need to be sorted, inner does.
fn autoreduce_step<I, C, P>(mut outer: Vec<Polynomial<I, C, P>>, inner: Vec<Polynomial<I, C, P>>)
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    // TODO: to be continued...
    //let new_inner: BinaryHeap<_> = outer.drain_filter(|p| reduce(p, inner)).collect();
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
