use crate::{
    ordered_sum,
    polynomial::{Coefficient, Id, Polynomial, Power, Term},
};

use std::collections::BinaryHeap;

trait InvertibleCoefficient: Coefficient + Ord + num_traits::ops::inv::Inv<Output = Self> {}

/// Merges two sorted iterators into a sorted Vec
fn sorted_merge<Ia, Ib, T>(mut a: Ia, mut b: Ib) -> Vec<T>
where
    Ia: Iterator<Item = T>,
    Ib: Iterator<Item = T>,
    T: Ord,
{
    let mut ret = Vec::new();

    let mut a_item = a.next();
    let mut b_item = b.next();

    loop {
        match (a_item, b_item) {
            (Some(a_val), Some(b_val)) => {
                if a_val < b_val {
                    ret.push(a_val);
                    a_item = a.next();
                    b_item = Some(b_val);
                } else {
                    ret.push(b_val);
                    a_item = Some(a_val);
                    b_item = b.next();
                }
            }
            (Some(a_val), None) => {
                ret.push(a_val);
                ret.extend(a);
                break;
            }
            (None, Some(b_val)) => {
                ret.push(b_val);
                ret.extend(b);
                break;
            }
            _ => break,
        }
    }

    ret
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
fn reduce<I, C, P>(p: &mut Polynomial<I, C, P>, g: &Vec<Polynomial<I, C, P>>) -> bool
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

            g.binary_search_by(|gp| gp.terms[0].monomial.cmp(p_ini))
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
            if reduction_step(p, &gp) {
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
    mut inner: Vec<Polynomial<I, C, P>>,
) -> (Vec<Polynomial<I, C, P>>, Vec<Polynomial<I, C, P>>)
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    // Creates a sequence of reduced sets, where the next set is reduced w.r.t. all previous sets:
    let mut reduced_seq = Vec::new();
    while !inner.is_empty() {
        let mut next_inner = BinaryHeap::new();
        let mut new_outer = BinaryHeap::new();

        // Reduce every inner element relative to the smaller elements.
        // If reduced to zero, it is discarded,
        // if reduced to non-zero, it goes to next_inner, to be reduced again on next iteration,
        // if not reduced, it goes to the reduced set of this iteration:
        while let Some(mut e) = inner.pop() {
            if reduce(&mut e.p, &inner) {
                if !e.p.is_zero() {
                    next_inner.push(e);
                }
            } else {
                new_outer.push(e);
            }
        }

        inner = next_inner.into_sorted_vec();
        if !new_outer.is_empty() {
            reduced_seq.push(new_outer);
        }
    }
    drop(inner);

    // TODO: Some random guy on Discord said it would be better to use a brodal queue here
    // instead of a sorted vector. Maybe try if you have nothing else to do.
    let mut new_outer = if let Some(innermost) = reduced_seq.pop() {
        innermost.into_sorted_vec()
    } else {
        // Inner is empty, there is nothing to do:
        return (outer, Vec::new());
    };

    let mut next_inner = BinaryHeap::new();

    // Coallesce the reduced sequence into the new outer.
    // This is O(N²) on the worst case, which is no worse than the previous step.
    while let Some(curr) = reduced_seq.pop() {
        let mut non_reduced = Vec::new();
        for mut e in curr.into_iter_sorted() {
            if reduce(&mut e.p, &new_outer) {
                if !e.p.is_zero() {
                    next_inner.push(e);
                }
            } else {
                non_reduced.push(e);
            }
        }

        new_outer = sorted_merge(new_outer.into_iter(), non_reduced.into_iter());
    }

    (new_outer, next_inner.into_sorted_vec())
}

fn full_autoreduce<I, C, P>(
    mut outer: Vec<IniSortedPolynomial<I, C, P>>,
    mut inner: Vec<IniSortedPolynomial<I, C, P>>,
) -> Vec<IniSortedPolynomial<I, C, P>>
where
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    while !inner.is_empty() {
        let (new_outer, new_inner) = autoreduce_step(outer, inner);
        outer = new_outer;
        inner = new_inner;
    }

    outer
}

#[cfg(test)]
mod tests {
    use num::Rational32;
    use num_traits::Pow;

    use super::*;

    impl Coefficient for Rational32 {}
    impl InvertibleCoefficient for Rational32 {}
    type FloatPoly = Polynomial<u8, Rational32, u32>;

    #[test]
    fn reduction_step_test() {
        // Can't use SmallPoly because i32 is not invertible
        let [x, y]: [FloatPoly; 2] = FloatPoly::new_variables([1u8, 0u8]).try_into().unwrap();

        let p = &(x.clone().pow(5u8) * y.clone().pow(3u8)) * Rational32::from(4);

        let r = &x.clone().pow(3u8) * Rational32::from(2) - y.clone() * x.clone()
            + &y.clone() * Rational32::from(2)
            - Rational32::from(3);

        let mut reduced = p.clone();
        reduction_step(&mut reduced, &r);
        println!("{}", reduced);

        let reconstructed_p = reduced + &(x.pow(2u8) * y.pow(3u8)) * Rational32::from(2) * r;

        assert_eq!(reconstructed_p, p);
    }
}
