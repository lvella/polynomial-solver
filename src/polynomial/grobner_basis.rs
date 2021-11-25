use crate::{
    ordered_ops,
    polynomial::{Coefficient, Id, Polynomial, Power, Term},
};

use itertools::Itertools;
use num_traits::Zero;
use std::{
    borrow::{Borrow, BorrowMut},
    collections::{BTreeSet, BinaryHeap, VecDeque},
    iter::Once,
    rc::Rc,
};

use super::Monomial;

trait InvertibleCoefficient
where
    Self: Coefficient + Ord + num_traits::ops::inv::Inv<Output = Self>,
    for<'a> &'a Self: std::ops::Mul<Output = Self>,
{
    /// Calculate elimination factor, so that self + factor*rhs = 0:
    fn elimination_factor(&self, rhs: &Self) -> Self {
        let mut factor = Self::zero();
        factor -= self * &rhs.clone().inv();
        factor
    }
}

/// Reduce one polynomial with respect to another.
/// This is kind of a multi-variable division, and the return is the remainder.
fn reduction_step<I, C, P>(p: &mut Polynomial<I, C, P>, reference: &Polynomial<I, C, P>) -> bool
where
    I: Id,
    C: InvertibleCoefficient,
    for<'a> &'a C: std::ops::Mul<Output = C>,
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
        let factor = Term {
            coefficient: ini_p.coefficient.elimination_factor(&ini_ref.coefficient),
            monomial: quot,
        };

        // Apply the coefficient to all the remaining terms of reference
        let difference: Vec<_> = ref_iter.map(|t| factor.clone() * t.clone()).collect();

        // Sum the remaining terms into a new polinomial:
        p.terms = Polynomial::sum_terms(p_iter, difference.into_iter());
        true
    } else {
        false
    }
}

/// all polynomials in g must be != 0
fn reduce<I, C, P>(
    p: &mut Polynomial<I, C, P>,
    g: &BTreeSet<Rc<Polynomial<I, C, P>>>,
    is_p_gt_g: bool,
) -> bool
where
    I: Id,
    C: InvertibleCoefficient,
    for<'a> &'a C: std::ops::Mul<Output = C>,
    P: Power,
{
    let mut was_reduced = false;

    'outer: loop {
        // Try to reduce using every polynomial <= p in g, in decreasing order:
        for gp in g.range::<Polynomial<I, C, P>, _>(..=&*p).rev() {
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

/// g must be the sole owner of the polynomials, otherwise this will panic
fn autoreduce<I, C, P>(
    mut g: BTreeSet<Rc<Polynomial<I, C, P>>>,
) -> BTreeSet<Rc<Polynomial<I, C, P>>>
where
    I: Id,
    C: InvertibleCoefficient,
    for<'a> &'a C: std::ops::Mul<Output = C>,
    P: Power,
{
    loop {
        let mut next_g = BTreeSet::new();
        let mut modified = false;
        while let Some(mut p) = g.pop_last() {
            if reduce(Rc::get_mut(&mut p).unwrap(), &g, true) {
                if p.is_zero() {
                    continue;
                }
                modified = true;
            }
            next_g.insert(p);
        }

        if !modified {
            return next_g;
        }
        g = next_g;
    }
}

fn spar_reduce<I, C, P>(
    p: &Polynomial<I, C, P>,
    q: &Polynomial<I, C, P>,
    current_set: &BTreeSet<Rc<Polynomial<I, C, P>>>,
) -> Option<Polynomial<I, C, P>>
where
    I: Id,
    C: InvertibleCoefficient,
    for<'a> &'a C: std::ops::Mul<Output = C>,
    P: Power,
{
    let ini_q = q.terms.get(0)?;
    let ini_p = p.terms.get(0)?;

    let sat_diff = |a: &Term<I, C, P>, b: &Term<I, C, P>| {
        let product = ordered_ops::saturating_sub(
            a.monomial.product.iter().cloned(),
            b.monomial.product.iter(),
            |x, y| y.id.cmp(&x.id),
            |mut x, y| {
                x.power = x.power.saturating_sub(&y.power);
                if x.power.is_zero() {
                    None
                } else {
                    Some(x)
                }
            },
        );

        let total_power = product.iter().fold(P::zero(), |mut acc, v| {
            acc += &v.power;
            acc
        });

        let monomial = Monomial {
            product,
            total_power,
        };

        monomial
    };

    let p_complement = sat_diff(ini_q, ini_p);
    let q_complement = sat_diff(ini_p, ini_q);

    // TODO: to be continued...
    // calculate the coefficient using the lcm(p.coef, q.coef)

    // q_complement must be negative, so the sum would eliminate the first term:
    q_complement.coefficient = {
        let mut neg = C::zero();
        neg -= q_complement.coefficient;
        neg
    };

    let spar = Polynomial::sum_terms(
        p.terms[1..]
            .iter()
            .cloned()
            .map(|x| x * p_complement.clone()),
        q.terms[1..]
            .iter()
            .cloned()
            .map(|x| x * q_complement.clone()),
    );

    // TODO: reduce spar and test if null

    None
}

fn grobner_basis<I, C, P>(
    input: impl Iterator<Item = Polynomial<I, C, P>>,
) -> BTreeSet<Rc<Polynomial<I, C, P>>>
where
    I: Id,
    C: InvertibleCoefficient,
    for<'a, 'b> &'a C: std::ops::Mul<&'b C, Output = C>,
    P: Power,
{
    let mut current_set = autoreduce(input.map(|p| Rc::new(p)).collect());
    let mut current_vec: Vec<_> = current_set.iter().rev().cloned().collect();

    let mut work_queue: VecDeque<Box<dyn Iterator<Item = (usize, usize)>>> = VecDeque::new();
    work_queue.push_back(Box::new((0..current_vec.len()).tuple_combinations()));

    while let Some(work) = work_queue.pop_front() {
        for (i, j) in work {
            if let Some(new_p) = spar_reduce(&current_vec[i], &current_vec[j], &current_set) {
                let curr_len = current_vec.len();
                work_queue.push_back(Box::new(
                    std::iter::once(curr_len).cartesian_product(0..curr_len),
                ));

                let new_p = Rc::new(new_p);
                current_vec.push(new_p.clone());
                current_set.insert(new_p);
            }
        }
    }
    drop(work_queue);

    autoreduce(current_set)
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
