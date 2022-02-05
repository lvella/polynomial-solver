use std::collections::HashSet;

use rug::Complete;

use crate::{
    big_unsigned::BigUnsigned,
    finite_field,
    polynomial::{self, Polynomial},
};

/// Simple tests that may tell if a single polynomial is solvable or not.
/// Returns Some(true) if solvable, Some(false) if not, None if unknown.
pub fn simple_solvability_tests<
    O: polynomial::monomial_ordering::Ordering,
    I: polynomial::Id,
    C: polynomial::Coefficient,
    P: polynomial::Power,
>(
    poly: Polynomial<O, I, C, P>,
) -> Option<bool> {
    let terms = poly.get_terms();

    // Get term that might be constant:
    let last_term = match terms.last() {
        None => {
            // If terms are empty, polynomial is zero, which is trivially solvable:
            return Some(true);
        }
        Some(term) => term,
    };

    // Test if polynomial has constant:
    if !last_term.get_monomial().get_total_power().is_zero() {
        // Polynomial has no constants, so it has a trivial zero:
        return Some(true);
    }

    // Test if polynomial has any terms other than the non-zero constant:
    if terms.len() == 1 {
        // Polynomial is a non-zero constant, thus it is trivially unsolvable:
        return Some(false);
    }

    // Find if the polynomial is linear
    for term in terms {
        if *term.get_monomial().get_total_power() > P::one() {
            // Polynomial is non-linear, we are not sure if it is solvable
            return None;
        }
    }

    // Polynomial is linear, so it is obviously solvable:
    Some(true)
}

/// Schmidt test, from https://doi.org/10.1016/0022-314X(74)90043-2
/// "A lower bound for the number of solutions of equations over finite fields."
/// by Wolfgang M. Schmidt, 1974
///
/// If the order of the finite field is big enough compared to the number of
/// variables and the polynomial degree, there is a lower bound on the number
/// of solutions that lies on F^n. If this lower bound is > 0, we can declare
/// the polynomial as solvable.
///
/// Returns true if the polynomial has solutions, false if it is unknown.
///
/// TODO: this function can probably be improved by using the results in
/// https://doi.org/10.1016/j.ffa.2005.03.003
/// "Improved explicit estimates on the number of solutions of equations over a finite field"
/// by Antonio Cafurea and Guillermo Matera, 2006
pub fn schimidt_lower_bound<
    O: polynomial::monomial_ordering::Ordering,
    I: polynomial::Id + std::hash::Hash,
    C: polynomial::Coefficient + finite_field::FiniteField,
    P: polynomial::Power + Into<f64>,
>(
    poly: Polynomial<O, I, C, P>,
) -> bool {
    // Get size of finite field:
    let q = C::get_order();

    // Count the number of variables and find polynomial degree:
    let (n, d) = {
        let mut var_set = HashSet::new();

        let zero = P::zero();
        let mut degree = &zero;

        for term in poly.get_terms() {
            let mon = term.get_monomial();
            if mon.get_total_power() > degree {
                degree = mon.get_total_power();
            }

            for var in mon.get_product() {
                var_set.insert(var.get_id().clone());
            }
        }

        (var_set.len(), degree.clone())
    };

    // Convert degree to float so we can log
    let d: f64 = d.into();
    assert!(
        d < 9007199254740992.0f64,
        "degree is to big to be exactly represented in 64-bit float"
    );

    let p_idx = (4.0 * d.ln()).trunc() as usize;
    // Given the limit of 9007199254740992, p_idx can be at most 146

    // 2 plus the first 146 primes:
    const primes: [u16; 147] = [
        2, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
        89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
        181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277,
        281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389,
        397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499,
        503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617,
        619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739,
        743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839,
    ];

    let n = rug::Integer::from(n);
    let d = rug::Integer::from(d as u64);
    let P = primes[p_idx] as u32;

    let mut condition = rug::Integer::from(10000u32);

    condition *= &n;
    condition *= &n;
    condition *= &n;

    condition *= &d;
    condition *= &d;
    condition *= &d;
    condition *= &d;
    condition *= &d;

    condition *= rug::Integer::from(P * P * P);

    if q <= condition {
        return false;
    }

    // The number of solutions is greater than q^(n - 1) - (d - 1)*(d - 2)*q^(n - 1.5) - 6*d^2*q^(n - 2)
    // If this lower bound is >= 0, then we have at least one solution. To check if >= 0, we can divide by
    // q^(n - 2), and check if the positive term is greater than the sum of the negative terms.
    q >= (&d - 1u8).complete() * (&d - 2u8).complete() * q.sqrt_ref().complete() + d.square() * 6u8
}
