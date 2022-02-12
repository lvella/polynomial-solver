use std::collections::HashSet;

use num_traits::{One, Zero};
use rug::Complete;

use crate::{
    factorization::finite_field_factorize,
    finite_field,
    polynomial::{self, Polynomial},
};

/// Schmidt test, from https://doi.org/10.1016/0022-314X(74)90043-2
/// "A lower bound for the number of solutions of equations over finite fields."
/// by Wolfgang M. Schmidt, 1974
///
/// For an absolutely irreducible polynomial, if the order of the finite field
/// is big enough compared to the number of variables and the polynomial degree,
/// there is a lower bound on the number of solutions that lies on F^n. If this
/// lower bound is > 0, we can declare the polynomial as solvable.
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
    C: finite_field::FiniteField,
    P: polynomial::Power + Into<f64>,
>(
    poly: Polynomial<O, I, C, P>,
    // TODO: maybe receive the number of variables as argument,
    // so we don't have to recount every time
) -> bool {
    // TODO: maybe test if it is absolutely irreducible here?

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

    // Convert degree to float so we can take logarithm
    let d: f64 = d.into();
    assert!(
        d < 9007199254740992.0f64,
        "degree is to big to be exactly represented in 64-bit float"
    );

    let p_idx = (4.0 * d.ln()).trunc() as usize;
    // Given the limit of 9007199254740992, p_idx can be at most 146

    // 2 followed by the first 146 primes:
    const PRIMES: [u16; 147] = [
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
    let p = PRIMES[p_idx] as u32;

    let mut condition = rug::Integer::from(10000u32);

    condition *= &n;
    condition *= &n;
    condition *= &n;

    condition *= &d;
    condition *= &d;
    condition *= &d;
    condition *= &d;
    condition *= &d;

    condition *= rug::Integer::from(p * p * p);

    if q <= condition {
        return false;
    }

    // The number of solutions is greater than q^(n - 1) - (d - 1)*(d - 2)*q^(n - 1.5) - 6*d^2*q^(n - 2)
    // If this lower bound is >= 0, then we have at least one solution. To check if >= 0, we can divide by
    // q^(n - 2), and check if the positive term is greater than the sum of the negative terms.
    q >= (&d - 1u8).complete() * (&d - 2u8).complete() * q.sqrt_ref().complete() + d.square() * 6u8
}

/// The main algorithm: returns true if the polynomial system
/// has solutions in the prime field.
/// Empty set is considered solvable.
pub fn prime_field_polynomial_system_solvability_test<
    O: polynomial::monomial_ordering::Ordering,
    I: polynomial::Id + std::hash::Hash,
    C: finite_field::PrimeField,
    P: polynomial::Power + Into<f64>,
>(
    mut polys: Vec<Polynomial<O, I, C, P>>,
) -> Result<bool, &'static str> {
    // We check the trivial cases first, use specialized techniques for them, and
    // only if there is no other resource, use the main algorithm from:
    // "Solving Systems of Polynomial Congruences Modulo a Large Prime" (1996)
    // by Ming-Deh Huang and Yiu-Chung Wong
    // https://doi.org/10.1109/SFCS.1996.548470

    // TODO: breakup the problem into independent sets
    // (i.e. sets of polynomials who don't share any variables).

    // Autoreduce polynomial set as it is relativelly cheap and
    // might help reducing the size of the problem:
    let polys = polynomial::grobner_basis::autoreduce(polys);

    // Test if anything is a solution to the system:
    if polys.is_empty() {
        return Ok(true);
    }

    // Find number of variables and maximum degree:
    let (n, d) = {
        let mut var_set = HashSet::new();

        let zero = P::zero();
        let mut degree = &zero;

        let mut has_constant_terms = false;

        for poly in polys.iter() {
            let terms = poly.get_terms();

            // Test if the polynomial has a constant:
            let last_term = terms.last().unwrap();
            if last_term.get_monomial().get_total_power().is_zero() {
                has_constant_terms = true;

                // Test if this polynomial has other, non-constant terms,
                // otherwise this system is trivially unsolvable:
                if terms.len() == 1 {
                    return Ok(false);
                }
            }

            // Iterate through terms, counting variables and degree
            for term in terms {
                let mon = term.get_monomial();
                if mon.get_total_power() > degree {
                    degree = mon.get_total_power();
                }

                for var in mon.get_product() {
                    var_set.insert(var.get_id().clone());
                }
            }
        }

        // Check if system is trivially solvable by setting all variables to zero:
        if !has_constant_terms {
            return Ok(true);
        }

        (var_set.len(), degree.clone())
    };

    // Since system has been reduced and still has no constant polynomials,
    // if it is linear then it is obviously solvable:
    if d.is_one() {
        return Ok(true);
    }

    // If the system is single variable, it can be solved by plain factorization.
    if n.is_one() {
        // Since the single variable system has been reduced,
        // only one polynomial must have remained:
        assert!(polys.len() == 1);
        let poly = polys.into_iter().next().unwrap();

        // If the polynomial has any irreducible linear factor, then it has a solution:
        for f in finite_field_factorize(poly) {
            if f.get_terms()[0].get_monomial().get_total_power().is_one() {
                return Ok(true);
            }
        }
        return Ok(false);
    }

    // Test for the single polynomial case:
    if polys.len() == 1 {
        todo!("Handle single polynomial case.");
    } else {
        todo!("Handle multiple polynomial case.");
    }
}

// Tests if a polynomial over finite field is absolutely irreducible.
