// TODO: possible optimizations for this grubner basis calculator:
// - Implement Faugère's F4 and F5 algorithms
//    - https://en.wikipedia.org/wiki/Faug%C3%A8re%27s_F4_and_F5_algorithms
// - Use degrevlex ordering, and then transform to lex, which is cheaper than calculating in lex directly

use crate::{
    ordered_ops,
    polynomial::{Id, Polynomial, Power, Term},
};

use itertools::Itertools;
use num_traits::Zero;
use std::{
    cmp::Reverse,
    collections::{BTreeSet, HashMap, VecDeque},
    rc::Rc,
};

use super::{division::InvertibleCoefficient, monomial_ordering::Ordering, Coefficient, Monomial};

/// Replace polynomial variables so that they have an order that is
/// more suitable to calculate the Gröbner Basis, according to this:
/// https://gitlab.trnsz.com/reduce-algebra/reduce-algebra/-/blob/master/packages/groebner/groebopt.red
///
/// Returns a map from the old variables to the new ones.
pub fn reorder_vars_for_easier_gb<O, C, P>(
    polynomials: &mut Vec<Polynomial<O, usize, C, P>>,
) -> HashMap<usize, usize>
where
    O: Ordering,
    C: Coefficient,
    P: Power,
{
    let mut var_map = HashMap::new();

    for p in polynomials.iter() {
        for t in p.terms.iter() {
            for var in t.monomial.product.iter() {
                let entry = var_map.entry(var.id).or_insert((P::zero(), 0usize));
                if entry.0 < t.monomial.total_power {
                    *entry = (t.monomial.total_power.clone(), 1);
                } else {
                    entry.1 += 1;
                }
            }
        }
    }

    let mut reordered: Vec<_> = var_map.keys().copied().collect();
    reordered.sort_unstable_by_key(|id| var_map.get(id).unwrap());

    let var_map: HashMap<usize, usize> = reordered.into_iter().zip(0..).collect();

    for p in polynomials.iter_mut() {
        for t in p.terms.iter_mut() {
            for var in t.monomial.product.iter_mut() {
                let new_id = var_map.get(&var.id).unwrap();
                var.id = *new_id;
            }

            t.monomial.product.sort_unstable_by_key(|w| Reverse(w.id));
        }

        p.terms.sort_unstable_by(|a, b| b.monomial.cmp(&a.monomial));
    }

    var_map
}

fn reduce<O, I, C, P>(
    p: &mut Polynomial<O, I, C, P>,
    g: &BTreeSet<Rc<Polynomial<O, I, C, P>>>,
) -> bool
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let mut was_reduced = false;

    'outer: loop {
        // Try to reduce using every polynomial <= p in g, in decreasing order:
        for gp in g.range::<Polynomial<O, I, C, P>, _>(..=&*p).rev() {
            let divisor = std::mem::replace(p, Polynomial::zero());
            let (quot, rem) = divisor.div_rem(&gp).unwrap();
            *p = rem;
            if !quot.is_zero() {
                was_reduced = true;

                if p.is_constant() {
                    // Can't be further reduced
                    break 'outer;
                }
                continue 'outer;
            }
        }

        // Could not reduced with any polynomial in g, so stop:
        break;
    }

    was_reduced
}

/// g must be the sole owner of the polynomials, otherwise this will panic
fn autoreduce<O, I, C, P>(
    mut g: BTreeSet<Rc<Polynomial<O, I, C, P>>>,
) -> BTreeSet<Rc<Polynomial<O, I, C, P>>>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    loop {
        let mut next_g = BTreeSet::new();
        let mut modified = false;
        while let Some(mut p) = g.pop_last() {
            if reduce(Rc::get_mut(&mut p).unwrap(), &g) {
                modified = true;
            }
            if !p.is_zero() {
                if p.is_constant() {
                    // Cut short the calculation in case of constant
                    return BTreeSet::from([p]);
                }
                next_g.insert(p);
            }
        }

        if !modified {
            return next_g;
        }
        g = next_g;
    }
}

fn spar_reduce<O, I, C, P>(
    p: &Polynomial<O, I, C, P>,
    q: &Polynomial<O, I, C, P>,
    current_set: &BTreeSet<Rc<Polynomial<O, I, C, P>>>,
) -> Option<Polynomial<O, I, C, P>>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let ini_p = p.terms.get(0)?;
    let ini_q = q.terms.get(0)?;

    let sat_diff = |a: &Term<O, I, C, P>, b: &Term<O, I, C, P>| {
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
            _phantom_ordering: std::marker::PhantomData,
        };

        Term {
            monomial,
            coefficient: a.coefficient.clone(),
        }
    };

    let p_complement = sat_diff(ini_q, ini_p);
    let mut q_complement = sat_diff(ini_p, ini_q);

    // q_complement must be negative, so the sum would eliminate the first term:
    q_complement.coefficient = {
        let mut neg = C::zero();
        neg -= q_complement.coefficient;
        neg
    };

    let mut spar = Polynomial {
        terms: Polynomial::sum_terms(
            p.terms[1..]
                .iter()
                .cloned()
                .map(|x| x * p_complement.clone()),
            q.terms[1..]
                .iter()
                .cloned()
                .map(|x| x * q_complement.clone()),
        ),
    };

    reduce(&mut spar, current_set);

    if spar.is_zero() {
        None
    } else {
        Some(spar)
    }
}

pub fn grobner_basis<O, I, C, P>(
    input: BTreeSet<Rc<Polynomial<O, I, C, P>>>,
) -> BTreeSet<Rc<Polynomial<O, I, C, P>>>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    let mut current_set = input;

    'restart: loop {
        print!("autoreducing ...");
        current_set = autoreduce(current_set);

        {
            let mut total_term_count = 0;
            let mut total_var_count = 0;
            for p in current_set.iter() {
                total_term_count += p.terms.len();
                for t in p.terms.iter() {
                    total_var_count += t.monomial.product.len();
                }
            }

            println!(
                " poly count: {}, total term count: {}, total var count: {}",
                current_set.len(),
                total_term_count,
                total_var_count
            );
        }

        let mut current_vec: Vec<_> = current_set.iter().rev().cloned().collect();

        let mut work_queue: VecDeque<Box<dyn Iterator<Item = (usize, usize)>>> = VecDeque::new();
        work_queue.push_back(Box::new((0..current_vec.len()).tuple_combinations()));

        let mut new_count = 0u16;
        while let Some(work) = work_queue.pop_front() {
            for (i, j) in work {
                if let Some(new_p) = spar_reduce(&current_vec[i], &current_vec[j], &current_set) {
                    // Cut short the calculation in case of constant:
                    let new_p = Rc::new(new_p);
                    if new_p.is_constant() {
                        return BTreeSet::from([new_p]);
                    }

                    let curr_len = current_vec.len();
                    work_queue.push_back(Box::new(
                        std::iter::once(curr_len).cartesian_product(0..curr_len),
                    ));

                    println!(
                        "#### {},  deg: {:?}",
                        current_vec.len(),
                        new_p.terms[0].monomial.total_power
                    );

                    current_vec.push(new_p.clone());
                    current_set.insert(new_p);

                    new_count += 1;
                    if new_count >= 1 {
                        continue 'restart;
                    }
                }
            }
        }

        break;
    }

    autoreduce(current_set)
}

pub fn grobner_basis_from_iter<O, I, C, P>(
    input: impl Iterator<Item = Polynomial<O, I, C, P>>,
) -> BTreeSet<Rc<Polynomial<O, I, C, P>>>
where
    O: Ordering,
    I: Id,
    C: InvertibleCoefficient,
    P: Power,
{
    grobner_basis(input.map(|p| Rc::new(p)).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::division::tests::*;
    use num_traits::{Inv, Pow};

    #[test]
    fn reduction_step_test() {
        // Can't use SmallPoly because i32 is not invertible
        let [x, y]: [QPoly; 2] = QPoly::new_variables([1u8, 0u8]).try_into().unwrap();

        let p = &(x.clone().pow(5u8) * y.clone().pow(3u8)) * r(4);

        let q = &x.clone().pow(3u8) * r(2) - y.clone() * x.clone() + &y.clone() * r(2) - r(3);

        let (quot, reduced) = p.clone().div_rem(&q).unwrap();
        println!("quot: {}, rem: {}", quot, reduced);

        let reconstructed_p = reduced + quot * q;

        assert_eq!(reconstructed_p, p);
    }

    #[test]
    fn grobner_basis_test() {
        let [x, y, z]: [QPoly; 3] = QPoly::new_variables([2, 1, 0u8]).try_into().unwrap();
        let eqs = [
            x.clone() * x.clone() + y.clone() * y.clone() + z.clone() * z.clone() - r(1),
            x.clone() * x.clone() - y.clone() + z.clone() * z.clone(),
            x.clone() - z.clone(),
        ];

        let grobner_basis = grobner_basis_from_iter(eqs.into_iter());
        println!("Gröbner Basis:");
        for p in grobner_basis.iter() {
            println!("{}", p);
        }

        let expected_solution = [
            &z.clone().pow(4u8) * r(4) + &z.clone().pow(2u8) * r(2) - r(1),
            y.clone() - &z.clone().pow(2u8) * r(2),
            x - z,
        ];

        for (result, expected) in grobner_basis.iter().zip(expected_solution) {
            assert_eq!(
                result.as_ref() * result.terms[0].coefficient.clone().inv(),
                &expected * expected.terms[0].coefficient.clone().inv()
            );
        }
    }

    #[test]
    fn test_grobner_basis_equal_1() {
        let [x, y]: [QPoly; 2] = QPoly::new_variables([1, 0u8]).try_into().unwrap();
        let unsolvable = [
            x.clone().pow(2u8) + x.clone() * y.clone() - r(10),
            x.clone().pow(3u8) + x.clone() * y.clone().pow(2u8) - r(25),
            x.clone().pow(4u8) + x.clone() * y.clone().pow(3u8) - r(70),
        ];

        let grobner_basis = grobner_basis_from_iter(unsolvable.into_iter());

        assert_eq!(grobner_basis.len(), 1);
        let p = grobner_basis.first().unwrap();
        assert!(p.is_constant() && !p.is_zero());

        println!("{}", grobner_basis.first().unwrap());
    }

    #[test]
    fn test_resilience_to_weird_input() {
        // Assert only the non-zero element remains:
        /*let zero_in_the_set =
            grobner_basis_from_iter([QPoly::new_constant(r(42)), QPoly::zero()].into_iter());

        assert_eq!(zero_in_the_set.len(), 1);
        let p = zero_in_the_set.first().unwrap();
        assert!(p.is_constant() && !p.is_zero());*/

        // Assert set is empty:
        let empty: BTreeSet<Rc<QPoly>> = grobner_basis_from_iter([].into_iter());
        assert!(empty.is_empty());
    }
}
