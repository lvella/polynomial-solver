//! Implementation of SB algorithm as defined in
//! "Practical Gröbner basis computation"
//! by Bjarke Hammersholt Roune and Michael Stillman
//! http://www.broune.com/papers/issac2012.html

mod basis_calculator;
mod indices;
mod s_pairs;

use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    fmt::Display,
    ops::Mul,
};

use self::basis_calculator::{BasisCalculator, KnownBasis, RegularReductionResult};

use super::{
    division::Field,
    divmask::{self, DivMaskTestResult},
};
use super::{monomial_ordering::Ordering, Exponent, Id, Monomial, Polynomial, Term};
use itertools::Itertools;
use num_traits::{One, Signed};

type CmpMap<O, I, P> = crate::fast_compare::ComparerMap<Signature<O, I, P>>;
type Ratio<O, I, P> = crate::fast_compare::FastCompared<Signature<O, I, P>>;

/// Returns the exponent of a variable inside a monomial.
fn get_var_exp_from_monomial<O: Ordering, I: Id, E: SignedExponent>(
    monomial: &Monomial<O, I, E>,
    id: &I,
) -> E {
    let m = &monomial.product;
    // Is binary search better than linear?
    // TODO: Maybe create a dense monomial to skip this search?
    match m.binary_search_by(|v| id.cmp(&v.id)) {
        Ok(idx) => m[idx].power.clone(),
        Err(_) => E::zero(),
    }
}

/// The Power type must be signed for this algorithm to work,
/// because we store the signature to leading monomial ratio, where
/// variable exponents can be negative.
pub trait SignedExponent: Exponent + Signed {}
impl<T> SignedExponent for T where T: Exponent + Signed {}

type DivMaskSize = u32;
type DivMap<P> = divmask::DivMap<DivMaskSize, P>;
type DivMask = divmask::DivMask<DivMaskSize>;

trait HasMonomial {
    type O: Ordering;
    type I: Id;
    type E: SignedExponent;
    fn monomial(&self) -> &Monomial<Self::O, Self::I, Self::E>;
}

impl<O: Ordering, I: Id, E: SignedExponent> HasMonomial for Monomial<O, I, E> {
    type O = O;
    type I = I;
    type E = E;

    fn monomial(&self) -> &Monomial<Self::O, Self::I, Self::E> {
        self
    }
}

/// Wraps together a divmask and a corresponding monomial, allowing for
/// accelerated divisibility test.
#[derive(Debug, Clone)]
struct Masked<T: HasMonomial> {
    divmask: DivMask,
    value: T,
}

impl<T: HasMonomial> Masked<T> {
    /// Uses the fast divmask comparison, and if it fails, uses the slow direct
    /// monomial comparison.
    fn divides<U: HasMonomial<O = T::O, I = T::I, E = T::E>>(&self, other: &Masked<U>) -> bool {
        match self.divmask.divides(&other.divmask) {
            DivMaskTestResult::NotDivisible => false,
            DivMaskTestResult::Unsure => self.value.monomial().divides(&other.value.monomial()),
        }
    }
}

/// The signature of a polynomial.
///
/// The signature of a polynomial is used to track what monomial multiplied by
/// which of the input polynomials originated it. For the formal definition, see
/// the paper.
///
/// There is a total order among signatures that is related to the monomial
/// ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature<O: Ordering, I: Id, P: SignedExponent> {
    idx: u32,
    monomial: Monomial<O, I, P>,
}

impl<O: Ordering, I: Id, E: SignedExponent> HasMonomial for Signature<O, I, E> {
    type O = O;
    type I = I;
    type E = E;

    fn monomial(&self) -> &Monomial<Self::O, Self::I, Self::E> {
        &self.monomial
    }
}

impl<O: Ordering, I: Id, P: SignedExponent> Mul<Monomial<O, I, P>> for Signature<O, I, P> {
    type Output = Self;

    fn mul(mut self, rhs: Monomial<O, I, P>) -> Self {
        self.monomial = self.monomial * rhs;
        self
    }
}

impl<O: Ordering, I: Id, P: SignedExponent + Display> Display for Signature<O, I, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{{}, {}}}", self.idx, self.monomial)
    }
}

/// Calculates signature to term ratio.
///
/// By allowing negative exponents, we can calculate the ratio between
/// a signature and a monomial, which is useful for comparison.
fn sign_to_monomial_ratio<O: Ordering, I: Id, P: SignedExponent>(
    signature: &Signature<O, I, P>,
    monomial: &Monomial<O, I, P>,
) -> Ratio<O, I, P> {
    let monomial = signature.monomial.fraction_division(monomial);

    Ratio::new(
        None,
        Signature {
            monomial,
            ..*signature
        },
    )
    .unwrap()
}

/// Signature polynomial.
///
/// In the paper, the SB algorithm is described in terms of elements of a
/// polynomial module, but it turns out that representing this element as a pair
/// (signature, polynomial) is sufficient for all the computations. Other fields
/// are optimizations.
#[derive(Debug)]
struct SignPoly<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// Own index inside the basis vector.
    idx: u32,

    /// Holds the signature for this polynomial
    masked_signature: Masked<Signature<O, I, P>>,

    /// The leading monomial of the polynomial.
    lm: Masked<Monomial<O, I, P>>,

    /// The leading coefficient of the polynomial.
    leading_coeff: C,

    /// The remaining terms of the polynomial, in descending order.
    ///
    /// This is a RefCell because if this SignPoly is classified as a hot
    /// reducer, the tail is fully reduced to save time when this polynomial is
    /// used in further reductions.
    tail: RefCell<Vec<Term<O, I, C, P>>>,

    /// Tells if this polynomial has been marked as a hot reducer, to prevent it
    /// to be reinserted in the list of polynomials to be hot reduced.
    is_hot_reducer: Cell<bool>,

    /// The inverse of the leading term coefficient. This is used repeatedly
    /// during reduction and is expensive to calculate.
    inv_leading_coeff: C,

    /// The signature to leading monomial ratio allows us to quickly find out
    /// what is the signature of a new S-pair calculated.
    ///
    /// This is a RefCell because on every insertion new SignPoly inserted on
    /// the basis, there might be a need to recalculate the comparer (integer
    /// used for accelerated ord comparision).
    sign_to_lm_ratio: RefCell<Ratio<O, I, P>>,

    /// The number of times this polynomial has been used as reducer.
    as_reducer_count: Cell<usize>,
}

impl<O: Ordering, I: Id, C: Field, P: SignedExponent + Display> Display for SignPoly<O, I, C, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "idx {}, sign {}: {} ...({})",
            self.idx,
            self.signature(),
            self.lm.value,
            self.tail.borrow().len()
        )
    }
}

impl<O: Ordering, I: Id, C: Field, P: SignedExponent> SignPoly<O, I, C, P> {
    /// Compare SigPolys by signature to leading monomial ratio.
    fn sign_to_lm_ratio_cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sign_to_lm_ratio.cmp(&other.sign_to_lm_ratio)
    }

    fn signature(&self) -> &Signature<O, I, P> {
        &self.masked_signature.value
    }

    fn into_polynomial(self) -> Polynomial<O, I, C, P> {
        let mut terms = self.tail.into_inner();
        terms.insert(
            0,
            Term {
                coefficient: self.leading_coeff,
                monomial: self.lm.value,
            },
        );
        Polynomial { terms }
    }
}

/// Handles the result of a reduction, and returns Err(Polynomial) in case of
/// constant, for early termination.
fn handle_reduction_result<
    O: Ordering,
    I: Id + Display,
    F: Field + Display,
    E: SignedExponent + Display,
>(
    c: &mut BasisCalculator<O, I, F, E>,
    reduction: RegularReductionResult<O, I, F, E>,
    spair_indices: &[(u32, u32)],
) -> Result<(), Vec<Polynomial<O, I, F, E>>> {
    match reduction {
        RegularReductionResult::Reduced(reduced) => {
            println!(
                "#(p: {}, s: {}), {:?} → {}",
                c.get_basis().polys.len(),
                c.get_num_syzygies(),
                spair_indices,
                reduced
            );

            // Polynomial is a new valid member of the basis. Insert it into
            // the basis.
            c.insert_poly_with_spairs(reduced);

            // Generate the corresponding Koszul syzygy to help eliminating
            // future S-pairs.
            c.add_koszul_syzygies(spair_indices);
        }
        RegularReductionResult::Zero(signature) => {
            // Polynomial reduces to zero, so we keep the signature to
            // eliminate S-pairs before reduction.
            c.add_spair_syzygy(signature, spair_indices);
        }
        RegularReductionResult::Singular => {
            // Polynomial was singular top reducible, so it was redundant
            // and discarded.
            return Ok(());
        }
        RegularReductionResult::NonZeroConstant(polynomial) => {
            // The new basis member is a constant, so it reduces everything
            // to zero and we can stop.
            return Err(vec![polynomial]);
        }
    }

    Ok(())
}

macro_rules! early_ret_err {
    ($result: expr) => {
        match $result {
            Ok(x) => x,
            Err(e) => return e,
        }
    };
}
/// Calculates a Grobner Basis using the Signature Buchberger (SB) algorithm.
///
/// The returned basis will not be reduced.
pub fn grobner_basis<
    O: Ordering,
    I: Id + Display,
    C: Field + Display,
    P: SignedExponent + Display,
>(
    input: Vec<Polynomial<O, I, C, P>>,
) -> Vec<Polynomial<O, I, C, P>> {
    // Quick sanity check if any of the inputs are constants, and get the
    // maximum variable id.
    let mut max_var_id = 0;
    for p in input.iter() {
        if p.is_constant() && !p.is_zero() {
            // If there is a constant, the GB for this input is trivial.
            return vec![Polynomial::new_constant(C::one())];
        }

        for t in p.terms.iter() {
            for var in t.monomial.product.iter() {
                let var_id = var.id.to_idx();
                if max_var_id < var_id {
                    max_var_id = var_id;
                }
            }
        }
    }

    let mut c = BasisCalculator::new(max_var_id + 1);

    // We incrementally add the input polynomials one by one, and expand the
    // calculated Gröbner Basis each time. This can be done because in the
    // signature order we use, called the "pot" order by "A survey on
    // signature-based algorithms for computing Gröbner bases" (Eder & Faugère,
    // 2017), all the S-pairs among the previous input polynomials have:
    //
    // a) smaller signature than the next input polynomial and all its S-pairs
    // descendants, so we don't break the rule that the new polynomials inserted
    // into the basis must be processed in incremental signature order;
    //
    // b) smaller signature/LM ratios than the next input polynomial, so it
    // can't possibly be a regular reducer for any of the previous basis
    // elements.
    //
    // This doesn't hold for "top" or other arbitrary signature orders, but
    // "pot" seems to be the most efficient order (and we are using it).
    for (i, p) in input.into_iter().enumerate() {
        let reduction = {
            // Assemble the signature for the new polynomial:
            let monomial = Monomial::one();
            let m_sign = Masked {
                divmask: c.get_basis().div_map.map(&monomial),
                value: Signature {
                    idx: i as u32,
                    monomial,
                },
            };

            // Reduce it:
            let b = c.get_basis();
            c.regular_reduce_head(
                b.polys.len() as u32,
                m_sign,
                p.terms
                    .into_iter()
                    .rev()
                    .map(|t| (t.monomial, t.coefficient))
                    .collect(),
            )
        };

        early_ret_err!(handle_reduction_result(&mut c, reduction, &[]));

        // Main loop, reduce every S-pair and insert in the basis until there are no
        // more S-pairs to be reduced. Since each newly inserted polynomials can
        // generate up to n-1 new S-pairs, this loop is exponential.
        loop {
            let (m_sign, s_pair, indices) = if let Some(next_spair) = c.get_next_spair() {
                next_spair
            } else {
                break;
            };

            let b = c.get_basis();
            let reduction = c.regular_reduce_head(b.polys.len() as u32, m_sign, s_pair);
            early_ret_err!(handle_reduction_result(&mut c, reduction, &indices[..]));

            // Something was added to the basis calculator, be it polynomial or syzygy,
            // so the monomials might have changed enough to justify a recalculation of
            // the divmasks and indices.
            //
            // Also, new reducers might have been classified as hot.
            c.optimize_structures();
        }

        // Syzygies found in this iteration are no longer useful in the next,
        // because the next signatures will have a different index, and are not
        // divisible by the currently known syzygies.
        c.clear_syzygies();
    }

    c.print_statistics();

    // Return the polynomials from the basis.
    c.into_iter().collect()
}

/// Change the variables so that they are a dense set starting from 0.
pub fn make_dense_variable_set<O: Ordering, I: Id, F: Field, E: Exponent>(
    polynomials: &mut [Polynomial<O, I, F, E>],
) -> HashMap<usize, usize> {
    // Figure out what variables are used:
    let mut used_set = HashSet::new();
    for p in polynomials.iter() {
        for t in p.terms.iter() {
            for var in t.monomial.product.iter() {
                used_set.insert(var.id.to_idx());
            }
        }
    }

    // Make a map from old values to new values without changing the relative
    // order.
    let var_map: HashMap<usize, usize> = used_set
        .into_iter()
        .sorted()
        .enumerate()
        .map(|(new_val, old_val)| (old_val, new_val))
        .collect();

    // Replace the variables in the polynomials.
    for p in polynomials.iter_mut() {
        for t in p.terms.iter_mut() {
            for var in t.monomial.product.iter_mut() {
                let new_idx = *var_map.get(&var.id.to_idx()).unwrap();
                var.id = I::from_idx(new_idx);
            }
        }
    }

    var_map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::division::tests::*;
    use num_traits::{Inv, Pow};

    #[test]
    fn grobner_basis_test() {
        let [x, y, z]: [QPoly; 3] = QPoly::new_variables([2, 1, 0u8]).try_into().unwrap();
        let eqs = [
            x.clone() * x.clone() + y.clone() * y.clone() + z.clone() * z.clone() - r(1),
            x.clone() * x.clone() - y.clone() + z.clone() * z.clone(),
            x.clone() - z.clone(),
        ];

        let grobner_basis = grobner_basis(eqs.into());
        let grobner_basis = crate::polynomial::grobner_basis::autoreduce(grobner_basis);
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
                result * result.terms[0].coefficient.clone().inv(),
                &expected * expected.terms[0].coefficient.clone().inv()
            );
        }
    }
}
