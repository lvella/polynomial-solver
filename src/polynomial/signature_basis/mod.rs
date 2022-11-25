//! Implementation of SB algorithm as defined in
//! "Practical Gröbner basis computation"
//! by Bjarke Hammersholt Roune and Michael Stillman
//! http://www.broune.com/papers/issac2012.html

mod basis_calculator;
mod s_pairs;
mod signature_monomial_index;

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Display,
    ops::{Bound::Excluded, Mul},
};

use self::{
    basis_calculator::{BasisCalculator, KnownBasis, SyzygySet},
    s_pairs::PartialSPair,
};

use super::{
    division::Field,
    divmask::{self, DivMaskTestResult},
};
use super::{monomial_ordering::Ordering, Exponent, Id, Monomial, Polynomial, Term};
use itertools::Itertools;
use num_traits::{One, Signed};

type CmpMap<O, I, P> = crate::fast_compare::ComparerMap<Signature<O, I, P>>;
type Ratio<O, I, P> = crate::fast_compare::FastCompared<Signature<O, I, P>>;

/// Tests if a set contains a divisor for a signature.
///
/// This is basically the implementation of signature criterion.
fn contains_divisor<O: Ordering, I: Id, P: SignedExponent>(
    msign: &MaskedSignature<O, I, P>,
    set: &SyzygySet<O, I, P>,
) -> bool {
    // Iterate over smaller signatures, testing if they are divisible
    let minimal = Signature {
        monomial: Monomial::one(),
        idx: msign.signature.idx,
    };

    let masked_dividend = &msign.monomial();

    for maybe_divisor in set.range(&minimal..=&msign.signature) {
        let masked_divisor = MaskedMonomialRef(maybe_divisor.1, &maybe_divisor.0.monomial);
        if masked_divisor.divides(masked_dividend) {
            return true;
        }
    }

    false
}

/// The Power type must be signed for this algorithm to work,
/// because we store the signature to leading monomial ratio, where
/// variable exponents can be negative.
pub trait SignedExponent: Exponent + Signed {}
impl<T> SignedExponent for T where T: Exponent + Signed {}

type DivMaskSize = u32;
type DivMap<P> = divmask::DivMap<DivMaskSize, P>;
type DivMask = divmask::DivMask<DivMaskSize>;

/// Wraps together a divmask and a (hopefully) corresponding monomial, wrapping
/// the divisibility test.
struct MaskedMonomialRef<'a, O: Ordering, I: Id, P: SignedExponent>(
    &'a DivMask,
    &'a Monomial<O, I, P>,
);

impl<'a, O: Ordering, I: Id, P: SignedExponent> MaskedMonomialRef<'a, O, I, P> {
    /// Uses the fast divmask comparison, and if it fails, uses the slow direct
    /// monomial comparison.
    fn divides(&self, other: &Self) -> bool {
        match self.0.divides(other.0) {
            DivMaskTestResult::NotDivisible => false,
            DivMaskTestResult::Unsure => self.1.divides(other.1),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskedSignature<O: Ordering, I: Id, P: SignedExponent> {
    divmask: DivMask,
    signature: Signature<O, I, P>,
}

impl<O: Ordering, I: Id, P: SignedExponent> MaskedSignature<O, I, P> {
    fn monomial(&self) -> MaskedMonomialRef<O, I, P> {
        MaskedMonomialRef(&self.divmask, &self.signature.monomial)
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
pub struct SignPoly<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    masked_signature: MaskedSignature<O, I, P>,

    polynomial: Polynomial<O, I, C, P>,
    /// The divmask fot the leading monomial.
    lm_divmask: DivMask,
    /// The inverse of the leading term coefficient. This is used repeatedly
    /// during reduction and is expensive to calculate.
    inv_leading_coeff: C,

    /// Own index inside the basis.
    idx: u32,

    /// The signature to leading monomial ratio allows us to quickly find
    /// out what is the signature of a new S-pair calculated.
    sign_to_lm_ratio: Ratio<O, I, P>,
}

impl<O: Ordering, I: Id, C: Field, P: SignedExponent + Display> Display for SignPoly<O, I, C, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "idx {}, sign {}: {} ...({})",
            self.idx,
            self.signature(),
            self.polynomial.terms[0].monomial,
            self.polynomial.terms.len() - 1
        )
    }
}

impl<O: Ordering, I: Id, C: Field, P: SignedExponent> SignPoly<O, I, C, P> {
    /// Compare SigPolys by signature to leading monomial ratio.
    fn sign_to_lm_ratio_cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sign_to_lm_ratio.cmp(&other.sign_to_lm_ratio)
    }

    /// Gets the leading monomial for division test.
    fn leading_monomial(&self) -> MaskedMonomialRef<O, I, P> {
        MaskedMonomialRef(&self.lm_divmask, &self.polynomial.terms[0].monomial)
    }

    fn signature(&self) -> &Signature<O, I, P> {
        &self.masked_signature.signature
    }
}

struct PointedCmp<T>(*const T);

impl<T: PartialEq> PartialEq for PointedCmp<T> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { *self.0 == *other.0 }
    }
}

impl<T: Eq> Eq for PointedCmp<T> {}

impl<T: PartialOrd> PartialOrd for PointedCmp<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe { (*self.0).partial_cmp(&*other.0) }
    }
}

impl<T: Ord> Ord for PointedCmp<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        unsafe { (*self.0).cmp(&*other.0) }
    }
}

/// The 3 possible results of a regular reduction.
enum RegularReductionResult<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// Polynomial was singular top reducible
    Singular,
    /// Polynomial was reduced to zero.
    Zero(MaskedSignature<O, I, P>),
    /// Polynomial was reduced to some non-zero constant.
    NonZeroConstant(Polynomial<O, I, C, P>),
    /// Polynomial was reduced to some non singular top reducible polynomial.
    Reduced(SignPoly<O, I, C, P>),
}

/// Tests for singular criterion: searches the basis members for an element
/// that would make the S-pair redundant.
///
/// Returns true if the S-pair is singular and must be eliminated.
fn test_singular_criterion<O: Ordering, I: Id, C: Field, P: SignedExponent>(
    m_sign: &MaskedSignature<O, I, P>,
    s_pair: &PartialSPair<O, I, C, P>,
    basis: &KnownBasis<O, I, C, P>,
) -> bool {
    // All this trickery with inner function just to avoid copying the
    // lowest_monomial_ratio from basis to create upper_limit.
    //
    // TODO: fix this very ugly hack
    fn inner<O: Ordering, I: Id, C: Field, P: SignedExponent>(
        upper_limit: &Ratio<O, I, P>,
        m_sign: &MaskedSignature<O, I, P>,
        s_pair: &PartialSPair<O, I, C, P>,
        basis: &KnownBasis<O, I, C, P>,
    ) -> bool {
        // Limit search to elements whose signature/lm ratio are greater than the
        // current candidate we have, in descending order, so that the first match
        // we find will be the one with the smallest leading monomial.
        let lower_limit = sign_to_monomial_ratio(&m_sign.signature, &s_pair.leading_term.monomial);
        let search_range = basis
            .by_sign_lm_ratio
            .range((
                Excluded((PointedCmp(&lower_limit), u32::MAX)),
                Excluded((PointedCmp(upper_limit), u32::MIN)),
            ))
            .rev();

        let masked_sig_monomial = m_sign.monomial();

        for (_, singular) in search_range {
            let singular = unsafe { &**singular };
            assert!(singular.signature().idx == m_sign.signature.idx);
            // Test singular criterion: if we find some element p whose signature
            // divides the S-pair's signature, it means there is some f such that
            // f*e has the same signature. Since we only search greater sign/LM
            // ratio, f*e will necessarily have smaller LM than the S-pair, which
            // means that this S-pair can be eliminated immediately, according to
            // Section 3.2 of the paper.
            if singular
                .masked_signature
                .monomial()
                .divides(&masked_sig_monomial)
            {
                return true;
            }
        }

        false
    }

    let upper_limit = Ratio::new(
        None,
        Signature {
            // The higher index will limit the search to smaller indices.
            idx: m_sign.signature.idx + 1,
            monomial: basis.lowest_monomial_ratio.replace(Monomial::one()),
        },
    )
    .unwrap();

    let ret = inner(&upper_limit, m_sign, s_pair, basis);

    basis
        .lowest_monomial_ratio
        .set(upper_limit.into_inner().monomial);

    ret
}

/// Regular reduction, as defined in the paper.
///
/// This is analogous to calculate the remainder on a multivariate polynomial
/// division, but with extra restrictions on what polynomials can be the divisor
/// according to their signature.
fn regular_reduce<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display>(
    idx: u32,
    m_sign: MaskedSignature<O, I, P>,
    reduced_poly: Polynomial<O, I, C, P>,
    basis: &KnownBasis<O, I, C, P>,
) -> RegularReductionResult<O, I, C, P> {
    // The paper suggests splitting the reduced polynomial into a hash map of
    // monomial -> coefficient, so that we can efficiently sum the new terms,
    // and a priority queue, so that we know what is the next monomial to be
    // reduced. We can do both with a single BTreeMap, which is ordered and has
    // fast map access. I have tested both solutions, and in bigger problems
    // BTreeMap seems a little better.

    // The tree with the terms to be reduced.
    let mut to_reduce: BTreeMap<Monomial<O, I, P>, C> = reduced_poly
        .terms
        .into_iter()
        // Since this is already reverse sorted, rev() is a little faster, as we
        // insert the elements in increasing order.
        .rev()
        .map(|term| (term.monomial, term.coefficient))
        .collect();

    // Reduce one term at a time.
    let mut reduced_terms = Vec::new();
    let mut lm_properties = None;

    while let Some((m, c)) = to_reduce.pop_last() {
        // Reassemble the term
        let term = Term {
            coefficient: c,
            monomial: m,
        };

        // Skip searching for a divisor for 1 and (maybe) save some time.
        if term.monomial.is_one() {
            reduced_terms.push(term);
            break;
        }

        // Calculate the divmask for the term to be reduced:
        let divmask = basis.div_map.map(&term.monomial);

        // Calculate signature to monomial ratio, to search for a reducer,
        // and possibly store it as the ratio for the leading term.
        let sign_to_term_ratio = sign_to_monomial_ratio(&m_sign.signature, &term.monomial);

        if let Some(reducer) = basis.find_a_reducer(
            &sign_to_term_ratio,
            MaskedMonomialRef(&divmask, &term.monomial),
        ) {
            // The reduction is said singular if we are reducing the leading
            // term and the factor*reducer have the same signature as the reduced.
            // This translates to equal signature/monomial ratio. In this case
            // we can stop.
            if reduced_terms.is_empty() && reducer.sign_to_lm_ratio == sign_to_term_ratio {
                return RegularReductionResult::Singular;
            }

            let mut iter = reducer.polynomial.terms.iter();
            let leading_term = iter.next().unwrap();

            // Calculate the multiplier monomial that will nullify the term.
            // We can unwrap() because we trust "find_a_regular_reducer" to
            // have returned a valid reducer.
            let monomial = term
                .monomial
                .whole_division(&leading_term.monomial)
                .unwrap();

            // Calculate the multiplier's coefficient using the reducer leading term:
            let coefficient = term
                .coefficient
                .elimination_factor(&reducer.inv_leading_coeff);

            let factor = Term {
                coefficient,
                monomial,
            };

            // Subtract every element of the reducer from the rest of the
            // polynomial.
            for term in iter {
                use std::collections::btree_map::Entry;

                let reducer_term = factor.clone() * term.clone();

                match to_reduce.entry(reducer_term.monomial) {
                    Entry::Vacant(entry) => {
                        // There was no such monomial, just insert:
                        entry.insert(reducer_term.coefficient);
                    }
                    Entry::Occupied(mut entry) => {
                        // Sum the coefficients, and remove if result is zero.
                        *entry.get_mut() += reducer_term.coefficient;
                        if entry.get().is_zero() {
                            entry.remove_entry();
                        }
                    }
                }
            }

            // Don't insert any new term in the final polynomial, as the
            // term has been eliminated.
            continue;
        }
        // No reducer was found.

        // The term could not be reduced. Store the ratio if this is the
        // leading term:
        if let None = lm_properties {
            assert!(reduced_terms.len() == 0);
            lm_properties = Some((sign_to_term_ratio, divmask));
        }

        // And insert it into the output. These terms are already in
        // decreasing order.
        reduced_terms.push(term)
    }

    let polynomial = Polynomial {
        terms: reduced_terms,
    };

    match lm_properties {
        Some((sign_to_lm_ratio, lm_divmask)) => RegularReductionResult::Reduced(SignPoly {
            inv_leading_coeff: polynomial.terms[0].coefficient.clone().inv(),
            masked_signature: m_sign,
            polynomial,
            lm_divmask,
            idx,
            sign_to_lm_ratio,
        }),
        None => {
            // The only way for lm_properties to be None is when
            // reduced_terms is empty or constant.
            match polynomial.terms.len() {
                0 => RegularReductionResult::Zero(m_sign),
                1 => {
                    assert!(polynomial.is_constant());
                    RegularReductionResult::NonZeroConstant(polynomial)
                }
                _ => panic!("This should never happen!"),
            }
        }
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

    // Something was added to the basis calculator, be it polynomial or
    // syzygy, so the monomials might have changed enough to justify
    // a recalculation of the divmasks.
    c.maybe_recalculate_divmasks();

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
            let m_sign = MaskedSignature {
                divmask: c.get_basis().div_map.map(&monomial),
                signature: Signature {
                    idx: i as u32,
                    monomial,
                },
            };

            // Reduce it:
            let b = c.get_basis();
            regular_reduce(b.polys.len() as u32, m_sign, p, b)
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
            let reduction = regular_reduce(b.polys.len() as u32, m_sign, s_pair, b);
            early_ret_err!(handle_reduction_result(&mut c, reduction, &indices[..]));
        }
    }

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
