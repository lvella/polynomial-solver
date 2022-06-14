//! Implementation of SB algorithm as defined in
//! "Practical Gröbner basis computation"
//! by Bjarke Hammersholt Roune and Michael Stillman
//! http://www.broune.com/papers/issac2012.html

mod s_pairs;

use std::{
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap},
    fmt::Display,
    hash::Hash,
};

use super::division::InvertibleCoefficient;
use super::{monomial_ordering::Ordering, Id, Monomial, Polynomial, Power, Term};
use itertools::Itertools;
use num_traits::{One, Zero};

use num_traits::Signed;

/// The Power type must be signed for this algorithm to work,
/// because we store the signature to leading monomial ratio, where
/// variable exponents can be negative.
pub trait SignedPower: Power + Signed {}
impl<T> SignedPower for T where T: Power + Signed {}

/// The signature of a polynomial.
///
/// The signature of a polynomial is used to track what monomial multiplied by
/// which of the input polynomials originated it. For the formal definition, see
/// the paper.
///
/// There is a total order among signatures that is related to the monomial
/// ordering.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Signature<O: Ordering, I: Id, P: SignedPower> {
    idx: u32,
    monomial: Monomial<O, I, P>,
}

impl<O: Ordering, I: Id + Display, P: SignedPower + Display> Display for Signature<O, I, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{{}, {}}}", self.idx, self.monomial)
    }
}

/// Calculates signature to term ratio.
///
/// By allowing negative exponents, we can calculate the ratio between
/// a signature and a monomial, which is useful for comparison.
fn sign_to_monomial_ratio<O: Ordering, I: Id, P: SignedPower>(
    signature: &Signature<O, I, P>,
    monomial: &Monomial<O, I, P>,
) -> Signature<O, I, P> {
    let monomial = signature.monomial.fraction_division(monomial);

    Signature {
        monomial,
        ..*signature
    }
}

/// Signature polynomial.
///
/// In the paper, the SB algorithm is described in terms of elements of a
/// polynomial module, but it turns out that representing this element as a
/// pair (signature, polynomial) is sufficient for all the computations.
/// Other fields are optimizations.
struct SignPoly<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    signature: Signature<O, I, P>,
    polynomial: Polynomial<O, I, C, P>,

    /// The signature to leading monomial ratio allows us to quickly find
    /// out what is the signature of a new S-pair calculated.
    ///
    /// TODO: there is an optimization where every such ratio is assigned an
    /// integer, thus can be compared in one instruction.
    sign_to_lm_ratio: Signature<O, I, P>,
}

impl<O: Ordering, I: Id + Display, C: InvertibleCoefficient, P: SignedPower + Display> Display
    for SignPoly<O, I, C, P>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} ...({})",
            self.signature,
            self.polynomial.terms[0].monomial,
            self.polynomial.terms.len() - 1
        )
    }
}

impl<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> SignPoly<O, I, C, P> {
    /// Creates a new Signature Polynomial.
    ///
    /// Polynomial can not be zero, otherwise this will panic.
    fn new(signature: Signature<O, I, P>, polynomial: Polynomial<O, I, C, P>) -> Self {
        let sign_to_lm_ratio = sign_to_monomial_ratio(&signature, &polynomial.terms[0].monomial);

        Self {
            signature,
            polynomial,
            sign_to_lm_ratio,
        }
    }

    /// Compare SigPolys by signature to leading monomial ratio.
    fn sign_to_lm_ratio_cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sign_to_lm_ratio.cmp(&other.sign_to_lm_ratio)
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

impl<T: Hash> Hash for PointedCmp<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (*self.0).hash(state) };
    }
}

/// Stores all the basis elements known and processed so far,
struct KnownBasis<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// Owns the basis polynomials, ordered by insertion order (which is
    /// important to the spair triangle).
    polys: Vec<Box<SignPoly<O, I, C, P>>>,

    /// Signatures of polynomials know to reduce to zero.
    ///
    /// TODO: like the above, use a proper multidimensional index.
    syzygies: BTreeSet<Signature<O, I, P>>,
}

/// Hold together the structures that must be coherent during the algorithm execution
struct BasisCalculator<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// The basis elements and syzygies.
    basis: KnownBasis<O, I, C, P>,

    /// Priority queue of the S-pairs pending to be processed.
    /// Elements are represent as pair of indices in "basis" Vec.
    spairs: s_pairs::SPairTriangle<O, I, P>,

    /// Basis ordered by signature to leading monomial ratio.
    ///
    /// TODO: to search for a reducer, maybe this should be a 2-D index (like
    /// R*-tree), indexing both the leading monomial and the signature/leading
    /// monomial ratio.
    by_sign_lm_ratio: BTreeMap<PointedCmp<Signature<O, I, P>>, *const SignPoly<O, I, C, P>>,
}

impl<
        O: Ordering,
        I: Id + Display,
        C: InvertibleCoefficient + Display,
        P: SignedPower + Display,
    > BasisCalculator<O, I, C, P>
{
    fn new() -> Self {
        BasisCalculator {
            basis: KnownBasis {
                polys: Vec::new(),
                syzygies: BTreeSet::new(),
            },
            spairs: s_pairs::SPairTriangle::new(),
            by_sign_lm_ratio: BTreeMap::new(),
        }
    }

    /// Adds a new polynomial to the Gröbner Basis and calculates its S-pairs.
    fn insert_poly_with_spairs(&mut self, sign_poly: SignPoly<O, I, C, P>) {
        let rc = Box::new(sign_poly);

        self.spairs.add_column(rc.as_ref(), &self.basis);
        self.by_sign_lm_ratio
            .insert(PointedCmp(&rc.sign_to_lm_ratio), rc.as_ref());

        self.basis.polys.push(rc);
    }

    fn next_spair(&mut self) -> Option<(Signature<O, I, P>, Polynomial<O, I, C, P>)> {
        self.spairs.get_next(&self.basis)
    }

    fn find_a_regular_reducer(
        &self,
        ratio: &Signature<O, I, P>,
        term: &Term<O, I, C, P>,
    ) -> Option<&SignPoly<O, I, C, P>> {
        // Filter out the unsuitable ratios:
        let suitable = self.by_sign_lm_ratio.range(..=PointedCmp(ratio));

        // Search all the suitable range for a divisor of term.
        for (_, elem) in suitable {
            let next = unsafe { &**elem };

            if next.polynomial.terms[0].monomial.divides(&term.monomial) {
                return Some(next);
            }
        }

        None
    }

    fn add_syzygy_signature(&mut self, signature: Signature<O, I, P>) {
        self.basis.syzygies.insert(signature);
    }
}

/// The 3 possible results of a regular reduction.
enum RegularReductionResult<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// Polynomial was singular top reducible
    Singular,
    /// Polynomial was reduced to zero.
    Zero(Signature<O, I, P>),
    /// Polynomial was reduced to some non-zero constant.
    NonZeroConstant(Polynomial<O, I, C, P>),
    /// Polynomial was reduced to some non singular top reducible polynomial.
    Reduced(SignPoly<O, I, C, P>),
}

/// Regular reduction, as defined in the paper.
///
/// This is analogous to calculate the remainder on a multivariate polynomial
/// division, but with extra restrictions on what polynomials can be the divisor
/// according to their signature.
fn regular_reduce<
    O: Ordering,
    I: Id + Display,
    C: InvertibleCoefficient + Display,
    P: SignedPower + Display,
>(
    signature: Signature<O, I, P>,
    polynomial: Polynomial<O, I, C, P>,
    basis: &BasisCalculator<O, I, C, P>,
) -> RegularReductionResult<O, I, C, P> {
    // The paper suggests splitting the reduced polynomial into a hash map of
    // monomial -> coefficient, so that we can efficiently sum the new terms,
    // and a priority queue, so that we know what is the next monomial to be
    // reduced. Tests have shown that this is actually better than simply using
    // a BTreeMap.

    let (mut to_reduce, mut remaining_terms): (
        BinaryHeap<Box<Monomial<O, I, P>>>,
        HashMap<PointedCmp<Monomial<O, I, P>>, C>,
    ) = polynomial
        .terms
        .into_iter()
        .map(|e| {
            let monomial = Box::new(e.monomial);
            let pointed = PointedCmp(monomial.as_ref());
            (monomial, (pointed, e.coefficient))
        })
        .unzip();

    // Reduce one term at a time.
    let mut reduced_terms = Vec::new();
    let mut sign_to_lm_ratio = None;
    while let Some(m) = to_reduce.pop() {
        let coefficient = if let Some(coefficient) = remaining_terms.remove(&PointedCmp(m.as_ref()))
        {
            coefficient
        } else {
            // The entry was removed due to summing to zero:
            continue;
        };

        // Reassemble the term
        let term = Term {
            coefficient,
            monomial: Box::<Monomial<O, I, P>>::into_inner(m),
        };

        // Skip searching for a divisor for 1 and (maybe) save some time.
        if term.monomial.is_one() {
            reduced_terms.push(term);
            break;
        }

        // Calculate signature to monomial ratio, to search for a reducer,
        // and possibly store it as the ratio for the leading term.
        let sign_to_term_ratio = sign_to_monomial_ratio(&signature, &term.monomial);

        if let Some(reducer) = basis.find_a_regular_reducer(&sign_to_term_ratio, &term) {
            // Since the reduction is singular, we can stop if we are
            // reducing the leading term.
            if reduced_terms.is_empty() && reducer.signature == signature {
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
                .elimination_factor(&leading_term.coefficient.clone().inv());

            let factor = Term {
                coefficient,
                monomial,
            };

            // Subtract every element of the reducer from the rest of the
            // polynomial.
            for term in iter {
                use std::collections::hash_map::Entry;

                let reducer_term = factor.clone() * term.clone();
                let new_monomial = Box::new(reducer_term.monomial);

                match remaining_terms.entry(PointedCmp(new_monomial.as_ref())) {
                    Entry::Vacant(entry) => {
                        // There was no such monomial, just insert:
                        to_reduce.push(new_monomial);
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
        if let None = sign_to_lm_ratio {
            assert!(reduced_terms.len() == 0);
            sign_to_lm_ratio = Some(sign_to_term_ratio);
        }

        // And insert it into the output. These terms are already in
        // decreasing order.
        reduced_terms.push(term)
    }

    let polynomial = Polynomial {
        terms: reduced_terms,
    };

    match sign_to_lm_ratio {
        Some(sign_to_lm_ratio) => RegularReductionResult::Reduced(SignPoly {
            signature,
            polynomial,
            sign_to_lm_ratio,
        }),
        None => {
            // The only way for sign_to_lm_ratio to be None is when
            // reduced_terms is empty or constant.
            match polynomial.terms.len() {
                0 => RegularReductionResult::Zero(signature),
                1 => {
                    assert!(polynomial.is_constant());
                    RegularReductionResult::NonZeroConstant(polynomial)
                }
                _ => panic!("This should never happen!"),
            }
        }
    }
}

/// Calculates the Grobner Basis using the Signature Buchberger (SB) algorithm.
pub fn grobner_basis<
    O: Ordering,
    I: Id + Display,
    C: InvertibleCoefficient + Display,
    P: SignedPower + Display,
>(
    input: &mut dyn Iterator<Item = Polynomial<O, I, C, P>>,
) -> Vec<Polynomial<O, I, C, P>> {
    // The algorithm performance might depend on the order the
    // elements are given in the input.

    let mut c = BasisCalculator::new();

    // Insert all input polynomials in the basis.
    // From my tests with a single input, sorting makes it run much faster.
    for polynomial in input.sorted() {
        if polynomial.is_zero() {
            // Zero polynomial is implicitly part of every ideal, so it is
            // redundant.
            continue;
        }

        if polynomial.is_constant() {
            // Constant polynomial means the ideal is the full set of all
            // polynomials, for which any constant polynomial is a generator, so
            // we can stop.
            return vec![polynomial];
        }

        let signature = Signature {
            idx: c.basis.polys.len() as u32,
            monomial: Monomial::one(),
        };
        c.insert_poly_with_spairs(SignPoly::new(signature, polynomial));
    }

    // Main loop, reduce every S-pair and insert in the basis until there are no
    // more S-pairs to be reduced. Since each newly inserted polynomials can
    // generate up to n-1 new S-pairs, this loop is exponential.
    while let Some((signature, polynomial)) = c.next_spair() {
        match regular_reduce(signature, polynomial, &c) {
            RegularReductionResult::Reduced(reduced) => {
                println!(
                    "#(p: {}, s: {}), {}",
                    c.basis.polys.len(),
                    c.basis.syzygies.len(),
                    reduced
                );

                // Polynomial is a new valid member of the basis. Insert it into
                // the basis.
                c.insert_poly_with_spairs(reduced);
            }
            RegularReductionResult::Zero(signature) => {
                // Polynomial reduces to zero, so we keep the signature to
                // eliminate S-pairs before reduction.
                c.add_syzygy_signature(signature);
            }
            RegularReductionResult::Singular => (
                // Polynomial was singular top reducible, so it was redundant
                // and discarded.
            ),
            RegularReductionResult::NonZeroConstant(polynomial) => {
                // The new basis member is a constant, so it reduces everything
                // to zero and we can stop.
                return vec![polynomial];
            }
        }
    }

    // Take the polynomials from the basis and return and autoreduce them, so
    // that we have a Reduced Gröbner Basis, which is unique.
    let gb = c
        .basis
        .polys
        .into_iter()
        .map(|sign_poly| sign_poly.polynomial)
        .collect();

    //println!("Gröbner basis computed, reducing...");
    //super::grobner_basis::autoreduce(gb)
    gb
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

        let grobner_basis = grobner_basis(&mut eqs.into_iter());
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
