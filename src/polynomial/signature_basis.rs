//! Implementation of SB algorithm as defined in
//! "Practical Gröbner basis computation"
//! by Bjarke Hammersholt Roune and Michael Stillman
//! http://www.broune.com/papers/issac2012.html

use std::collections::BTreeMap;

use super::division::InvertibleCoefficient;
use super::{monomial_ordering::Ordering, Id, Monomial, Polynomial, Power, Term};
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

/// Calculates signature to term ratio.
///
/// By allowing negative exponents, we can calculate the ratio between
/// a signature and a monomial, which is useful for comparison.
fn sign_to_monomial_ratio<O: Ordering, I: Id, P: SignedPower>(
    mut signature: Signature<O, I, P>,
    monomial: &Monomial<O, I, P>,
) -> Signature<O, I, P> {
    signature.monomial = signature.monomial.fraction_division(monomial);
    signature
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

impl<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> SignPoly<O, I, C, P> {
    /// Creates a new Signature Polynomial.
    ///
    /// Polynomial can not be zero, otherwise this will panic.
    fn new(signature: Signature<O, I, P>, polynomial: Polynomial<O, I, C, P>) -> Self {
        let sign_to_lm_ratio =
            sign_to_monomial_ratio(signature.clone(), &polynomial.terms[0].monomial);

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

/// S-pairs data structures.
mod s_pairs {
    use std::collections::BinaryHeap;

    use crate::{
        ordered_ops::partial_sum,
        polynomial::{
            division::InvertibleCoefficient, monomial_ordering::Ordering, Id, Polynomial, Term,
        },
    };

    use super::{SignPoly, Signature, SignedPower};

    /// Half S-pair
    ///
    /// This contains only what is needed to classify the S-pair (the signature), and
    /// the index of the other polynomial needed to build the full S-pair.
    struct HalfSPair<O: Ordering, I: Id, P: SignedPower> {
        signature: Signature<O, I, P>,
        idx: u32,
    }

    impl<O: Ordering, I: Id, P: SignedPower> HalfSPair<O, I, P> {
        /// Creates a new S-pair, if not eliminated by early elimination criteria.
        fn new_if_not_eliminated<C: InvertibleCoefficient>(
            sign_poly: &SignPoly<O, I, C, P>,
            idx: u32,
            basis: &[SignPoly<O, I, C, P>],
        ) -> Option<Self> {
            let other = &basis[idx as usize];

            // Find what polynomial to calculate the signature from.
            // It is the one with highest signature to LM ratio.
            let (sign_base, sign_other) = match sign_poly.sign_to_lm_ratio_cmp(&other) {
                std::cmp::Ordering::Equal => {
                    // Non-regular criterion: if the signature from both
                    // polynomials are the same, this S-pair is singular and can
                    // be eliminated immediately.
                    return None;
                }
                std::cmp::Ordering::Less => {
                    // TODO: implement here high-ratio base divisor criterion
                    (other, sign_poly)
                }
                std::cmp::Ordering::Greater => {
                    // TODO: implement here low-ratio base divisor criterion
                    (sign_poly, other)
                }
            };

            // Calculate the S-pair signature.
            let signature = HalfSPair::calculate_signature(sign_base, sign_other);

            // TODO: implement here signature criterion

            Some(HalfSPair { signature, idx })
        }

        /// Creates a new S-pair without checking any elimination criteria.
        fn new_unconditionally<C: InvertibleCoefficient>(
            sign_poly: &SignPoly<O, I, C, P>,
            idx: u32,
            basis: &[SignPoly<O, I, C, P>],
        ) -> Self {
            let other = &basis[idx as usize];

            // Find what polynomial to calculate the signature from.
            // It is the one with highest signature to LM ratio.
            let (sign_base, sign_other) = match sign_poly.sign_to_lm_ratio_cmp(&other) {
                std::cmp::Ordering::Less => (other, sign_poly),
                _ => (sign_poly, other),
            };

            HalfSPair {
                signature: HalfSPair::calculate_signature(sign_base, sign_other),
                idx,
            }
        }

        /// Calculate the S-pair signature.
        fn calculate_signature<C: InvertibleCoefficient>(
            base: &SignPoly<O, I, C, P>,
            other: &SignPoly<O, I, C, P>,
        ) -> Signature<O, I, P> {
            let monomial = base.signature.monomial.clone()
                * other.polynomial.terms[0]
                    .monomial
                    .div_by_gcd(&base.polynomial.terms[0].monomial);

            Signature {
                monomial,
                ..base.signature
            }
        }
    }

    /// Elements of the SPairTriangle, ordered by head_spair signature.
    struct SPairColumn<O: Ordering, I: Id, P: SignedPower> {
        head_spair: HalfSPair<O, I, P>,

        /// The index of the polynomial S-pairing with the others in the colum.
        origin_idx: u32,

        /// Index of polynomials ordered by descending signature of the S-pair with origin_idx.
        ///
        /// After head_spair is consumed, an element is popped from this vec to build the next
        /// spair_head with origin_idx.
        column: Vec<u32>,
    }

    impl<O: Ordering, I: Id, P: SignedPower> PartialEq for SPairColumn<O, I, P> {
        fn eq(&self, other: &Self) -> bool {
            self.head_spair.signature.eq(&other.head_spair.signature)
        }
    }

    impl<O: Ordering, I: Id, P: SignedPower> Eq for SPairColumn<O, I, P> {}

    impl<O: Ordering, I: Id, P: SignedPower> PartialOrd for SPairColumn<O, I, P> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(&other))
        }
    }

    impl<O: Ordering, I: Id, P: SignedPower> Ord for SPairColumn<O, I, P> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            // The elements are ordered in descending order so that
            // the binary heap will return the smallest element.
            other.head_spair.signature.cmp(&self.head_spair.signature)
        }
    }

    /// S-Pair where only the leading term has been evaluated.
    struct PartialSPair<'a, O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
        leading_term: Term<O, I, C, P>,
        iter_p: Box<(dyn Iterator<Item = Term<O, I, C, P>> + 'a)>,
        iter_q: Box<(dyn Iterator<Item = Term<O, I, C, P>> + 'a)>,
    }

    impl<'a, O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower>
        From<PartialSPair<'a, O, I, C, P>> for Polynomial<O, I, C, P>
    {
        /// Complete the calculation of PartialSPair into a SigPoly
        fn from(spair: PartialSPair<O, I, C, P>) -> Self {
            let mut terms = vec![spair.leading_term];
            Self::sum_terms(spair.iter_p, spair.iter_q, &mut terms);
            Self { terms }
        }
    }

    impl<'a, O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower>
        PartialSPair<'a, O, I, C, P>
    {
        /// Creates a partial S-pair with a leading term plus enough information
        /// to finish the computation. Performs relativelly prime elimination
        /// criterion, and return None if the S-pair was either eliminated or
        /// turns out to evaluate to zero.
        fn new_if_not_eliminated(
            p: &'a SignPoly<O, I, C, P>,
            q: &'a SignPoly<O, I, C, P>,
        ) -> Option<Self> {
            // Helper function used to calculate the complement of each polynomial
            let complement = |a: &Term<O, I, C, P>, b: &Term<O, I, C, P>| Term {
                monomial: a.monomial.div_by_gcd(&b.monomial),
                // Each complement has the coefficient of the other polynomial, so that
                // when multiplied, they end up with the same value.
                coefficient: a.coefficient.clone(),
            };

            let mut iter_p = p.polynomial.terms.iter();
            let ini_p = iter_p.next()?;

            let mut iter_q = q.polynomial.terms.iter();
            let ini_q = iter_q.next()?;

            // Relativelly prime criterion: if leading monomials are relativelly
            // prime, the S-pair will reduce to zero.
            if !ini_p.monomial.has_shared_variables(&ini_q.monomial) {
                return None;
            }

            let p_complement = complement(ini_q, ini_p);
            let mut q_complement = complement(ini_p, ini_q);

            // q_complement's coefficient must be the opposite, so the sum would
            // eliminate the first term:
            q_complement.coefficient = {
                let mut neg = C::zero();
                neg -= q_complement.coefficient;
                neg
            };

            let mut iter_p = Box::new(
                iter_p
                    .map(move |x| p_complement.clone() * x.clone())
                    .peekable(),
            );
            let mut iter_q = Box::new(
                iter_q
                    .map(move |x| q_complement.clone() * x.clone())
                    .peekable(),
            );

            let leading_term = partial_sum(
                &mut iter_p,
                &mut iter_q,
                |a, b| b.monomial.cmp(&a.monomial),
                |mut a, b| {
                    a.coefficient += b.coefficient;
                    if a.coefficient.is_zero() {
                        None
                    } else {
                        Some(a)
                    }
                },
            )?;

            Some(PartialSPair {
                leading_term,
                iter_p,
                iter_q,
            })
        }
    }

    /// Efficient priority queue to store S-pairs.
    ///
    /// Data structure defined in the paper to efficiently store and quickly
    /// retrieve the S-pair with minimal signature. This is basically a
    /// heap of ordered vectors.
    pub struct SPairTriangle<O: Ordering, I: Id, P: SignedPower> {
        // TODO: test if storing Box<SPairColumn> improves performance
        heads: BinaryHeap<SPairColumn<O, I, P>>,
    }

    impl<O: Ordering, I: Id, P: SignedPower> SPairTriangle<O, I, P> {
        pub fn new() -> Self {
            SPairTriangle {
                heads: BinaryHeap::new(),
            }
        }

        pub fn add_column<C: InvertibleCoefficient>(
            &mut self,
            sign_poly: &SignPoly<O, I, C, P>,
            basis: &[SignPoly<O, I, C, P>],
        ) {
            let mut new_spairs: Vec<_> = basis
                .iter()
                .enumerate()
                .filter_map(|(idx, _)| {
                    HalfSPair::new_if_not_eliminated(sign_poly, idx as u32, basis)
                })
                .collect();

            // Sort by signature in decreasing order, so we can pop the next element from the tail.
            new_spairs.sort_unstable_by(|a, b| b.signature.cmp(&a.signature));

            if let Some(head_spair) = new_spairs.pop() {
                let column: Vec<u32> = new_spairs.into_iter().map(|spair| spair.idx).collect();
                let origin_idx = basis.len() as u32;

                self.heads.push(SPairColumn {
                    head_spair,
                    column,
                    origin_idx,
                });
            }
        }

        /// Extract the one of the S-pairs with minimal signature. There can be multiple.
        fn pop<'a, C: InvertibleCoefficient>(
            &mut self,
            basis: &'a [SignPoly<O, I, C, P>],
        ) -> Option<(
            Signature<O, I, P>,
            &'a SignPoly<O, I, C, P>,
            &'a SignPoly<O, I, C, P>,
        )> {
            // Get the S-pair at the head of the column
            let mut head = self.heads.pop()?;
            let ret = head.head_spair;
            let a_poly = &basis[head.origin_idx as usize];
            let b_poly = &basis[ret.idx as usize];

            // Update the column's head and insert it back into the heap
            if let Some(next_head_idx) = head.column.pop() {
                head.head_spair = HalfSPair::new_unconditionally(a_poly, next_head_idx, basis);
                self.heads.push(head);
            }

            Some((ret.signature, a_poly, b_poly))
        }

        /// Return the next S-pair to be reduced, which is the S-pair of minimal
        /// signature. Or None if there are no more S-pairs.
        pub fn get_next<C: InvertibleCoefficient>(
            &mut self,
            basis: &[SignPoly<O, I, C, P>],
        ) -> Option<(Signature<O, I, P>, Polynomial<O, I, C, P>)> {
            // Iterate until some S-pair remains that is not eliminated by one
            // of the late elimination criteria.
            while let Some((signature, a_poly, b_poly)) = self.pop(basis) {
                let mut chosen_spair = PartialSPair::new_if_not_eliminated(a_poly, b_poly);

                // Duplicate signature criterion: only one of all S-pairs of the
                // same signature must be chosen, the one with the smallest
                // leading monomial.
                while let Some(head) = self.heads.peek() {
                    if head.head_spair.signature != signature {
                        break;
                    }

                    let (_, a_poly, b_poly) = self.pop(basis).unwrap();

                    // Only process the new S-pair if no other of same signature has been eliminated.
                    if let Some(spair) = &mut chosen_spair {
                        match PartialSPair::new_if_not_eliminated(a_poly, b_poly) {
                            Some(new_spair) => {
                                // There is a non-eliminated new S-pair,
                                // replace the chosen one if it has a smaller
                                // signature.
                                if new_spair.leading_term.monomial < spair.leading_term.monomial {
                                    *spair = new_spair;
                                }
                            }
                            None => {
                                // The new S-pair was eliminated, so every
                                // S-pair of same signature can be eliminated
                                // as well.
                                chosen_spair = None;
                            }
                        }
                    }
                }

                // All S-pairs of this signature have been consumed, and there
                // is at most one remaining.
                let spair = match chosen_spair {
                    Some(spair) => spair,
                    None => {
                        // The current S-pair has been eliminated.
                        // Try another one.
                        continue;
                    }
                };

                // TODO: perform all these elimination criteria:
                // - late signature criterion
                // - Koszul criterion
                // not sure if here or before calculating all these lading terms.

                // TODO: perform singular criterion elimination.

                return Some((signature, spair.into()));
            }
            None
        }
    }
}

/// Hold together the structures that must be coherent during the algorithm execution
struct BasisCalculator<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    basis: Vec<SignPoly<O, I, C, P>>,
    spairs: s_pairs::SPairTriangle<O, I, P>,
}

/// Result from searching for a regular reducer.
enum ReducerSearchResult<'a, O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// A regular reducer was found, it is the returned monomial multiplied by
    /// the returned polynomial.
    Some(Monomial<O, I, P>, &'a SignPoly<O, I, C, P>),
    /// A reducer of same signature was found, so the reduction can be skipped
    Singular,
    /// No reducer could be found, so the term is reduced.
    None,
}

impl<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> BasisCalculator<O, I, C, P> {
    fn new() -> Self {
        BasisCalculator {
            basis: Vec::new(),
            spairs: s_pairs::SPairTriangle::new(),
        }
    }

    /// Adds a new polynomial to the Gröbner Basis and calculates its S-pairs.
    fn insert_poly_with_spairs(&mut self, sign_poly: SignPoly<O, I, C, P>) {
        self.spairs.add_column(&sign_poly, &self.basis);
        self.basis.push(sign_poly);
    }

    fn next_spair(&mut self) -> Option<(Signature<O, I, P>, Polynomial<O, I, C, P>)> {
        self.spairs.get_next(&self.basis)
    }

    fn find_a_regular_reducer(
        &self,
        ratio: &Signature<O, I, P>,
        term: &Term<O, I, C, P>,
    ) -> ReducerSearchResult<O, I, C, P> {
        // TODO: to be continued...
        todo!()
    }

    fn add_syzygy_signature(&mut self, signature: Signature<O, I, P>) {
        // TODO: to be continued...
        todo!()
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
fn regular_reduce<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower>(
    signature: Signature<O, I, P>,
    polynomial: Polynomial<O, I, C, P>,
    basis: &BasisCalculator<O, I, C, P>,
) -> RegularReductionResult<O, I, C, P> {
    // The paper suggests splitting the reduced polynomial into a hash map of
    // monomial -> coefficient, so that we can efficiently sum the new terms,
    // and a priority queue, so that we know what is the next monomial to be
    // reduced. We can do both with a single BTreeMap, which is ordered and has
    // fast map access. For now, I will use a BTreeMap, which I suspect to be
    // good enough.
    //
    // TODO: compare with the paper's solution

    // The tree with the terms to be reduced.
    let mut to_reduce: BTreeMap<Monomial<O, I, P>, C> = polynomial
        .terms
        .into_iter()
        // Since this is already reverse sorted, rev() is a little faster, as we
        // insert the elements in increasing order.
        .rev()
        .map(|term| (term.monomial, term.coefficient))
        .collect();

    // Reduce one term at a time.
    let mut reduced_terms = Vec::new();
    let mut sign_to_lm_ratio = None;
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

        // Calculate signature to monomial ratio, to search for a reducer,
        // and possibly store it as the ratio for the leading term.
        let sign_to_term_ratio = sign_to_monomial_ratio(signature.clone(), &term.monomial);

        match basis.find_a_regular_reducer(&sign_to_term_ratio, &term) {
            ReducerSearchResult::Some(monomial, reducer) => {
                let mut iter = reducer.polynomial.terms.iter();

                // Calculate the multiplier coefficient using the reducer leading term:
                let coefficient = term
                    .coefficient
                    .elimination_factor(&iter.next().unwrap().coefficient.clone().inv());

                let factor = Term {
                    coefficient,
                    monomial,
                };

                // Subtract every element of the reducer from the rest of the
                // polynomial.
                for term in iter {
                    let reducer_term = factor.clone() * term.clone();

                    match to_reduce.entry(reducer_term.monomial) {
                        std::collections::btree_map::Entry::Vacant(entry) => {
                            // There was no such monomial, just insert:
                            entry.insert(reducer_term.coefficient);
                        }
                        std::collections::btree_map::Entry::Occupied(mut entry) => {
                            // Sum the coefficients, and remove if result is zero.
                            *entry.get_mut() += reducer_term.coefficient;
                            if entry.get().is_zero() {
                                entry.remove_entry();
                            }
                        }
                    }
                }

                // Don't insert any new term in the final polynomial
                continue;
            }
            ReducerSearchResult::Singular => {
                // Since the reduction is singular, we can stop if we are
                // reducing the leading term.
                if reduced_terms.is_empty() {
                    return RegularReductionResult::Singular;
                }
                // otherwise this simply fall through as it can't be reduced.

                // TODO: Really can't? It seems to me signature stuff can be
                // ignored if we are not reducing the leading term. Eventually
                // we should experiment with only considering signatures with
                // the leading term.
            }
            ReducerSearchResult::None => (
                // No reducer was found.
            ),
        }

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
pub fn grobner_basis<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower>(
    input: &mut dyn Iterator<Item = Polynomial<O, I, C, P>>,
) -> Vec<Polynomial<O, I, C, P>> {
    // The algorithm performance might depend on the order the
    // elements are given in the input.
    //
    // TODO: if there is a way to reorder the input so that it
    // runs faster, this is the place.

    let mut c = BasisCalculator::new();

    // Insert all input polynomials in the basis
    for polynomial in input {
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
            idx: c.basis.len() as u32,
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

    // Take the polynomials from the basis and return.
    //
    // TODO: maybe autoreduce this basis so that we have a Reduced Gröbner
    // Basis, which is unique.
    c.basis
        .into_iter()
        .map(|sign_poly| sign_poly.polynomial)
        .collect()
}
