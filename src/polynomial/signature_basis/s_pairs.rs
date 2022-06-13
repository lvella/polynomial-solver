
//! S-pairs data structures.

use std::{collections::BinaryHeap, fmt::Display};

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
        basis: &[Box<SignPoly<O, I, C, P>>],
    ) -> Option<Self> {
        let other = basis[idx as usize].as_ref();

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
        basis: &[Box<SignPoly<O, I, C, P>>],
    ) -> Self {
        let other = basis[idx as usize].as_ref();

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

impl<O: Ordering, I: Id + Display, P: SignedPower + Display> SPairTriangle<O, I, P> {
    pub fn new() -> Self {
        SPairTriangle {
            heads: BinaryHeap::new(),
        }
    }

    pub fn add_column<C: InvertibleCoefficient>(
        &mut self,
        sign_poly: &SignPoly<O, I, C, P>,
        basis: &[Box<SignPoly<O, I, C, P>>],
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
        basis: &'a [Box<SignPoly<O, I, C, P>>],
    ) -> Option<(
        Signature<O, I, P>,
        &'a SignPoly<O, I, C, P>,
        &'a SignPoly<O, I, C, P>,
    )> {
        // Get the S-pair at the head of the column
        let mut head = self.heads.pop()?;
        let ret = head.head_spair;
        let a_poly = basis[head.origin_idx as usize].as_ref();
        let b_poly = basis[ret.idx as usize].as_ref();

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
        basis: &[Box<SignPoly<O, I, C, P>>],
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
                            // leading monomial.
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
