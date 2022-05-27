//! Implementation of SB algorithm as defined in
//! "Practical Gröbner basis computation"
//! by Bjarke Hammersholt Roune and Michael Stillman
//! http://www.broune.com/papers/issac2012.html

use super::{monomial_ordering::Ordering, Coefficient, Id, Monomial, Polynomial, Power};
use num_traits::{One, Signed};

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
struct Signature<O: Ordering, I: Id, P: SignedPower> {
    idx: u32,
    monomial: Monomial<O, I, P>,
}

/// Signature polynomial.
///
/// In the paper, the SB algorithm is described in terms of elements of a
/// polynomial module, but it turns out that representing this element as a
/// pair (signature, polynomial) is sufficient for all the computations.
/// Other fields are optimizations.
struct SigPoly<O: Ordering, I: Id, C: Coefficient, P: SignedPower> {
    signature: Signature<O, I, P>,
    polynomial: Polynomial<O, I, C, P>,

    /// The signature to leading monomial ratio allows us to quickly
    /// find out what is the signature of a new S-pair calculated.
    ///
    /// TODO: there is an optimization where every such ratio is
    /// assigned an integer, thus can be compared in one instruction.
    sign_to_lm_ratio: Signature<O, I, P>,
}

impl<O: Ordering, I: Id, C: Coefficient, P: SignedPower> SigPoly<O, I, C, P> {
    /// Creates a new Signature Polynomial.
    ///
    /// Polynomial can not be zero, otherwise this will panic.
    fn new(signature: Signature<O, I, P>, polynomial: Polynomial<O, I, C, P>) -> Self {
        let sig_to_lead_term_ratio = Signature {
            idx: signature.idx.clone(),
            monomial: signature
                .monomial
                .clone()
                .fraction_division(&polynomial.get_terms()[0].get_monomial()),
        };

        Self {
            signature,
            polynomial,
            sign_to_lm_ratio: sig_to_lead_term_ratio,
        }
    }
}

/// Regular reduction, as defined in the paper.
///
/// This is analogous to calculate the remainder on a multivariate polynomial
/// division, but with extra restrictions on what polynomials can be the divisor
/// according to their signature.
fn regular_reduce<O: Ordering, I: Id, C: Coefficient, P: SignedPower>(
    reduced: SigPoly<O, I, C, P>,
    reducer: Vec<SigPoly<O, I, C, P>>,
) {
}

/// S-pairs data structures.
mod s_pairs {
    use std::collections::BinaryHeap;

    use crate::polynomial::{monomial_ordering::Ordering, Coefficient, Id, Monomial};

    use super::{SigPoly, Signature, SignedPower};

    /// Partial S-pair
    ///
    /// This contains everything needed build and classify an S-pair, without
    /// carrying out the full computation.
    struct SPair<O: Ordering, I: Id, P: SignedPower> {
        signature: Signature<O, I, P>,
        //leading_monomial: Monomial<O, I, P>,
        idx: u32,
    }

    impl<O: Ordering, I: Id, P: SignedPower> SPair<O, I, P> {
        /// Creates a new S-pair, if not eliminated by early elimination criteria.
        fn new_if_viable<C: Coefficient>(
            sig_poly: &SigPoly<O, I, C, P>,
            idx: u32,
            basis: &[SigPoly<O, I, C, P>],
        ) -> Option<Self> {
            let other = &basis[idx as usize];

            // Find what polynomial to calculate the signature from.
            // It is the one with highest signature to LM ratio.
            let (sign_base, sign_other) =
                match sig_poly.sign_to_lm_ratio.cmp(&other.sign_to_lm_ratio) {
                    std::cmp::Ordering::Equal => {
                        // Non-regular criterion: if the signature from both
                        // polynomials are the same, this S-pair is singular and can
                        // be eliminated immediately.
                        return None;
                    }
                    std::cmp::Ordering::Less => {
                        // TODO: implement here high-ratio base divisor criterion
                        (other, sig_poly)
                    }
                    std::cmp::Ordering::Greater => {
                        // TODO: implement here low-ratio base divisor criterion
                        (sig_poly, other)
                    }
                };

            // Calculate the S-pair signature.
            let monomial = sign_base.signature.monomial.clone()
                * sign_other.polynomial.terms[0]
                    .monomial
                    .div_by_gcd(&sign_base.polynomial.terms[0].monomial);

            // TODO: implement here signature criterion

            let signature = Signature {
                monomial,
                ..sign_base.signature
            };

            Some(SPair { signature, idx })
        }
    }

    /// Elements of the SPairTriangle, ordered by head_spair signature.
    struct SPairColumn<O: Ordering, I: Id, P: SignedPower> {
        head_spair: SPair<O, I, P>,

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

    /// Efficient priority queue to store S-pairs.
    ///
    /// Data structure defined in the paper to efficiently store and quickly
    /// retrieve the S-pair with minimal signature. This is basically a
    /// heap of ordered vectors.
    pub struct SPairTriangle<O: Ordering, I: Id, P: SignedPower> {
        heads: BinaryHeap<SPairColumn<O, I, P>>,
    }

    impl<O: Ordering, I: Id, P: SignedPower> SPairTriangle<O, I, P> {
        pub fn new() -> Self {
            SPairTriangle {
                heads: BinaryHeap::new(),
            }
        }

        pub fn add_column<C: Coefficient>(
            &mut self,
            sig_poly: &SigPoly<O, I, C, P>,
            basis: &[SigPoly<O, I, C, P>],
        ) {
            let mut new_spairs: Vec<_> = basis
                .iter()
                .enumerate()
                .filter_map(|(idx, poly)| SPair::new_if_viable(sig_poly, idx as u32, basis))
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
    }
}

/// Hold together the structures that must be coherent during the algorithm execution
struct BasisCalculator<O: Ordering, I: Id, C: Coefficient, P: SignedPower> {
    basis: Vec<SigPoly<O, I, C, P>>,
    spairs: s_pairs::SPairTriangle<O, I, P>,
}

impl<O: Ordering, I: Id, C: Coefficient, P: SignedPower> BasisCalculator<O, I, C, P> {
    fn new() -> Self {
        BasisCalculator {
            basis: Vec::new(),
            spairs: s_pairs::SPairTriangle::new(),
        }
    }

    /// Adds a new polynomial to the Gröbner Basis
    fn insert_poly(&mut self, sig_poly: SigPoly<O, I, C, P>) {
        self.spairs.add_column(&sig_poly, &self.basis);
        self.basis.push(sig_poly);
    }
}

/// Calculates the Grobner Basis using the Signature Buchberger (SB) algorithm.
pub fn grobner_basis<O: Ordering, I: Id, C: Coefficient, P: SignedPower>(
    input: &mut dyn Iterator<Item = Polynomial<O, I, C, P>>,
) -> Vec<Polynomial<O, I, C, P>> {
    // The algorithm performance might depend on the order the
    // elements are given in the input.

    // TODO: if there is a way to reorder the input so that it
    // runs faster, this is the place.

    let mut c = BasisCalculator::new();

    for polynomial in input {
        let idx = c.basis.len() as u32;
        let signature = Signature {
            idx,
            monomial: Monomial::one(),
        };

        c.insert_poly(SigPoly::new(signature, polynomial));
    }

    // TODO: to be continued
    Vec::new()
}