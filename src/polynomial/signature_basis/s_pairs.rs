//! S-pairs data structures.

use std::{
    cmp::max,
    collections::{BTreeMap, BinaryHeap},
    fmt::Display,
    marker::PhantomData,
    ops::{
        Bound::{Excluded, Unbounded},
        Index,
    },
};

use bitvec::prelude::BitVec;
use itertools::Itertools;

use crate::{
    ordered_ops::partial_sum,
    polynomial::{
        division::Field, monomial_ordering::Ordering, Id, Monomial, Polynomial, Term, VariablePower,
    },
};

use super::{
    basis_calculator::SyzygySet, contains_divisor, rewrite_spair, DivMask, KnownBasis,
    MaskedMonomialRef, MaskedSignature, PointedCmp, Ratio, SignPoly, Signature, SignedPower,
};

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
    ///
    /// On error, tells if S-pair is known to reduce to zero.
    fn new_if_not_eliminated<C: Field>(
        sign_poly: &SignPoly<O, I, C, P>,
        other: &SignPoly<O, I, C, P>,
        base_divisors: &BaseDivisors<O, I, C, P>,
        basis: &KnownBasis<O, I, C, P>,
        syzygies: &SyzygySet<O, I, P>,
        triangle: &SyzygyTriangle,
    ) -> Result<Self, bool> {
        // Find what polynomial to calculate the signature from.
        // It is the one with highest signature to LM ratio.
        let (sign_base, sign_other) = match sign_poly.sign_to_lm_ratio_cmp(&other) {
            std::cmp::Ordering::Equal => {
                // Non-regular criterion: if the signature from both polynomials
                // would be the same when each is multiplied by its
                // complementary factor, then this S-pair is singular and can be
                // eliminated immediately (I have no idea why, I don't know if
                // it is redundant or a syzygy or whatever).
                return Err(false);
            }
            std::cmp::Ordering::Less => {
                // Test for high-ratio base divisor criterion:
                if let Some(bd) = &base_divisors.high {
                    if bd.0.idx != other.idx
                        && triangle[(bd.0.idx, other.idx)]
                        && other.sign_to_lm_ratio > bd.0.sign_to_lm_ratio
                    {
                        return Err(true);
                    }
                }

                (other, sign_poly)
            }
            std::cmp::Ordering::Greater => {
                // Test for low-ratio base divisor criterion:
                if let Some(bd) = &base_divisors.low {
                    if bd.divisor.idx != other.idx
                        && triangle[(bd.divisor.idx, other.idx)]
                        && other.sign_to_lm_ratio < bd.divisor.sign_to_lm_ratio
                        && other.leading_monomial().divides(&bd.get_discriminator())
                    {
                        return Err(true);
                    }
                }

                (sign_poly, other)
            }
        };

        // Calculate the S-pair signature.
        let signature = HalfSPair::calculate_signature(sign_base, sign_other);
        let masked_signature = MaskedSignature {
            divmask: basis.div_map.map(&signature.monomial),
            signature,
        };

        // Early test for signature criterion:
        if contains_divisor(&masked_signature, syzygies) {
            return Err(true);
        } else {
            Ok(HalfSPair {
                signature: masked_signature.signature,
                idx: other.idx,
            })
        }
    }

    /// Creates a new S-pair without checking any elimination criteria.
    fn new_unconditionally<C: Field>(
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
    fn calculate_signature<C: Field>(
        base: &SignPoly<O, I, C, P>,
        other: &SignPoly<O, I, C, P>,
    ) -> Signature<O, I, P> {
        let monomial = base.signature().monomial.clone()
            * other.polynomial.terms[0]
                .monomial
                .div_by_gcd(&base.polynomial.terms[0].monomial);

        Signature {
            monomial,
            ..*base.signature()
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
pub struct PartialSPair<'a, O: Ordering, I: Id, C: Field, P: SignedPower> {
    pub leading_term: Term<O, I, C, P>,
    iter_p: Box<(dyn Iterator<Item = Term<O, I, C, P>> + 'a)>,
    iter_q: Box<(dyn Iterator<Item = Term<O, I, C, P>> + 'a)>,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedPower> From<PartialSPair<'a, O, I, C, P>>
    for Polynomial<O, I, C, P>
{
    /// Complete the calculation of PartialSPair into a SigPoly
    fn from(spair: PartialSPair<O, I, C, P>) -> Self {
        let mut terms = vec![spair.leading_term];
        Self::sum_terms(spair.iter_p, spair.iter_q, &mut terms);
        Self { terms }
    }
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedPower> PartialSPair<'a, O, I, C, P> {
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

/// Base divisors used in the base divisor criterion.
///
/// TODO: Test without this criterion again when a proper multidimensional index
/// have been implemented, because right now it makes things worse, not better.
struct BaseDivisors<'a, O: Ordering, I: Id, C: Field, P: SignedPower> {
    high: Option<HighBaseDivisor<'a, O, I, C, P>>,
    low: Option<LowBaseDivisor<'a, O, I, C, P>>,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedPower> BaseDivisors<'a, O, I, C, P> {
    fn new(sign_poly: &SignPoly<O, I, C, P>, basis: &KnownBasis<O, I, C, P>) -> Self {
        Self {
            high: HighBaseDivisor::new(sign_poly, basis),
            low: LowBaseDivisor::new(sign_poly, basis),
        }
    }
}

struct HighBaseDivisor<'a, O: Ordering, I: Id, C: Field, P: SignedPower>(&'a SignPoly<O, I, C, P>);

impl<'a, O: Ordering, I: Id, C: Field, P: SignedPower> HighBaseDivisor<'a, O, I, C, P> {
    fn new(sign_poly: &SignPoly<O, I, C, P>, basis: &KnownBasis<O, I, C, P>) -> Option<Self> {
        let lm = &sign_poly.leading_monomial();

        // Search for high base divisor only where sign/lm ratio is higher,
        // otherwise this polynomial would have been reduced or eliminated already.
        for (_, maybe_divisor) in basis
            .by_sign_lm_ratio
            .range((Excluded(PointedCmp(&sign_poly.sign_to_lm_ratio)), Unbounded))
        {
            let maybe_divisor = unsafe { &**maybe_divisor };
            if maybe_divisor.leading_monomial().divides(lm) {
                return Some(HighBaseDivisor(maybe_divisor));
            }
        }

        None
    }
}

/// An iterator aggregating multiple VariablePower iterators, assumed to be in
/// descending order of variable id.
///
/// Each element is a tuple (variable_id, vec_of_powers) for the power of
/// variable_id for each iterator. If some variable is not present in some
/// iterator, the value is set to zero. As long as a variable id is present in
/// at least one iterator, it will be output.
struct MultiVarWalk<'a, I: 'a + Id, P: 'a + SignedPower> {
    iters: Vec<&'a mut dyn Iterator<Item = &'a VariablePower<I, P>>>,
    current: Vec<Option<&'a VariablePower<I, P>>>,
    next_id: Option<I>,
}

impl<'a, I: 'a + Id, P: 'a + SignedPower> MultiVarWalk<'a, I, P> {
    fn new(mut iters: Vec<&'a mut dyn Iterator<Item = &'a VariablePower<I, P>>>) -> Self {
        let mut next_id = None;

        let current = iters
            .iter_mut()
            .map(|i| {
                let var = i.next();
                Self::update_next_id(&mut next_id, var);
                var
            })
            .collect();

        Self {
            iters,
            current,
            next_id,
        }
    }

    fn update_next_id(next_id: &mut Option<I>, var: Option<&VariablePower<I, P>>) {
        if let Some(var) = var {
            if let Some(id) = &next_id {
                if var.id > *id {
                    *next_id = Some(var.id.clone());
                }
            } else {
                *next_id = Some(var.id.clone());
            }
        }
    }
}

impl<'a, I: 'a + Id, P: 'a + SignedPower> Iterator for MultiVarWalk<'a, I, P> {
    type Item = (I, Vec<P>);

    fn next(&mut self) -> Option<Self::Item> {
        let id = self.next_id.as_ref()?.clone();
        let mut values = Vec::new();
        values.reserve(self.current.len());

        self.next_id = None;

        for (var, iter) in self.current.iter_mut().zip(self.iters.iter_mut()) {
            // Decide what value to use for this iter:
            values.push(if let Some(v) = var {
                if v.id == id {
                    let value = v.power.clone();
                    *var = iter.next();
                    value
                } else {
                    P::zero()
                }
            } else {
                P::zero()
            });

            // Choose the highest of the IDs for next id to be output:
            Self::update_next_id(&mut self.next_id, *var);
        }

        Some((id, values))
    }
}

/// Low base divisor information
struct LowBaseDivisor<'a, O: Ordering, I: Id, C: Field, P: SignedPower> {
    divisor: &'a SignPoly<O, I, C, P>,
    /// The x^v in the paper.
    discriminator: Monomial<O, I, P>,
    discriminator_mask: DivMask,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedPower> LowBaseDivisor<'a, O, I, C, P> {
    /// For low base divisor, find the polynomial with maximum sign/lm ratio
    /// whose signature divides sign_poly.
    fn new(sign_poly: &SignPoly<O, I, C, P>, basis: &KnownBasis<O, I, C, P>) -> Option<Self> {
        // Creates a monomial where all variables have maximum power. This
        // will be useful in querying the BTreeMap below, and will be the
        // basis of the discriminator.
        let max_monomial = Monomial {
            product: (0..basis.max_exp.len())
                .map(|idx| VariablePower {
                    id: I::from_idx(basis.max_exp.len() - 1 - idx),
                    power: P::max_value(),
                })
                .collect(),
            total_power: P::max_value(),
            _phantom_ordering: PhantomData,
        };

        let mut divisor = None;

        // Search for the divisor in the range where signatures have the
        // same idx, from maximum signature/lm ratio to minimum. We use the
        // fact that the stored sign/lm ratio has the same idx as the stored
        // signature.
        let range_max = Ratio::new(
            None,
            Signature {
                monomial: max_monomial,
                idx: sign_poly.signature().idx,
            },
        )
        .unwrap();

        let sign_monomial = sign_poly.masked_signature.monomial();
        for (_, maybe_divisor) in basis
            .by_sign_lm_ratio
            .range(..=PointedCmp(&range_max))
            .rev()
        {
            let maybe_divisor = unsafe { &**maybe_divisor };
            if maybe_divisor.signature().idx != sign_poly.signature().idx {
                // We are out of the possible divisor range.
                return None;
            }

            if maybe_divisor
                .masked_signature
                .monomial()
                .divides(&sign_monomial)
            {
                divisor = Some(maybe_divisor);
                break;
            }
        }

        let divisor = divisor?;

        // Calculate the discriminant:
        let a = &divisor.polynomial.terms[0].monomial;
        let b = &sign_poly.polynomial.terms[0].monomial;

        let p = sign_poly
            .signature()
            .monomial
            .clone()
            .whole_division(&divisor.signature().monomial)
            .unwrap()
            * a.clone();

        // Reuse the maximum monomial so we don't have to reallocate it.
        let mut v = range_max.into_inner().monomial;

        let mut ia = a.product.iter();
        let mut ib = b.product.iter();
        let mut ip = p.product.iter();

        let mut multivar_iter = MultiVarWalk::new(vec![&mut ia, &mut ib, &mut ip]);
        if let Some(mut multivar) = multivar_iter.next() {
            for var in v.product.iter_mut() {
                // b == p, so v is infinity (unchanged)
                if var.id != multivar.0 {
                    continue;
                }

                // We have a, b and p, do the comparison:
                let (a, b, p) = multivar.1.into_iter().next_tuple().unwrap();
                if b > p {
                    var.power = max(p, a);
                }

                multivar = match multivar_iter.next() {
                    Some(x) => x,
                    None => break,
                }
            }
        }

        Some(LowBaseDivisor {
            divisor,
            discriminator_mask: basis.div_map.map(&v),
            discriminator: v,
        })
    }

    fn get_discriminator(&self) -> MaskedMonomialRef<O, I, P> {
        MaskedMonomialRef(&self.discriminator_mask, &self.discriminator)
    }
}

/// Stores one bit for every S-pair ever generated, saying if it reduces to
/// zero. This is used in base divisor criterion.
///
/// TODO: there may be possible to use a single BitVec, but I didn't think long
/// and hard on how to do the indexing.
pub struct SyzygyTriangle(Vec<BitVec>);

impl SyzygyTriangle {
    fn new() -> Self {
        Self(Vec::new())
    }

    fn syzygy_triangle_idx(idx: (u32, u32)) -> (usize, usize) {
        if idx.0 < idx.1 {
            (idx.0 as usize, idx.1 as usize)
        } else {
            (idx.1 as usize, idx.0 as usize)
        }
    }

    fn set(&mut self, idx: (u32, u32), val: bool) {
        let (min, max) = Self::syzygy_triangle_idx(idx);
        self.0[max].set(min, val);
    }

    fn add_column(&mut self, column: BitVec) {
        self.0.push(column);
    }
}

impl Index<(u32, u32)> for SyzygyTriangle {
    type Output = <BitVec as Index<usize>>::Output;

    fn index(&self, idx: (u32, u32)) -> &Self::Output {
        let (min, max) = Self::syzygy_triangle_idx(idx);
        &self.0[max][min]
    }
}

/// Efficient priority queue to store S-pairs.
///
/// Data structure defined in the paper to efficiently store and quickly
/// retrieve the S-pair with minimal signature. This is basically a
/// heap of ordered vectors.
pub struct SPairTriangle<O: Ordering, I: Id, P: SignedPower> {
    /// Stores the S-pairs to be reduced.
    heads: BinaryHeap<SPairColumn<O, I, P>>,

    /// Tells if an S-pair is a syzygy.
    reduces_to_zero: SyzygyTriangle,
}

impl<O: Ordering, I: Id + Display, P: SignedPower + Display> SPairTriangle<O, I, P> {
    pub fn new() -> Self {
        SPairTriangle {
            heads: BinaryHeap::new(),
            reduces_to_zero: SyzygyTriangle::new(),
        }
    }

    pub fn add_column<C: Field>(
        &mut self,
        sign_poly: &SignPoly<O, I, C, P>,
        basis: &KnownBasis<O, I, C, P>,
        syzygies: &SyzygySet<O, I, P>,
    ) {
        // Base divisors are used in a elimination criterion. We must calculate
        // them beforehand as they are used in every S-pair added in this new
        // column.
        let base_divisors = BaseDivisors::new(sign_poly, basis);

        let mut new_spairs = Vec::new();
        let mut reduces_to_zero = BitVec::with_capacity(basis.polys.len());
        for other_poly in basis.polys.iter() {
            let red_to_zero = match HalfSPair::new_if_not_eliminated(
                sign_poly,
                other_poly.as_ref(),
                &base_divisors,
                basis,
                syzygies,
                &self.reduces_to_zero,
            ) {
                Ok(spair) => {
                    new_spairs.push(spair);
                    false
                }
                Err(red_to_zero) => red_to_zero,
            };
            reduces_to_zero.push(red_to_zero);
        }
        self.reduces_to_zero.add_column(reduces_to_zero);

        // Sort by signature in decreasing order, so we can pop the next element from the tail.
        new_spairs.sort_unstable_by(|a, b| b.signature.cmp(&a.signature));

        if let Some(head_spair) = new_spairs.pop() {
            let column: Vec<u32> = new_spairs.into_iter().map(|spair| spair.idx).collect();
            let origin_idx = basis.polys.len() as u32;

            self.heads.push(SPairColumn {
                head_spair,
                column,
                origin_idx,
            });
        }
    }

    /// Extract the one of the S-pairs with minimal signature. There can be multiple.
    fn pop<'a, C: Field>(
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
        assert!(a_poly.idx == head.origin_idx);
        let b_poly = basis[ret.idx as usize].as_ref();
        assert!(b_poly.idx == ret.idx);

        // Update the column's head and insert it back into the heap
        if let Some(next_head_idx) = head.column.pop() {
            head.head_spair = HalfSPair::new_unconditionally(a_poly, next_head_idx, basis);
            self.heads.push(head);
        }

        Some((ret.signature, a_poly, b_poly))
    }

    /// Return the next S-pair to be reduced, which is the S-pair of minimal
    /// signature. Or None if there are no more S-pairs.
    pub fn get_next<'a, C: Field>(
        &mut self,
        basis: &KnownBasis<O, I, C, P>,
        syzygies: &mut BTreeMap<Signature<O, I, P>, DivMask>,
    ) -> Option<(
        MaskedSignature<O, I, P>,
        Polynomial<O, I, C, P>,
        Vec<(u32, u32)>,
    )> {
        let mut same_sign_spairs = Vec::new();

        // Iterate until some S-pair remains that is not eliminated by one
        // of the late elimination criteria.
        while let Some((signature, a_poly, b_poly)) = self.pop(&basis.polys) {
            same_sign_spairs.clear();
            same_sign_spairs.push((a_poly.idx, b_poly.idx));

            let m_sign = MaskedSignature {
                divmask: basis.div_map.map(&signature.monomial),
                signature,
            };

            // Late test for signature criterion:
            let mut chosen_spair = if contains_divisor(&m_sign, &syzygies) {
                // Eliminated by signature criterion
                Err(true)
            } else {
                // Either we get a S-pair, or it was not eliminated by signature.
                PartialSPair::new_if_not_eliminated(a_poly, b_poly).ok_or(false)
            };

            // Duplicate signature criterion: only one of all S-pairs of the
            // same signature must be chosen, the one with the smallest
            // leading monomial.
            while let Some(head) = self.heads.peek() {
                if head.head_spair.signature != m_sign.signature {
                    break;
                }

                let (_, a_poly, b_poly) = self.pop(&basis.polys).unwrap();
                same_sign_spairs.push((a_poly.idx, b_poly.idx));

                // Only process the new S-pair if no other of same signature has been eliminated.
                if let Ok(spair) = &mut chosen_spair {
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
                            // The new S-pair was eliminated by relatively prime
                            // criterion (or amazingly, reduced to zero), so
                            // every S-pair of same signature can be eliminated
                            // as well.
                            chosen_spair = Err(false);
                        }
                    }
                }
            }

            // All S-pairs of this signature have been consumed, and there
            // is at most one remaining.
            match chosen_spair {
                Ok(spair) => {
                    // We found a potential S-pair. Apply rewrite criterion it
                    // and return if not singular.
                    if let Some(spair) = rewrite_spair(&m_sign, spair, basis) {
                        return Some((m_sign, spair, same_sign_spairs));
                    }
                }
                Err(eliminated_by_signature) => {
                    // The current S-pair has been eliminated. If it was not
                    // eliminated by signature, we stumbled upon a Koszul
                    // sygyzy, so we add its signature to help eliminating
                    // future cases.
                    //
                    // We don't need to add the Koszul signature for every
                    // polynomial pair discarded because this signature we are
                    // adding necessarily divides all of them.
                    if !eliminated_by_signature {
                        syzygies.insert(m_sign.signature, m_sign.divmask);
                    }

                    // Mark every popped S-pair as reducing to zero.
                    self.mark_as_syzygy(&same_sign_spairs[..]);
                }
            };
        }
        // No s-pair found, we are done.
        None
    }

    pub fn mark_as_syzygy(&mut self, indices: &[(u32, u32)]) {
        for idx in indices {
            self.reduces_to_zero.set(*idx, true);
        }
    }
}
