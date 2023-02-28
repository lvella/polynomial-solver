//! S-pairs data structures.

use std::{cmp::max, collections::BinaryHeap, fmt::Display, marker::PhantomData, ops::Index};

use bitvec::prelude::BitVec;
use itertools::Itertools;

use crate::polynomial::{
    division::Field, monomial_ordering::Ordering, Id, Monomial, Polynomial, Term, VariablePower,
};

use super::{
    basis_calculator::SyzygySet, contains_divisor, DivMask, KnownBasis, MaskedMonomialRef,
    MaskedSignature, PointedCmp, Ratio, SignPoly, Signature, SignedExponent,
};

/// Calculate monomial factor that is multiplied to base to get the S-pair.
fn calculate_spair_factor<O: Ordering, I: Id, C: Field, P: SignedExponent>(
    base: &SignPoly<O, I, C, P>,
    other: &SignPoly<O, I, C, P>,
) -> Monomial<O, I, P> {
    other.polynomial.terms[0]
        .monomial
        .div_by_gcd(&base.polynomial.terms[0].monomial)
}

/// Half S-pair
///
/// This contains only what is needed to classify the S-pair (the signature), and
/// the index of the other polynomial needed to build the full S-pair.
struct HalfSPair<O: Ordering, I: Id, P: SignedExponent> {
    signature: Signature<O, I, P>,
    idx: u32,
}

impl<O: Ordering, I: Id, P: SignedExponent> HalfSPair<O, I, P> {
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
        let signature =
            sign_base.signature().clone() * calculate_spair_factor(sign_base, sign_other);
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
}

/// Contains the information needed to compute the S-pair polynomial, including
/// its first reducer.
struct SPairBuildInfo<O: Ordering, I: Id, P: SignedExponent> {
    /// The monomial that multiplying by the base polynomial will give the SPair.
    multiplier: Monomial<O, I, P>,
    /// The idx of the base polynomial.
    base_idx: u32,
    /// This is the index of the other polynomial in the S-pair.
    other_idx: u32,
}

impl<O: Ordering, I: Id, P: SignedExponent> SPairBuildInfo<O, I, P> {
    /// Get the index pair that originated this S-pair.
    ///
    /// Biggest idx comes first, just to preserve the convention.
    fn idx_pair(&self) -> (u32, u32) {
        if self.base_idx > self.other_idx {
            (self.base_idx, self.other_idx)
        } else {
            (self.other_idx, self.base_idx)
        }
    }
}

/// Contains the information needed to compute the full S-pair.
struct SPairInfo<O: Ordering, I: Id, P: SignedExponent> {
    signature: Signature<O, I, P>,
    build_info: SPairBuildInfo<O, I, P>,
    lms_are_relativelly_prime: bool,
}

impl<O: Ordering, I: Id, P: SignedExponent> SPairInfo<O, I, P> {
    /// Creates a new S-pair info without checking for any elimination criteria.
    fn new<C: Field>(
        a_poly: &SignPoly<O, I, C, P>,
        b_poly: &SignPoly<O, I, C, P>,
        signature: Option<Signature<O, I, P>>,
    ) -> Self {
        let lms_are_relativelly_prime = !a_poly.polynomial.terms[0]
            .monomial
            .has_shared_variables(&b_poly.polynomial.terms[0].monomial);

        // Find what polynomial to calculate the signature from.
        // It is the one with highest signature to LM ratio.
        let (sign_base, sign_other) = match a_poly.sign_to_lm_ratio_cmp(&b_poly) {
            std::cmp::Ordering::Less => (b_poly, a_poly),
            _ => (a_poly, b_poly),
        };

        let multiplier = calculate_spair_factor(sign_base, sign_other);
        let signature = match signature {
            Some(s) => s,
            None => sign_base.signature().clone() * multiplier.clone(),
        };

        SPairInfo {
            signature,
            build_info: SPairBuildInfo {
                multiplier,
                base_idx: sign_base.idx,
                other_idx: sign_other.idx,
            },
            lms_are_relativelly_prime,
        }
    }

    /// Creates a new S-pair info directly from a HalfSpair.
    fn from_half<C: Field>(
        half_spair: HalfSPair<O, I, P>,
        b_poly: &SignPoly<O, I, C, P>,
        basis: &KnownBasis<O, I, C, P>,
    ) -> Self {
        let a_poly = basis.polys[half_spair.idx as usize].as_ref();
        Self::new(b_poly, a_poly, Some(half_spair.signature))
    }
}

/// Elements of the SPairTriangle, ordered by spair signature, where head_spair
/// is the first.
struct SPairColumn<O: Ordering, I: Id, P: SignedExponent> {
    head_spair: SPairInfo<O, I, P>,

    /// The index of the polynomial S-pairing with the others in the colum.
    origin_idx: u32,

    /// Index of polynomials ordered by descending signature of the S-pair with origin_idx.
    ///
    /// After head_spair is consumed, an element is popped from this vec to build the next
    /// spair_head with origin_idx.
    column: Vec<u32>,
}

impl<O: Ordering, I: Id, P: SignedExponent> PartialEq for SPairColumn<O, I, P> {
    fn eq(&self, other: &Self) -> bool {
        self.head_spair.signature.eq(&other.head_spair.signature)
    }
}

impl<O: Ordering, I: Id, P: SignedExponent> Eq for SPairColumn<O, I, P> {}

impl<O: Ordering, I: Id, P: SignedExponent> PartialOrd for SPairColumn<O, I, P> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&other))
    }
}

impl<O: Ordering, I: Id, P: SignedExponent> Ord for SPairColumn<O, I, P> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // The elements are ordered in descending order so that
        // the binary heap will return the smallest element.
        other.head_spair.signature.cmp(&self.head_spair.signature)
    }
}

/// S-Pair where only the leading term has been evaluated.
pub struct PartialSPair<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> {
    pub leading_term: Term<O, I, C, P>,
    origin_poly: &'a SignPoly<O, I, C, P>,
    build_info: SPairBuildInfo<O, I, P>,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> PartialSPair<'a, O, I, C, P> {
    fn new(
        build_info: SPairBuildInfo<O, I, P>,
        basis: &'a [Box<SignPoly<O, I, C, P>>],
    ) -> PartialSPair<'a, O, I, C, P> {
        let origin_poly = basis[build_info.base_idx as usize].as_ref();
        let mut leading_term = origin_poly.polynomial.terms[0].clone();
        leading_term.monomial = leading_term.monomial * build_info.multiplier.clone();

        Self {
            leading_term,
            origin_poly,
            build_info,
        }
    }

    pub fn complete(self: Self) -> Polynomial<O, I, C, P> {
        let mut terms = vec![self.leading_term];
        terms.extend(self.origin_poly.polynomial.terms[1..].iter().map(|term| {
            let mut term = term.clone();
            term.monomial = self.build_info.multiplier.clone() * term.monomial;
            term
        }));

        Polynomial { terms }
    }
}

/// Base divisors used in the base divisor criterion.
///
/// TODO: Test without this criterion again when a proper multidimensional index
/// have been implemented, because right now it makes things worse, not better.
struct BaseDivisors<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> {
    high: Option<HighBaseDivisor<'a, O, I, C, P>>,
    low: Option<LowBaseDivisor<'a, O, I, C, P>>,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> BaseDivisors<'a, O, I, C, P> {
    fn new(sign_poly: &SignPoly<O, I, C, P>, basis: &KnownBasis<O, I, C, P>) -> Self {
        Self {
            high: HighBaseDivisor::new(sign_poly, basis),
            low: LowBaseDivisor::new(sign_poly, basis),
        }
    }
}

struct HighBaseDivisor<'a, O: Ordering, I: Id, C: Field, P: SignedExponent>(
    &'a SignPoly<O, I, C, P>,
);

impl<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> HighBaseDivisor<'a, O, I, C, P> {
    fn new(sign_poly: &SignPoly<O, I, C, P>, basis: &KnownBasis<O, I, C, P>) -> Option<Self> {
        let lm = sign_poly.leading_monomial();

        basis
            .by_sign_lm_ratio_and_lm
            .find_high_base_divisor(&sign_poly.sign_to_lm_ratio, lm)
            .map(|ptr| Self(unsafe { &*ptr }))
    }
}

/// An iterator aggregating multiple VariablePower iterators, assumed to be in
/// descending order of variable id.
///
/// Each element is a tuple (variable_id, vec_of_powers) for the power of
/// variable_id for each iterator. If some variable is not present in some
/// iterator, the value is set to zero. As long as a variable id is present in
/// at least one iterator, it will be output.
struct MultiVarWalk<'a, I: 'a + Id, P: 'a + SignedExponent> {
    iters: Vec<&'a mut dyn Iterator<Item = &'a VariablePower<I, P>>>,
    current: Vec<Option<&'a VariablePower<I, P>>>,
    next_id: Option<I>,
}

impl<'a, I: 'a + Id, P: 'a + SignedExponent> MultiVarWalk<'a, I, P> {
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

impl<'a, I: 'a + Id, P: 'a + SignedExponent> Iterator for MultiVarWalk<'a, I, P> {
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
struct LowBaseDivisor<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> {
    divisor: &'a SignPoly<O, I, C, P>,
    /// The x^v in the paper.
    discriminator: Monomial<O, I, P>,
    discriminator_mask: DivMask,
}

impl<'a, O: Ordering, I: Id, C: Field, P: SignedExponent> LowBaseDivisor<'a, O, I, C, P> {
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
            .range(..=(PointedCmp(&range_max), u32::MAX))
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

        let mut multivar_iter = MultiVarWalk::new(vec![&mut ia, &mut ib, &mut ip])
            .fuse()
            .peekable();

        v.product.retain_mut(|var| {
            let multivar = match multivar_iter.peek() {
                Some(x) => x,
                None => return true,
            };

            // b == p, so v is infinity (unchanged)
            if var.id != multivar.0 {
                return true;
            }
            let multivar = multivar_iter.next().unwrap();

            // We have a, b and p, do the comparison:
            let (a, b, p) = multivar.1.into_iter().next_tuple().unwrap();
            if b > p {
                var.power = max(p, a);
                if var.power.is_zero() {
                    return false;
                }
            }

            true
        });

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
pub struct SPairTriangle<O: Ordering, I: Id, P: SignedExponent> {
    /// Stores the S-pairs to be reduced.
    heads: BinaryHeap<SPairColumn<O, I, P>>,

    /// Tells if an S-pair is a syzygy.
    reduces_to_zero: SyzygyTriangle,

    /// Counter for singular criterion eliminations.
    singular_criterion_counter: usize,
}

impl<O: Ordering, I: Id, P: SignedExponent + Display> SPairTriangle<O, I, P> {
    pub fn new() -> Self {
        SPairTriangle {
            heads: BinaryHeap::new(),
            reduces_to_zero: SyzygyTriangle::new(),
            singular_criterion_counter: 0,
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
                    false /* does not reduce to zero (that we know) */
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
                head_spair: SPairInfo::from_half(head_spair, sign_poly, basis),
                column,
                origin_idx,
            });
        }
    }

    /// Extract the one of the S-pairs with minimal signature. There can be multiple.
    fn pop<C: Field>(&mut self, basis: &[Box<SignPoly<O, I, C, P>>]) -> Option<SPairInfo<O, I, P>> {
        // Get the S-pair at the head of the column
        let mut head = self.heads.pop()?;
        let ret = head.head_spair;

        // Update the column's head and insert it back into the heap
        if let Some(next_head_idx) = head.column.pop() {
            let a_poly = basis[head.origin_idx as usize].as_ref();
            assert!(a_poly.idx == head.origin_idx);
            let b_poly = basis[next_head_idx as usize].as_ref();
            assert!(b_poly.idx == next_head_idx);

            head.head_spair = SPairInfo::new(a_poly, b_poly, None);
            self.heads.push(head);
        }

        Some(ret)
    }

    /// Return the next S-pair to be reduced, which is the S-pair of minimal
    /// signature. Or None if there are no more S-pairs.
    pub fn get_next<'a, C: Field>(
        &mut self,
        basis: &KnownBasis<O, I, C, P>,
        syzygies: &mut SyzygySet<O, I, P>,
    ) -> Option<(
        MaskedSignature<O, I, P>,
        Polynomial<O, I, C, P>,
        Vec<(u32, u32)>,
    )> {
        let mut same_sign_spairs = Vec::new();

        // Iterate until some S-pair remains that is not eliminated by one
        // of the late elimination criteria.
        while let Some(spair) = self.pop(&basis.polys) {
            same_sign_spairs.clear();
            same_sign_spairs.push(spair.build_info.idx_pair());

            let m_sign = MaskedSignature {
                divmask: basis.div_map.map(&spair.signature.monomial),
                signature: spair.signature,
            };

            // Test for relativelly prime criterion.
            let mut chosen_spair = if spair.lms_are_relativelly_prime {
                // Eliminated by the relativelly prime criterion.
                Err(false)
            } else {
                // Late test for signature criterion:
                if contains_divisor(&m_sign, &syzygies) {
                    // Eliminated by signature criterion
                    Err(true)
                } else {
                    // Either we get an S-pair, or it was not eliminated by signature.
                    Ok(PartialSPair::new(spair.build_info, &basis.polys))
                }
            };

            // Duplicate signature criterion: only one of all S-pairs of the
            // same signature must be chosen, the one with the smallest
            // leading monomial.
            while let Some(head) = self.heads.peek() {
                if head.head_spair.signature != m_sign.signature {
                    break;
                }

                let new_spair = self.pop(&basis.polys).unwrap();
                same_sign_spairs.push(new_spair.build_info.idx_pair());

                // Only process the new S-pair if no other of same signature has been eliminated.
                if let Ok(spair) = &mut chosen_spair {
                    if new_spair.lms_are_relativelly_prime {
                        // Eliminated by the relativelly prime criterion.
                        chosen_spair = Err(false)
                    } else {
                        let new_spair = PartialSPair::new(new_spair.build_info, &basis.polys);

                        if new_spair.leading_term.monomial < spair.leading_term.monomial {
                            *spair = new_spair;
                        }
                    }
                }
            }

            // All S-pairs of this signature have been consumed, and there
            // is at most one remaining.
            match chosen_spair {
                Ok(spair) => {
                    // We found a potential S-pair. Apply singular criterion.
                    if !basis
                        .by_sign_lm_ratio_and_lm
                        .test_singular_criterion(&m_sign, &spair.leading_term.monomial)
                    {
                        // S-pair was kept.
                        return Some((m_sign, spair.complete(), same_sign_spairs));
                    } else {
                        self.singular_criterion_counter += 1;
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
                        syzygies.push((m_sign.signature.monomial, m_sign.divmask));
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

    pub fn get_singular_criterion_counter(&self) -> usize {
        self.singular_criterion_counter
    }
}
