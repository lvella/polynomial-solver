use std::{collections::BTreeMap, fmt::Display};

use num_traits::{One, Zero};

use crate::polynomial::{
    division::InvertibleCoefficient, divmask::MaximumExponentsTracker, monomial_ordering::Ordering,
    Id, Monomial, Polynomial,
};

use super::{
    contains_divisor, s_pairs, DivMap, DivMask, MaskedMonomialRef, MaskedSignature, PointedCmp,
    SignPoly, Signature, SignedPower,
};

/// Stores all the basis elements known and processed so far.
///
/// Everything is public because all fields must be read by the user, and the
/// user can only get an immutable reference.
pub struct KnownBasis<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// Tracks the maximum exponent seen for each variable, and the evolution.
    pub max_exp: MaximumExponentsTracker<P>,

    /// Mapping between monomials and divmasks that is dependent on the current
    /// distribution of the monomial.
    pub div_map: DivMap<P>,

    /// Owns the basis polynomials, ordered by insertion order (which is
    /// important to the spair triangle).
    pub polys: Vec<Box<SignPoly<O, I, C, P>>>,

    /// Basis ordered by signature to leading monomial ratio.
    ///
    /// TODO: to search for a reducer and for a high base divisor, maybe this
    /// should be a n-D index (like R*-tree), indexing both the leading monomial
    /// variables and the signature/leading monomial ratio.
    pub(super) by_sign_lm_ratio:
        BTreeMap<PointedCmp<Signature<O, I, P>>, *const SignPoly<O, I, C, P>>,
    // TODO: create an n-D index specifically for rewrite criterion and low base
    // divisor, indexing both signature/leading monomial ratio and signature
    // monomial variables.
}

impl<
        O: Ordering,
        I: Id + Display,
        C: InvertibleCoefficient + Display,
        P: SignedPower + Display,
    > KnownBasis<O, I, C, P>
{
    pub(super) fn find_a_regular_reducer(
        &self,
        ratio: &Signature<O, I, P>,
        monomial: MaskedMonomialRef<O, I, P>,
    ) -> Option<&SignPoly<O, I, C, P>> {
        // Filter out the unsuitable ratios:
        let suitable = self.by_sign_lm_ratio.range(..=PointedCmp(ratio));

        // Search all the suitable range for a divisor of term.
        for (_, elem) in suitable {
            let next = unsafe { &**elem };

            if next.leading_monomial().divides(&monomial) {
                return Some(next);
            }
        }

        None
    }
}

pub type SyzygySet<O, I, P> = BTreeMap<Signature<O, I, P>, DivMask>;

/// Hold together the structures that must be coherent during the algorithm execution
pub struct BasisCalculator<O: Ordering, I: Id, C: InvertibleCoefficient, P: SignedPower> {
    /// The basis elements and syzygies.
    basis: KnownBasis<O, I, C, P>,

    /// Signatures of polynomials know to reduce to zero.
    ///
    /// TODO: use a proper multidimensional index.
    ///
    /// TODO: maybe periodically remove elements that are divisible by other
    /// elements
    syzygies: SyzygySet<O, I, P>,

    /// Priority queue of the S-pairs pending to be processed.
    /// Elements are represent as pair of indices in "basis" Vec.
    spairs: s_pairs::SPairTriangle<O, I, P>,
}

impl<
        O: Ordering,
        I: Id + Display,
        C: InvertibleCoefficient + Display,
        P: SignedPower + Display,
    > BasisCalculator<O, I, C, P>
{
    /// Creates a new basis calculator.
    ///
    /// May fail if the input contains a constant polynomial, in which case the
    /// polynomial is returned as the error.
    pub fn new(input: Vec<Polynomial<O, I, C, P>>) -> Result<Self, Polynomial<O, I, C, P>> {
        let mut max_exp = MaximumExponentsTracker::new();

        let mut filtered_input: Vec<Polynomial<O, I, C, P>> = input
            .into_iter()
            .filter_map(|polynomial| {
                if polynomial.is_zero() {
                    // Zero polynomial is implicitly part of every ideal, so it is
                    // redundant. Discarded by filter_map.
                    return None;
                }

                if polynomial.is_constant() {
                    // Constant polynomial means the ideal is the full set of all
                    // polynomials, for which any constant polynomial is a generator, so
                    // we can stop. Iteration is cut short by collect() into Option<Vec>
                    return Some(Err(polynomial));
                }

                // Update the maximum exponent for each variable used.
                for term in polynomial.terms.iter() {
                    for var in term.monomial.product.iter() {
                        max_exp.add_var(&var);
                    }
                }

                Some(Ok(polynomial))
            })
            .collect::<Result<_, _>>()?;

        // The algorithm performance might depend on the order the elements are
        // given in the input. From my tests with a single input, sorting makes it
        // run much faster.
        filtered_input.sort_unstable();

        max_exp.reset_tracking();
        let mut c = BasisCalculator {
            basis: KnownBasis {
                div_map: DivMap::new(&max_exp),
                max_exp,
                polys: Vec::new(),
                by_sign_lm_ratio: BTreeMap::new(),
            },
            syzygies: BTreeMap::new(),
            spairs: s_pairs::SPairTriangle::new(),
        };

        // Insert all input polynomials in the basis.
        for polynomial in filtered_input {
            let monomial = Monomial::one();

            let signature = Signature {
                idx: c.basis.polys.len() as u32,
                monomial,
            };
            c.insert_poly_with_spairs(SignPoly::new(
                &c.basis.div_map,
                signature.idx,
                signature,
                polynomial,
            ));
        }

        Ok(c)
    }

    pub fn get_next_spair(
        &mut self,
    ) -> Option<(
        MaskedSignature<O, I, P>,
        Polynomial<O, I, C, P>,
        Vec<(u32, u32)>,
    )> {
        self.spairs.get_next(&self.basis, &mut self.syzygies)
    }

    pub fn get_basis(&self) -> &KnownBasis<O, I, C, P> {
        &self.basis
    }

    pub fn get_num_syzygies(&self) -> usize {
        self.syzygies.len()
    }

    /// Adds a new polynomial to the Gröbner Basis and calculates its S-pairs.
    pub fn insert_poly_with_spairs(&mut self, sign_poly: SignPoly<O, I, C, P>) {
        let sign_poly = Box::new(sign_poly);

        self.update_max_exp(&sign_poly.masked_signature.signature.monomial);
        for term in sign_poly.polynomial.terms.iter() {
            self.update_max_exp(&term.monomial);
        }

        self.spairs
            .add_column(&sign_poly, &self.basis, &self.syzygies);

        self.basis
            .by_sign_lm_ratio
            .insert(PointedCmp(&sign_poly.sign_to_lm_ratio), sign_poly.as_ref());

        self.basis.polys.push(sign_poly);
    }

    pub fn add_spair_syzygy(
        &mut self,
        signature: MaskedSignature<O, I, P>,
        indices: &[(u32, u32)],
    ) {
        self.spairs.mark_as_syzygy(indices);
        self.add_syzygy(signature);
    }

    pub fn add_koszul_syzygies(&mut self, indices: &[(u32, u32)]) {
        for (p, q) in indices {
            let p = self.basis.polys[*p as usize].as_ref();
            let q = self.basis.polys[*q as usize].as_ref();

            // Choose q to be the basis of the signature:
            let (sign_basis, lm_basis) = match p.sign_to_lm_ratio_cmp(q) {
                std::cmp::Ordering::Less => (q, p),
                std::cmp::Ordering::Equal => {
                    // Non-regular Koszul syzygy, skip,
                    continue;
                }
                std::cmp::Ordering::Greater => (p, q),
            };

            let mut signature = sign_basis.signature().clone();
            signature.monomial = signature.monomial * lm_basis.polynomial.terms[0].monomial.clone();
            let divmask = self.basis.div_map.map(&signature.monomial);

            let masked_signature = MaskedSignature { divmask, signature };
            if !contains_divisor(&masked_signature, &self.syzygies) {
                self.add_syzygy(masked_signature);
                // DO NOT mark the original S-pair as syzygy, because it is not!
                // Except in special cases that have already been handled,
                // Koszul(a,b) != S-pair(a,b)
                // I.e. the S-pair itself is not a syzygy.
            }
        }
    }

    pub fn maybe_recalculate_divmasks(&mut self) {
        const RECALC_PERCENTAGE: u8 = 20;

        // If changes are smaller then the give percerntage, do nothing.
        if !self
            .basis
            .max_exp
            .has_grown_beyond_percentage(RECALC_PERCENTAGE)
        {
            return;
        }

        println!("Recalculating divmasks.");

        // Recreate the div map.
        self.basis.max_exp.reset_tracking();
        self.basis.div_map = DivMap::new(&self.basis.max_exp);
        let div_map = &self.basis.div_map;

        // Recalculate both masks of each polynomial.
        for poly in self.basis.polys.iter_mut() {
            let lm_divmask = div_map.map(&poly.polynomial.terms[0].monomial);
            poly.as_mut().lm_divmask = lm_divmask;

            let sign_divmask = div_map.map(&poly.signature().monomial);
            poly.as_mut().masked_signature.divmask = sign_divmask;
        }

        // Recalculate the mask of each syzygy.
        for (signature, divmask) in self.syzygies.iter_mut() {
            *divmask = div_map.map(&signature.monomial);
        }
    }

    fn add_syzygy(&mut self, signature: MaskedSignature<O, I, P>) {
        self.update_max_exp(&signature.signature.monomial);

        self.syzygies.insert(signature.signature, signature.divmask);
    }

    fn update_max_exp(&mut self, monomial: &Monomial<O, I, P>) {
        for var in monomial.product.iter() {
            self.basis.max_exp.add_var(var);
        }
    }
}

impl<
        O: Ordering,
        I: Id + Display,
        C: InvertibleCoefficient + Display,
        P: SignedPower + Display,
    > IntoIterator for BasisCalculator<O, I, C, P>
{
    type Item = Polynomial<O, I, C, P>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.basis
            .polys
            .into_iter()
            .map(|sign_poly| sign_poly.polynomial)
    }
}
