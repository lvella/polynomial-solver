use std::{collections::BTreeMap, fmt::Display};

use num_traits::{One, Zero};

use crate::polynomial::{
    division::Field, divmask::MaximumExponentsTracker, monomial_ordering::Ordering, Id, Monomial,
    Polynomial,
};

use super::{
    contains_divisor, s_pairs, CmpMap, DivMap, DivMask, MaskedMonomialRef, MaskedSignature,
    PointedCmp, Ratio, SignPoly, Signature, SignedExponent,
};

/// Stores all the basis elements known and processed so far.
///
/// Everything is public because all fields must be read by the user, and the
/// user can only get an immutable reference.
pub struct KnownBasis<O: Ordering, I: Id, C: Field, P: SignedExponent> {
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
        BTreeMap<(PointedCmp<Ratio<O, I, P>>, u32), *const SignPoly<O, I, C, P>>,
    // TODO: create an n-D index specifically for rewrite criterion and low base
    // divisor, indexing both signature/leading monomial ratio and signature
    // monomial variables.
}

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display> KnownBasis<O, I, C, P> {
    pub(super) fn find_a_regular_reducer(
        &self,
        ratio: &Ratio<O, I, P>,
        monomial: MaskedMonomialRef<O, I, P>,
    ) -> Option<&SignPoly<O, I, C, P>> {
        // Filter out the unsuitable ratios:
        let suitable = self
            .by_sign_lm_ratio
            .range(..=(PointedCmp(ratio), u32::MAX));

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
pub struct BasisCalculator<O: Ordering, I: Id, C: Field, P: SignedExponent> {
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

    /// Maps signature/monomial ratios to numbers for fast comparison:
    ratio_map: CmpMap<O, I, P>,
}

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display>
    BasisCalculator<O, I, C, P>
{
    /// Creates a new basis calculator.
    ///
    /// May fail if the input contains a constant polynomial, in which case the
    /// polynomial is returned as the error.
    pub fn new(input: Vec<Polynomial<O, I, C, P>>) -> Result<Self, Polynomial<O, I, C, P>> {
        let mut max_exp = MaximumExponentsTracker::new();

        let filtered_input: Vec<Polynomial<O, I, C, P>> = input
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

        max_exp.reset_tracking();
        let mut c = BasisCalculator {
            basis: KnownBasis {
                div_map: DivMap::new(&max_exp),
                max_exp,
                polys: Vec::new(),
                by_sign_lm_ratio: BTreeMap::new(),
            },
            syzygies: SyzygySet::new(),
            spairs: s_pairs::SPairTriangle::new(),
            ratio_map: CmpMap::new(),
        };

        // Insert all input polynomials in the basis.
        for polynomial in filtered_input {
            let monomial = Monomial::one();

            let signature = Signature {
                idx: c.basis.polys.len() as u32,
                monomial,
            };

            let sign_poly = SignPoly::new(&c.basis.div_map, signature.idx, signature, polynomial);

            println!(
                "#(p: {}, s: {}), [] → {}",
                c.basis.polys.len(),
                c.get_num_syzygies(),
                sign_poly
            );
            c.insert_poly_with_spairs(sign_poly);
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
    pub fn insert_poly_with_spairs(&mut self, mut sign_poly: SignPoly<O, I, C, P>) {
        // Insert the new polynomial ratio to the ratio map, and we maybe have to
        // rebuild the whole map.
        if sign_poly
            .sign_to_lm_ratio
            .update(&mut self.ratio_map)
            .is_err()
        {
            // The new ratio does not fit into the ratio_map, rebuid it to make room:
            println!("Rebuilding the ratio map.");
            self.ratio_map.rebuild();

            // If it doesn't fit now, the map is too full so there is nothing we
            // can do. We unwrap and let it panic.
            sign_poly
                .sign_to_lm_ratio
                .update(&mut self.ratio_map)
                .unwrap();

            // Update every existing polynomial, this can't fail:
            for p in self.basis.polys.iter_mut() {
                // Since the elements were already in the map, this can't fail.
                p.as_mut()
                    .sign_to_lm_ratio
                    .update(&mut self.ratio_map)
                    .unwrap();
            }
        }

        let sign_poly = Box::new(sign_poly);

        self.update_max_exp(&sign_poly.masked_signature.signature.monomial);
        for term in sign_poly.polynomial.terms.iter() {
            self.update_max_exp(&term.monomial);
        }

        self.spairs
            .add_column(&sign_poly, &self.basis, &self.syzygies);

        self.basis.by_sign_lm_ratio.insert(
            (PointedCmp(&sign_poly.sign_to_lm_ratio), sign_poly.idx),
            sign_poly.as_ref(),
        );

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

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display> IntoIterator
    for BasisCalculator<O, I, C, P>
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
