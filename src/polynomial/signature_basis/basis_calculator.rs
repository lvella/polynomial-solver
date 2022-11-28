use std::{fmt::Display, ptr::addr_of};

use crate::polynomial::{
    division::Field, divmask::MaximumExponentsTracker, monomial_ordering::Ordering, Id, Monomial,
    Polynomial,
};

use super::{
    contains_divisor, indices::ratio_monomial_index::RatioMonomialIndex, s_pairs, CmpMap, DivMap,
    DivMask, MaskedMonomialRef, MaskedSignature, Ratio, SignPoly, SignedExponent,
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

    /// Basis indexed both by sinature/LM ratio and LM. Used in multidimensional
    /// search for reducer and high base divisor.
    pub(super) by_sign_lm_ratio_and_lm: RatioMonomialIndex<O, I, C, P>,
    // TODO: create an n-D index specifically for singular criterion and low base
    // divisor, indexing both signature/leading monomial ratio and signature
    // monomial variables.
}

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display> KnownBasis<O, I, C, P> {
    /// Returns either a regular reducer (whose factor*reducer has smaller
    /// signature than the reduced) or a singular reducer (where the signature
    /// is the same), in the absence of a regular reducer.
    ///
    /// The search for a singular reducer could be separated from the search for
    /// a regular reducer, but since those searches are used in close proximity
    /// and are very related, I think it saves time to do both here.
    pub(super) fn find_a_reducer(
        &self,
        ratio: &Ratio<O, I, P>,
        monomial: MaskedMonomialRef<O, I, P>,
    ) -> Option<&SignPoly<O, I, C, P>> {
        self.by_sign_lm_ratio_and_lm
            .find_a_reducer(ratio, monomial)
            .map(|ptr| unsafe { &*ptr })
    }
}

pub type SyzygySet<O, I, P> = Vec<(Monomial<O, I, P>, DivMask)>;

/// Hold together the structures that must be coherent during the algorithm execution
pub struct BasisCalculator<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// The basis elements and syzygies.
    basis: KnownBasis<O, I, C, P>,

    /// For each new input polynomial processed, this is a set of signatures of
    /// polynomials know to reduce to zero, for that signature index.
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
    pub fn new(num_vars: usize) -> Self {
        let max_exp = MaximumExponentsTracker::new(num_vars);
        let div_map = DivMap::new(&max_exp);
        let by_sign_lm_ratio_and_lm = RatioMonomialIndex::new(num_vars, &div_map, Vec::new());
        BasisCalculator {
            basis: KnownBasis {
                div_map,
                max_exp,
                polys: Vec::new(),
                by_sign_lm_ratio_and_lm,
            },
            syzygies: SyzygySet::new(),
            spairs: s_pairs::SPairTriangle::new(),
            ratio_map: CmpMap::new(),
        }
    }

    /// Returns the next spair signature, polynomial, and the set of index pairs
    /// that originates this same S-pair.
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

        self.basis
            .by_sign_lm_ratio_and_lm
            .insert(&self.basis.div_map, sign_poly.as_ref());

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

    /// Recalculate divmaps and rebalance indexes.
    pub fn maybe_rebuild_structures(&mut self) {
        const RECALC_PERCENTAGE: u8 = 20;

        // If changes are smaller then the give percerntage, do nothing.
        if !self
            .basis
            .max_exp
            .has_grown_beyond_percentage(RECALC_PERCENTAGE)
        {
            return;
        }

        println!("Rebuilding indexes.");

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
        for (monomial, divmask) in self.syzygies.iter_mut() {
            *divmask = div_map.map(&monomial);
        }

        // Recreate the index for reductions.
        self.basis.by_sign_lm_ratio_and_lm = RatioMonomialIndex::new(
            self.basis.max_exp.len(),
            div_map,
            self.basis.polys.iter().map(|p| addr_of!(**p)).collect(),
        );
    }

    pub fn clear_syzygies(&mut self) {
        self.syzygies.clear();
    }

    fn add_syzygy(&mut self, signature: MaskedSignature<O, I, P>) {
        self.update_max_exp(&signature.signature.monomial);

        self.syzygies
            .push((signature.signature.monomial, signature.divmask));
    }

    fn update_max_exp(&mut self, monomial: &Monomial<O, I, P>) {
        for var in monomial.product.iter() {
            self.basis.max_exp.add_var(var);
        }
    }

    pub fn print_statistics(&self) {
        println!(
            "* singular criterion eliminations: {}",
            self.spairs.get_singular_criterion_counter()
        );
        println!(
            "* low base divisors found: {}",
            self.spairs.get_lbd_counter()
        );
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
