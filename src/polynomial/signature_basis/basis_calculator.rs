use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    fmt::Display,
    rc::Rc,
};

use num_traits::One;
use replace_with::replace_with_or_abort;

use crate::polynomial::{
    division::Field, divmask::MaximumExponentsTracker, monomial_ordering::Ordering, Id, Monomial,
    Polynomial, Term,
};

use super::{
    indices::{monomial_index::MonomialIndex, ratio_monomial_index::RatioMonomialIndex},
    s_pairs, sign_to_monomial_ratio, CmpMap, DivMap, DivMask, Masked, Ratio, SignPoly, Signature,
    SignedExponent,
};

/// The fraction of all term reductions a polynomial must be part as reducer to
/// be considered hot, and be subject to full reduction. I.e., a polynomial is
/// fully reduced if its reduction_count >= total_reductions *
/// HOT_REDUCER_FRACTION.
const HOT_REDUCER_FRACTION: f64 = 0.75;

/// Stores all the basis elements known and processed so far.
///
/// Everything is public because all fields must be read by the user, and the
/// user can only get an immutable reference.
pub struct KnownBasis<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// Number of variables in the system.
    pub num_vars: usize,

    /// Mapping between monomials and divmasks that is dependent on the current
    /// distribution of the monomial.
    pub div_map: Rc<DivMap<P>>,

    /// Owns the basis polynomials, ordered by insertion order (which is
    /// important to the spair triangle).
    pub(super) polys: Vec<Rc<SignPoly<O, I, C, P>>>,

    /// Basis indexed both by sinature/LM ratio and LM. Used in multidimensional
    /// search for reducer and high base divisor.
    pub(super) by_sign_lm_ratio_and_lm: RatioMonomialIndex<O, I, C, P>,
    // TODO: create an n-D index specifically for singular criterion and low base
    // divisor, indexing both signature/leading monomial ratio and signature
    // monomial variables.
}

impl<O: Ordering, I: Id, C: Field, P: SignedExponent> KnownBasis<O, I, C, P> {
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
        monomial: &Masked<Monomial<O, I, P>>,
    ) -> Option<Rc<SignPoly<O, I, C, P>>> {
        self.by_sign_lm_ratio_and_lm.find_a_reducer(ratio, monomial)
    }
}

pub type SyzygySet<O, I, E> = MonomialIndex<O, I, E>;

/// Hold together the structures that must be coherent during the algorithm execution
pub struct BasisCalculator<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// The basis elements and syzygies.
    basis: KnownBasis<O, I, C, P>,

    /// For each new input polynomial processed, this is a set of signatures of
    /// polynomials know to reduce to zero, for that signature index.
    ///
    /// TODO: maybe periodically remove elements that are divisible by other
    /// elements
    syzygies: SyzygySet<O, I, P>,

    /// Tracks the maximum exponent seen for each variable, and the evolution.
    max_exp: MaximumExponentsTracker<P>,

    /// Priority queue of the S-pairs pending to be processed.
    /// Elements are represent as pair of indices in "basis" Vec.
    spairs: s_pairs::SPairTriangle<O, I, P>,

    /// Maps signature/monomial ratios to numbers for fast comparison:
    ratio_map: CmpMap<O, I, P>,

    /// Number of term reductions performed so far.
    reduction_count: usize,
}

/// The 3 possible results of a regular reduction.
pub(super) enum RegularReductionResult<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    /// Polynomial was singular top reducible
    Singular,
    /// Polynomial was reduced to zero.
    Zero(Masked<Signature<O, I, P>>),
    /// Polynomial was reduced to some non-zero constant.
    NonZeroConstant(Polynomial<O, I, C, P>),
    /// Polynomial was reduced to some non singular top reducible polynomial.
    Reduced(SignPoly<O, I, C, P>),
}

/// The possible results of a regular reduction step
enum ReductionStepResult<O: Ordering, I: Id, C: Field, P: SignedExponent> {
    Singular,
    Zero,
    Reduced(Term<O, I, C, P>, Ratio<O, I, P>, DivMask),
}

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display>
    BasisCalculator<O, I, C, P>
{
    /// Creates a new basis calculator.
    pub fn new(num_vars: usize) -> Self {
        let max_exp = MaximumExponentsTracker::new(num_vars);
        let div_map = Rc::new(DivMap::new(&max_exp));
        let by_sign_lm_ratio_and_lm = RatioMonomialIndex::new(num_vars, div_map.clone(), &[]);
        let syzygies = MonomialIndex::new(num_vars, div_map.clone(), vec![]);
        BasisCalculator {
            basis: KnownBasis {
                num_vars,
                div_map,
                polys: Vec::new(),
                by_sign_lm_ratio_and_lm,
            },
            max_exp,
            syzygies,
            spairs: s_pairs::SPairTriangle::new(),
            ratio_map: CmpMap::new(),
            reduction_count: 0,
        }
    }

    /// Returns the next spair signature, polynomial, and the set of index pairs
    /// that originates this same S-pair.
    pub(super) fn get_next_spair(
        &mut self,
    ) -> Option<(
        Masked<Signature<O, I, P>>,
        BTreeMap<Monomial<O, I, P>, C>,
        Vec<(u32, u32)>,
    )> {
        self.spairs
            .get_next(&self.basis, &mut self.syzygies, &mut self.max_exp)
    }

    pub fn get_basis(&self) -> &KnownBasis<O, I, C, P> {
        &self.basis
    }

    pub fn get_num_syzygies(&self) -> usize {
        self.syzygies.len()
    }

    /// Adds a new polynomial to the Gröbner Basis and calculates its S-pairs.
    pub(super) fn insert_poly_with_spairs(&mut self, sign_poly: SignPoly<O, I, C, P>) {
        // Insert the new polynomial ratio to the ratio map, and we maybe have to
        // rebuild the whole map.
        if sign_poly
            .sign_to_lm_ratio
            .borrow_mut()
            .update(&mut self.ratio_map)
            .is_err()
        {
            // The new ratio does not fit into the ratio_map, rebuild it to make room:
            println!("Rebuilding the ratio map.");
            self.ratio_map.rebuild();

            // If it doesn't fit now, the map is too full so there is nothing we
            // can do. We unwrap and let it panic.
            sign_poly
                .sign_to_lm_ratio
                .borrow_mut()
                .update(&mut self.ratio_map)
                .unwrap();

            // Update every existing polynomial, this can't fail:
            for p in self.basis.polys.iter() {
                // Since the elements were already in the map, this can't fail.
                p.sign_to_lm_ratio
                    .borrow_mut()
                    .update(&mut self.ratio_map)
                    .unwrap();
            }
        }

        let sign_poly = Rc::new(sign_poly);

        self.max_exp
            .update(&sign_poly.masked_signature.value.monomial);

        self.max_exp.update(&sign_poly.lm.value);
        for term in sign_poly.tail.borrow().iter() {
            self.max_exp.update(&term.monomial);
        }

        self.spairs
            .add_column(&sign_poly, &self.basis, &self.syzygies);

        self.basis
            .by_sign_lm_ratio_and_lm
            .insert(Rc::clone(&sign_poly));

        self.basis.polys.push(sign_poly);
    }

    pub(super) fn add_spair_syzygy(
        &mut self,
        signature: Masked<Signature<O, I, P>>,
        indices: &[(u32, u32)],
    ) {
        self.spairs.mark_as_syzygy(indices);
        self.add_syzygy(signature);
    }

    pub fn add_koszul_syzygies(&mut self, indices: &[(u32, u32)]) {
        for (p, q) in indices {
            let mut signature;
            let divmask;
            {
                let p = &*self.basis.polys[*p as usize];
                let q = &*self.basis.polys[*q as usize];

                // Choose q to be the basis of the signature:
                let (sign_basis, lm_basis) = match p.sign_to_lm_ratio_cmp(&q) {
                    std::cmp::Ordering::Less => (q, p),
                    std::cmp::Ordering::Equal => {
                        // Non-regular Koszul syzygy, skip,
                        continue;
                    }
                    std::cmp::Ordering::Greater => (p, q),
                };

                signature = sign_basis.signature().clone();
                signature.monomial = signature.monomial * lm_basis.lm.value.clone();
                divmask = self.basis.div_map.map(&signature.monomial);
            }

            let masked_signature = Masked {
                divmask,
                value: signature,
            };
            // Do not add redundant koszul syzygies:
            if !self.syzygies.contains_divisor(&masked_signature) {
                self.add_syzygy(masked_signature);
                // DO NOT mark the original S-pair as syzygy, because it is not!
                // Except in special cases that have already been handled,
                // Koszul(a,b) != S-pair(a,b)
                // I.e. the S-pair itself is not a syzygy.
            }
        }
    }

    /// Fully reduce hot reducers and recalculate divmaps and rebalance indexes.
    pub fn optimize_structures(&mut self) {
        const RECALC_PERCENTAGE: u8 = 20;

        // If changes are smaller then the give percerntage, do nothing.
        if !self.max_exp.has_grown_beyond_percentage(RECALC_PERCENTAGE) {
            return;
        }

        println!("Rebuilding indexes.");

        // Reset by_sign_lm_ratio_and_lm index, so that we only have one
        // reference to each SignPoly, so we can mutate them from inside a Rc.
        replace_with_or_abort(&mut self.basis.by_sign_lm_ratio_and_lm, |old_index| {
            drop(old_index);

            // Recreate the div map.
            self.max_exp.reset_tracking();
            self.basis.div_map = Rc::new(DivMap::new(&self.max_exp));
            let div_map = Rc::clone(&self.basis.div_map);

            // Recalculate both masks of each polynomial. Rc::get_mut should
            // succeed because the index is gone by now, so we hold the only
            // reference counter.
            for poly in self.basis.polys.iter_mut().map(|p| Rc::get_mut(p).unwrap()) {
                poly.lm.divmask = div_map.map(&poly.lm.value);

                let sign_divmask = div_map.map(&poly.signature().monomial);
                poly.masked_signature.divmask = sign_divmask;
            }

            // Recalculates the mask and recreates the index for syzygy basis.
            replace_with_or_abort(&mut self.syzygies, |syzygies| {
                let mut syzygies = syzygies.to_vec();
                for syzygy in syzygies.iter_mut() {
                    syzygy.divmask = div_map.map(&syzygy.value);
                }
                SyzygySet::new(self.basis.num_vars, Rc::clone(&div_map), syzygies)
            });

            // Recreate the index for reductions.
            RatioMonomialIndex::new(self.basis.num_vars, div_map, &self.basis.polys)
        });
    }

    pub fn clear_syzygies(&mut self) {
        self.syzygies = SyzygySet::new(self.basis.num_vars, self.basis.div_map.clone(), vec![]);
    }

    fn add_syzygy(&mut self, signature: Masked<Signature<O, I, P>>) {
        self.max_exp.update(&signature.value.monomial);

        self.syzygies.insert(Masked {
            divmask: signature.divmask,
            value: signature.value.monomial,
        });
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

    /// Regular reduction, as defined in the paper, but only for the head term.
    ///
    /// It seems that only reducing the head term often saves us a lot of time.
    pub(super) fn regular_reduce_head(
        &mut self,
        idx: u32,
        m_sign: Masked<Signature<O, I, P>>,
        mut to_reduce: BTreeMap<Monomial<O, I, P>, C>,
    ) -> RegularReductionResult<O, I, C, P> {
        let result = self.regular_reduce_step(true, &m_sign, &mut to_reduce);

        match result {
            ReductionStepResult::Reduced(head, sign_to_lm_ratio, lm_divmask) => {
                if head.monomial.is_one() {
                    let polynomial = Polynomial { terms: vec![head] };
                    RegularReductionResult::NonZeroConstant(polynomial)
                } else {
                    let tail: Vec<Term<O, I, C, P>> = to_reduce
                        .into_iter()
                        .rev()
                        .map(|(monomial, coefficient)| Term {
                            monomial,
                            coefficient,
                        })
                        .collect();

                    let lm = Masked {
                        divmask: lm_divmask,
                        value: head.monomial,
                    };

                    RegularReductionResult::Reduced(SignPoly {
                        inv_leading_coeff: head.coefficient.clone().inv(),
                        leading_coeff: head.coefficient,
                        lm,
                        masked_signature: m_sign,
                        idx,
                        sign_to_lm_ratio: RefCell::new(sign_to_lm_ratio),
                        tail: RefCell::new(tail),
                        as_reducer_count: Cell::new(0),
                        is_hot_reducer: Cell::new(false),
                    })
                }
            }
            ReductionStepResult::Singular => RegularReductionResult::Singular,
            ReductionStepResult::Zero => {
                assert!(to_reduce.is_empty());
                RegularReductionResult::Zero(m_sign)
            }
        }
    }

    /// Fully reduce hot reducers.
    fn regular_reduce_tail(&mut self, poly: &SignPoly<O, I, C, P>) {
        // Borrow mut the tail of the polynomial and fully reduce it:
        replace_with_or_abort(&mut *poly.tail.borrow_mut(), |tail| {
            // Build the BTreeMap used as reduction input. It seems to be
            // faster if inserted in ascending order, thus the rev().
            let mut to_reduce: BTreeMap<Monomial<O, I, P>, C> = tail
                .into_iter()
                .rev()
                .map(|t| (t.monomial, t.coefficient))
                .collect();

            let mut tail = Vec::new();
            while let ReductionStepResult::Reduced(term, _, _) =
                self.regular_reduce_step(false, &poly.masked_signature, &mut to_reduce)
            {
                tail.push(term);
            }

            tail
        });
    }

    /// One step of regular reduction algorithm.
    ///
    /// Reduces the leading term until the first term that can't be reduced,
    /// returning it, alongside its properties.
    ///
    /// Reduction is analogous to calculate the remainder on a multivariate
    /// polynomial division, but with extra restrictions on what polynomials can
    /// be the divisor according to their signature.
    ///
    /// The paper suggests splitting the reduced polynomial into a hash map of
    /// monomial -> coefficient, so that we can efficiently sum the new terms,
    /// and a priority queue, so that we know what is the next monomial to be
    /// reduced. We can do both with a single BTreeMap, which is ordered and has
    /// fast map access. I have tested both solutions, and in bigger problems
    /// BTreeMap seems a little better.
    fn regular_reduce_step(
        &mut self,
        is_head_reduction: bool,
        m_sign: &Masked<Signature<O, I, P>>,
        to_reduce: &mut BTreeMap<Monomial<O, I, P>, C>,
    ) -> ReductionStepResult<O, I, C, P> {
        use ReductionStepResult::*;

        while let Some((monomial, coefficient)) = to_reduce.pop_last() {
            // Calculate signature to monomial ratio, to search for a reducer,
            // and possibly store it as the ratio for the leading term.
            let sign_to_term_ratio = sign_to_monomial_ratio(&m_sign.value, &monomial);

            // Calculate the divmask for the term to be reduced:
            let monomial = Masked {
                divmask: self.basis.div_map.map(&monomial),
                value: monomial,
            };

            if let Some(reducer) = {
                // Skip searching for a reducer if term is constant, and hopefully save some time.
                if monomial.value.is_one() {
                    None
                } else {
                    self.basis.find_a_reducer(&sign_to_term_ratio, &monomial)
                }
            } {
                // The reduction is said singular if we are reducing the leading
                // term and the factor*reducer have the same signature as the reduced.
                // This translates to equal signature/monomial ratio. In this case
                // we can stop.
                if is_head_reduction && *reducer.sign_to_lm_ratio.borrow() == sign_to_term_ratio {
                    return Singular;
                }

                // Increment the global reduction counter.
                self.reduction_count += 1;

                // Increment the usage counter for the reducer.
                let reducer_count = reducer.as_reducer_count.get() + 1;
                reducer.as_reducer_count.set(reducer_count);

                // Set this polynomial to be reduced if we find it to be hot.
                if !reducer.is_hot_reducer.get()
                    && reducer_count as f64 >= self.reduction_count as f64 * HOT_REDUCER_FRACTION
                {
                    reducer.is_hot_reducer.set(true);
                    // It is fine to call this recursively here because no
                    // reducer found on the call stack so far will be found
                    // again as reducer, because they necessarily have bigger
                    // leading monomials than the monomial in any term being
                    // reduced.
                    self.regular_reduce_tail(&reducer);
                }

                // Calculate the multiplier monomial that will nullify the term.
                // We can unwrap() because we trust "find_a_regular_reducer" to
                // have returned a valid reducer.
                let factor_monomial = monomial.value.whole_division(&reducer.lm.value).unwrap();

                // Calculate the multiplier's coefficient using the reducer leading term:
                let factor_coefficient = coefficient.elimination_factor(&reducer.inv_leading_coeff);

                // Subtract every element of the reducer from the rest of the
                // polynomial.
                for term in reducer.tail.borrow().iter() {
                    use std::collections::btree_map::Entry;

                    let reducer_coef = factor_coefficient.clone() * term.coefficient.clone();
                    let reducer_monomial = factor_monomial.clone() * term.monomial.clone();

                    match to_reduce.entry(reducer_monomial) {
                        Entry::Vacant(entry) => {
                            // There was no such monomial, just insert:
                            entry.insert(reducer_coef);
                        }
                        Entry::Occupied(mut entry) => {
                            // Sum the coefficients, and remove if result is zero.
                            *entry.get_mut() += reducer_coef;
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

            // No reducer was found, so the term is fully reduced and we can
            // return it.
            return Reduced(
                Term {
                    monomial: monomial.value,
                    coefficient,
                },
                sign_to_term_ratio,
                monomial.divmask,
            );
        }

        Zero
    }
}

impl<O: Ordering, I: Id, C: Field + Display, P: SignedExponent + Display> IntoIterator
    for BasisCalculator<O, I, C, P>
{
    type Item = Polynomial<O, I, C, P>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        // Drop the index here otherwise the unwrap of the Rc will fail.
        drop(self.basis.by_sign_lm_ratio_and_lm);

        self.basis
            .polys
            .into_iter()
            .map(|sign_poly| Rc::try_unwrap(sign_poly).unwrap().into_polynomial())
    }
}
