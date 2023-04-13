//! This module uses a k-d tree to provide a multidimensional index on signature
//! to leading monomial ratio and the exponents of the leading monomial.

use std::marker::PhantomData;
use std::rc::Rc;

use crate::kd_tree::{self, DataOperations, KDTree, SearchPath};
use crate::polynomial::divmask::DivMaskTestResult;
use crate::polynomial::signature_basis::{
    get_var_exp_from_monomial, Masked, Ratio, SignPoly, Signature,
};
use crate::polynomial::Monomial;
use crate::polynomial::{division::Field, monomial_ordering::Ordering, Id, VariablePower};

use super::{make_dense_monomial, DivMap, SignedExponent};

/// The entries stored in the leafs are raw pointers to SignPoly.
struct Entry<O: Ordering, I: Id, F: Field, E: SignedExponent>(Rc<SignPoly<O, I, F, E>>);

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> Entry<O, I, F, E> {
    fn lm(&self) -> &Monomial<O, I, E> {
        &self.0.lm.value
    }
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> kd_tree::Entry for Entry<O, I, F, E> {
    type KeyElem = KeyElem<O, I, F, E>;
    type PartitionFilter = PartitionFilter<O, I, F, E>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
        if dim == 0 {
            KeyElem::S2LMRatio(Rc::clone(&self.0))
        } else {
            let id = I::from_idx(dim - 1);
            let power = get_var_exp_from_lm(&self.0, &id);
            KeyElem::MonomialVar(VariablePower { id, power })
        }
    }

    fn average_filter(&self, other: &Self, dim: usize) -> Self::PartitionFilter {
        let a = &*self.0;
        let b = &*other.0;
        if dim == 0 {
            // The tree elements must have accelerated ratio comparers, so these
            // unwrap must not panic:
            let cmp_a = a.sign_to_lm_ratio.borrow().get_comparer().unwrap();
            let cmp_b = b.sign_to_lm_ratio.borrow().get_comparer().unwrap();

            // The average must be calculated as u64 because we use the entire u32
            // space as accelerator.
            let avg = (cmp_a as u64 + cmp_b as u64 + 1) / 2;
            PartitionFilter::S2LMRatio(avg as u32, PhantomData {})
        } else {
            let id = I::from_idx(dim - 1);

            let exp_a = get_var_exp_from_lm(&a, &id);
            let exp_b = get_var_exp_from_lm(&b, &id);
            let avg = (exp_a + exp_b + E::one()) / E::from(2);

            PartitionFilter::MonomialVar(VariablePower { id, power: avg })
        }
    }

    fn cmp_dim(&self, other: &Self::KeyElem) -> std::cmp::Ordering {
        let poly = &*self.0;
        match other {
            KeyElem::S2LMRatio(other) => poly.sign_to_lm_ratio_cmp(&other),
            KeyElem::MonomialVar(var) => get_var_exp_from_lm(&poly, &var.id).cmp(&var.power),
        }
    }
}

fn get_var_exp_from_lm<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    poly: &SignPoly<O, I, F, E>,
    id: &I,
) -> E {
    get_var_exp_from_monomial(&poly.lm.value, id)
}

/// The key element 0 is a signature/leading monomial ratio, which is stored as
/// the integer comparer and a pointer to the original. The other key elements
/// are variables to some power, factors of the leading monomial.
enum KeyElem<O: Ordering, I: Id, F: Field, E: SignedExponent> {
    S2LMRatio(Rc<SignPoly<O, I, F, E>>),
    MonomialVar(VariablePower<I, E>),
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> kd_tree::KeyElem for KeyElem<O, I, F, E> {
    fn dim_index(&self) -> usize {
        match self {
            KeyElem::S2LMRatio(_) => 0,
            KeyElem::MonomialVar(var) => var.id.to_idx() + 1,
        }
    }
}

/// This partition is almost like a KeyElem, but just uses the int accelerator
/// for comparisons on the S2LMRatio (which can't be inserted on the tree
/// because has no monomial associated).
enum PartitionFilter<O: Ordering, I: Id, F: Field, E: SignedExponent> {
    S2LMRatio(u32, PhantomData<(O, F)>),
    MonomialVar(VariablePower<I, E>),
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> kd_tree::PartitionFilter
    for PartitionFilter<O, I, F, E>
{
    type Entry = Entry<O, I, F, E>;

    fn is_less(&self, e: &Self::Entry) -> bool {
        let poly = &*e.0;
        match self {
            PartitionFilter::S2LMRatio(comparer, _) => {
                poly.sign_to_lm_ratio.borrow().get_comparer().unwrap() < *comparer
            }
            PartitionFilter::MonomialVar(var) => get_var_exp_from_lm(&poly, &var.id) < var.power,
        }
    }

    fn into_key(self) -> Option<<Self::Entry as kd_tree::Entry>::KeyElem> {
        match self {
            PartitionFilter::S2LMRatio(_, _) => None,
            PartitionFilter::MonomialVar(var) => Some(KeyElem::MonomialVar(var)),
        }
    }
}

/// Struct implementing the operations needed on building the kD-Tree.
struct Operations<O: Ordering, I: Id, F: Field, E: SignedExponent> {
    div_map: Rc<DivMap<E>>,
    _phantom: PhantomData<(O, I, F)>,
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> DataOperations for Operations<O, I, F, E> {
    type Entry = Entry<O, I, F, E>;
    type NodeData = Masked<Monomial<O, I, E>>;

    /// Calculate the GCD of leading monomials among all given entries.
    fn make(&self, entries: &[Self::Entry]) -> Self::NodeData {
        Masked::gcd_all(entries.iter().map(|e| e.lm()), &self.div_map).unwrap()
    }

    /// Update a node_data with the GCD of itself and the leading monomial of a
    /// new entry.
    fn update(&self, node_data: &mut Self::NodeData, new_entry: &Self::Entry) {
        node_data.gcd_update(&new_entry.lm(), &self.div_map);
    }
}

/// A k-dimensional tree index, indexed by the signatures/leading monomial ratio
/// and the exponents of the leading monomial.
///
/// The tree is accelerated by the having the divmask of the GCD between all
/// contained elements, to quickly rule out the branch on search for a divisor,
/// using the fact that if a divides b then GCD(a, c) also divides b, for any c.
pub struct RatioMonomialIndex<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    KDTree<Operations<O, I, F, E>>,
);

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> RatioMonomialIndex<O, I, F, E> {
    pub(in crate::polynomial::signature_basis) fn new(
        num_variables: usize,
        div_map: Rc<DivMap<E>>,
        elems: &[Rc<SignPoly<O, I, F, E>>],
    ) -> Self {
        let entries = elems.into_iter().map(|e| Entry(Rc::clone(e))).collect();
        Self(KDTree::new(
            num_variables + 1,
            entries,
            Operations {
                div_map,
                _phantom: PhantomData {},
            },
        ))
    }

    pub(in crate::polynomial::signature_basis) fn insert(
        &mut self,
        elem: Rc<SignPoly<O, I, F, E>>,
    ) {
        self.0.insert(Entry(elem))
    }

    pub(in crate::polynomial::signature_basis) fn find_high_base_divisor(
        &self,
        s_lm_ratio: &Ratio<O, I, E>,
        lm: &Masked<Monomial<O, I, E>>,
    ) -> Option<Rc<SignPoly<O, I, F, E>>> {
        let mut best: Option<Rc<SignPoly<O, I, F, E>>> = None;
        let dense_monomial = make_dense_monomial(&lm.value);
        self.0.search(
            &|key, contained_gcd| {
                if let DivMaskTestResult::NotDivisible = contained_gcd.divmask.divides(&lm.divmask)
                {
                    return SearchPath::None;
                };

                match key {
                    KeyElem::S2LMRatio(key) => {
                        // Since the reference polynomial is fully regular
                        // reduced, all possible divisors must have higher
                        // signature/LM ratio, otherwise it would already have
                        // been reduced or eliminated as singular.
                        if *s_lm_ratio < *key.sign_to_lm_ratio.borrow() {
                            SearchPath::Both
                        } else {
                            SearchPath::GreaterOrEqualThan
                        }
                    }
                    KeyElem::MonomialVar(var) => {
                        let mut path = SearchPath::Both;
                        if let Some(exp) = dense_monomial.get(var.id.to_idx()) {
                            if *exp < var.power {
                                path = SearchPath::LessThan;
                            }
                        }
                        path
                    }
                }
            },
            &mut |Entry(poly)| {
                if poly.lm.divides(&lm) {
                    assert!(*poly.sign_to_lm_ratio.borrow() > *s_lm_ratio);
                    match &best {
                        Some(best_poly) => {
                            // The best high base divisor is the one with
                            // maximum signature/lead ratio.
                            if poly.sign_to_lm_ratio > best_poly.sign_to_lm_ratio {
                                best = Some(Rc::clone(poly));
                            }
                        }
                        None => best = Some(Rc::clone(poly)),
                    }
                }

                true
            },
        );

        best
    }

    /// For low base divisor, find the polynomial with maximum sign/lm ratio
    /// whose signature divides sign_poly's.
    pub(in crate::polynomial::signature_basis) fn find_low_base_divisor(
        &self,
        sign_poly: &SignPoly<O, I, F, E>,
    ) -> Option<Rc<SignPoly<O, I, F, E>>> {
        let mut found: Option<Rc<SignPoly<O, I, F, E>>> = None;

        self.0.search(
            &|key, _| {
                if let KeyElem::S2LMRatio(key) = key {
                    let b_sign_idx = key.signature().idx;
                    match b_sign_idx.cmp(&sign_poly.signature().idx) {
                        std::cmp::Ordering::Less => SearchPath::GreaterOrEqualThan,
                        std::cmp::Ordering::Equal => SearchPath::Both,
                        std::cmp::Ordering::Greater => SearchPath::LessThan,
                    }
                } else {
                    SearchPath::Both
                }
            },
            &mut |Entry(poly)| {
                if poly.signature().idx == sign_poly.signature().idx
                    && poly.masked_signature.divides(&sign_poly.masked_signature)
                {
                    match &found {
                        Some(best_match) => {
                            if poly.sign_to_lm_ratio > best_match.sign_to_lm_ratio {
                                found = Some(Rc::clone(poly));
                            }
                        }
                        None => found = Some(Rc::clone(poly)),
                    }
                }
                true
            },
        );

        found
    }

    pub(in crate::polynomial::signature_basis) fn find_a_reducer(
        &self,
        s_lm_ratio: &Ratio<O, I, E>,
        lm: &Masked<Monomial<O, I, E>>,
    ) -> Option<Rc<SignPoly<O, I, F, E>>> {
        let dense_monomial = make_dense_monomial(&lm.value);
        let mut found: Option<Rc<SignPoly<O, I, F, E>>> = None;
        self.0.search(
            &|key, contained_gcd| {
                if let DivMaskTestResult::NotDivisible = contained_gcd.divmask.divides(&lm.divmask)
                {
                    return SearchPath::None;
                };

                match key {
                    KeyElem::S2LMRatio(key) => {
                        if *s_lm_ratio < *key.sign_to_lm_ratio.borrow() {
                            SearchPath::LessThan
                        } else {
                            SearchPath::Both
                        }
                    }
                    KeyElem::MonomialVar(var) => {
                        if let Some(exp) = dense_monomial.get(var.id.to_idx()) {
                            if *exp < var.power {
                                return SearchPath::LessThan;
                            }
                        }
                        SearchPath::Both
                    }
                }
            },
            &mut |Entry(poly)| {
                let ord = poly.sign_to_lm_ratio.borrow().cmp(s_lm_ratio);
                if ord.is_le() && poly.lm.divides(&lm) {
                    found = Some(Rc::clone(poly));
                    // Keep searching if ratios are equal (meaning this find is
                    // a singular reducer), otherwise stop searching (this find
                    // is a regular reducer, which takes precedence).
                    ord.is_eq()
                } else {
                    true
                }
            },
        );

        found
    }

    /// Singular criterion test: search in the basis for an element with
    /// signature S and leading monomial M such that:
    /// - there is a monomial k such k*S is equal the provided S-Pair's
    /// signature T (which means S divides the T);
    /// - and where k*M is smaller than the provided S-Pair's leading monomial
    /// (which translates to signature/LM ratio of the S-Pair being lower than
    /// S/M).
    ///
    /// This search only uses the indexed signature/LM ratio to narrow down the
    /// possible signature divisors.
    pub(in crate::polynomial::signature_basis) fn test_singular_criterion(
        &self,
        sign: &Masked<Signature<O, I, E>>,
        lm: &Monomial<O, I, E>,
    ) -> bool {
        let ratio_mon = sign.value.monomial.fraction_division(lm);

        let mut is_singular = false;
        self.0.search(
            &|key, _| {
                if let KeyElem::S2LMRatio(b_ratio) = key {
                    let b_ratio = b_ratio.sign_to_lm_ratio.borrow();
                    let b_ratio = b_ratio.get_value();
                    match b_ratio.idx.cmp(&sign.value.idx) {
                        std::cmp::Ordering::Less => SearchPath::GreaterOrEqualThan,
                        std::cmp::Ordering::Equal => {
                            if b_ratio.monomial > ratio_mon {
                                SearchPath::Both
                            } else {
                                SearchPath::GreaterOrEqualThan
                            }
                        }
                        std::cmp::Ordering::Greater => SearchPath::LessThan,
                    }
                } else {
                    SearchPath::Both
                }
            },
            &mut |Entry(poly)| {
                is_singular = sign.value.idx == poly.signature().idx
                    && poly.masked_signature.divides(&sign)
                    && ratio_mon < poly.sign_to_lm_ratio.borrow().get_value().monomial;

                !is_singular
            },
        );
        is_singular
    }
}

#[cfg(test)]
mod tests {
    use crate::polynomial::Polynomial;

    use super::get_var_exp_from_monomial;

    pub type Poly = Polynomial<crate::polynomial::monomial_ordering::Grevlex, u8, i32, i32>;

    #[test]
    fn test_get_var_exp() {
        let [x8, x7]: [Poly; 2] = Poly::new_variables([8u8, 7u8]).try_into().unwrap();

        let poly = x8.clone() * x8.clone() * x7;
        let exp = get_var_exp_from_monomial(&poly.terms[0].monomial, &8);
        assert!(exp == 2);
    }
}
