//! This module uses a k-d tree to provide a multidimensional index on signature
//! to leading monomial ratio and the exponents of the leading monomial.

use std::marker::PhantomData;
use std::rc::Rc;

use crate::kd_tree::{self, DataOperations, KDTree, SearchPath};
use crate::polynomial::divmask::DivMaskTestResult;
use crate::polynomial::signature_basis::{
    get_var_exp_from_monomial, MaskedMonomialRef, MaskedSignature, Ratio, SignPoly,
};
use crate::polynomial::Monomial;
use crate::polynomial::{division::Field, monomial_ordering::Ordering, Id, VariablePower};

use super::{make_dense_monomial, DivMap, MaskedMonomial, SignedExponent};

/// The entries stored in the leafs are raw pointers to SignPoly.
struct Entry<O: Ordering, I: Id, F: Field, E: SignedExponent>(*const SignPoly<O, I, F, E>);

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> Clone for Entry<O, I, F, E> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<O: Ordering, I: Id, F: Field, E: SignedExponent> Copy for Entry<O, I, F, E> {}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> kd_tree::Entry for Entry<O, I, F, E> {
    type KeyElem = KeyElem<O, I, E>;

    fn get_key_elem(&self, dim: usize) -> Self::KeyElem {
        let poly = unsafe { &(*self.0) };
        if dim == 0 {
            KeyElem::S2LMRatio(&poly.sign_to_lm_ratio)
        } else {
            let id = I::from_idx(dim - 1);
            let power = get_var_exp_from_lm(poly, &id);
            KeyElem::MonomialVar(VariablePower { id, power })
        }
    }

    fn average_key_elem(&self, other: &Self, dim: usize) -> Self::KeyElem {
        let b = unsafe { &(*other.0) };
        if dim == 0 {
            KeyElem::S2LMRatio(&b.sign_to_lm_ratio)
        } else {
            let a = unsafe { &(*self.0) };
            let id = I::from_idx(dim - 1);

            let exp_a = get_var_exp_from_lm(a, &id);
            let exp_b = get_var_exp_from_lm(b, &id);
            let avg = (exp_a + exp_b + E::one()) / E::from(2);
            KeyElem::MonomialVar(VariablePower { id, power: avg })
        }
    }

    fn cmp_dim(&self, other: &Self::KeyElem) -> std::cmp::Ordering {
        let poly = unsafe { &(*self.0) };
        match other {
            KeyElem::S2LMRatio(ratio) => poly.sign_to_lm_ratio.cmp(unsafe { &(**ratio) }),
            KeyElem::MonomialVar(var) => get_var_exp_from_lm(poly, &var.id).cmp(&var.power),
        }
    }
}

fn get_var_exp_from_lm<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    poly: &SignPoly<O, I, F, E>,
    id: &I,
) -> E {
    get_var_exp_from_monomial(&poly.polynomial.terms[0].monomial, id)
}

/// The key element 0 is a signature/leading monomial ratio, which is stored as
/// the integer comparer and a pointer to the original. The other key elements
/// are variables to some power, factors of the leading monomial.
enum KeyElem<O: Ordering, I: Id, E: SignedExponent> {
    S2LMRatio(*const Ratio<O, I, E>),
    MonomialVar(VariablePower<I, E>),
}

impl<O: Ordering, I: Id, E: SignedExponent> kd_tree::KeyElem for KeyElem<O, I, E> {
    fn dim_index(&self) -> usize {
        match self {
            KeyElem::S2LMRatio(_) => 0,
            KeyElem::MonomialVar(var) => var.id.to_idx() + 1,
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

    type NodeData = MaskedMonomial<O, I, E>;

    /// Creates a monomial mask from the leading monomial of the entry.
    fn map(&self, entry: &Self::Entry) -> Self::NodeData {
        let monomial = unsafe { (*entry.0).polynomial.terms[0].monomial.clone() };
        let divmask = self.div_map.map(&monomial);
        MaskedMonomial { divmask, monomial }
    }

    /// GCD between NodeData
    fn accum(&self, a: Self::NodeData, other: &Self::NodeData) -> Self::NodeData {
        a.gcd(other, &self.div_map)
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
    pub fn new(
        num_variables: usize,
        div_map: Rc<DivMap<E>>,
        elems: Vec<*const SignPoly<O, I, F, E>>,
    ) -> Self {
        let entries = elems.into_iter().map(|e| Entry(e)).collect();
        Self(KDTree::new(
            num_variables + 1,
            entries,
            Operations {
                div_map,
                _phantom: PhantomData {},
            },
        ))
    }

    pub fn insert(&mut self, elem: *const SignPoly<O, I, F, E>) {
        self.0.insert(Entry(elem))
    }

    pub(in crate::polynomial::signature_basis) fn find_high_base_divisor(
        &self,
        s_lm_ratio: &Ratio<O, I, E>,
        lm: MaskedMonomialRef<O, I, E>,
    ) -> Option<*const SignPoly<O, I, F, E>> {
        let mut best: Option<*const SignPoly<O, I, F, E>> = None;
        let dense_monomial = make_dense_monomial(lm.1);
        self.0.search(
            &|key, contained_gcd| {
                if let DivMaskTestResult::NotDivisible = contained_gcd.divmask.divides(lm.0) {
                    return SearchPath::None;
                };

                match key {
                    KeyElem::S2LMRatio(ratio) => {
                        // Since the reference polynomial is fully regular
                        // reduced, all possible divisors must have higher
                        // signature/LM ratio, otherwise it would already have
                        // been reduced or eliminated as singular.
                        if unsafe { *s_lm_ratio < **ratio } {
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
            &mut |Entry(poly_ptr)| {
                let poly = unsafe { &**poly_ptr };
                if poly.leading_monomial().divides(&lm) {
                    assert!(poly.sign_to_lm_ratio > *s_lm_ratio);
                    match best {
                        Some(best_poly) => {
                            let best_poly = unsafe { &*best_poly };
                            // The best high base divisor is the one that with
                            // maximum signature/lead ratio.
                            if poly.sign_to_lm_ratio > best_poly.sign_to_lm_ratio {
                                best = Some(*poly_ptr);
                            }
                        }
                        None => best = Some(*poly_ptr),
                    }
                }

                true
            },
        );

        best
    }

    pub(in crate::polynomial::signature_basis) fn find_a_reducer(
        &self,
        s_lm_ratio: &Ratio<O, I, E>,
        lm: MaskedMonomialRef<O, I, E>,
    ) -> Option<*const SignPoly<O, I, F, E>> {
        let dense_monomial = make_dense_monomial(lm.1);
        let mut found = None;
        self.0.search(
            &|key, contained_gcd| {
                if let DivMaskTestResult::NotDivisible = contained_gcd.divmask.divides(lm.0) {
                    return SearchPath::None;
                };

                match key {
                    KeyElem::S2LMRatio(ratio) => {
                        if s_lm_ratio < (unsafe { &(**ratio) }) {
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
            &mut |Entry(poly_ptr)| {
                let poly = unsafe { &**poly_ptr };
                let ord = poly.sign_to_lm_ratio.cmp(s_lm_ratio);
                if ord != std::cmp::Ordering::Greater && poly.leading_monomial().divides(&lm) {
                    found = Some(*poly_ptr);
                    // Keep searching if ratios are equal (meaning this find is
                    // a singular reducer), otherwise stop searching (this find
                    // is a regular reducer, which takes precedence).
                    ord == std::cmp::Ordering::Equal
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
    pub fn test_singular_criterion(
        &self,
        sign: &MaskedSignature<O, I, E>,
        lm: &Monomial<O, I, E>,
    ) -> bool {
        let ratio_mon = sign.signature.monomial.fraction_division(lm);
        let masked_sig_monomial = sign.monomial();

        let mut is_singular = false;
        self.0.search(
            &|key, _| {
                if let KeyElem::S2LMRatio(b_ratio_ptr) = key {
                    let b_ratio = unsafe { &**b_ratio_ptr }.get_value();
                    match b_ratio.idx.cmp(&sign.signature.idx) {
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
            &mut |Entry(poly_ptr)| {
                let poly = unsafe { &**poly_ptr };
                is_singular = sign.signature.idx == poly.signature().idx
                    && poly
                        .masked_signature
                        .monomial()
                        .divides(&masked_sig_monomial)
                    && ratio_mon < poly.sign_to_lm_ratio.get_value().monomial;
                !is_singular
            },
        );
        is_singular
    }

    /// For low base divisor, find the polynomial with maximum sign/lm ratio
    /// whose signature divides sign_poly's.
    pub fn find_low_base_divisor<'a>(
        &'a self,
        sign_poly: &SignPoly<O, I, F, E>,
    ) -> Option<&'a SignPoly<O, I, F, E>> {
        let mut found: Option<&'a SignPoly<O, I, F, E>> = None;

        self.0.search(
            &|key, _| {
                if let KeyElem::S2LMRatio(b_ratio_ptr) = key {
                    let b_ratio = unsafe { &**b_ratio_ptr }.get_value();
                    match b_ratio.idx.cmp(&sign_poly.signature().idx) {
                        std::cmp::Ordering::Less => SearchPath::GreaterOrEqualThan,
                        std::cmp::Ordering::Equal => SearchPath::Both,
                        std::cmp::Ordering::Greater => SearchPath::LessThan,
                    }
                } else {
                    SearchPath::Both
                }
            },
            &mut |Entry(poly_ptr)| {
                let poly = unsafe { &**poly_ptr };
                if poly.signature().idx == sign_poly.signature().idx
                    && poly
                        .masked_signature
                        .monomial()
                        .divides(&sign_poly.masked_signature.monomial())
                {
                    match found {
                        Some(best_match) => {
                            if poly.sign_to_lm_ratio > best_match.sign_to_lm_ratio {
                                found = Some(poly);
                            }
                        }
                        None => found = Some(poly),
                    }
                }
                true
            },
        );

        found
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
