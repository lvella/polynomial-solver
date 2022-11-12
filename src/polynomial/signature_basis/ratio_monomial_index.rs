//! This module uses a k-d tree to provide a multidimensional index on signature
//! to leading monomial ratio and the exponents of the leading monomial.

use crate::kd_tree::{self, KDTree, SearchPath};
use crate::polynomial::divmask::DivMaskTestResult;
use crate::polynomial::Monomial;
use crate::polynomial::{division::Field, monomial_ordering::Ordering, Id, VariablePower};

use super::{DivMap, DivMask, MaskedMonomialRef, Ratio, SignPoly, SignedExponent};

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

/// Returns the exponent of a variable inside a monomial.
fn get_var_exp_from_monomial<O: Ordering, I: Id, E: SignedExponent>(
    monomial: &Monomial<O, I, E>,
    id: &I,
) -> E {
    let m = &monomial.product;
    // Is binary search better than linear?
    // TODO: Maybe create a dense monomial to skip this search?
    match m.binary_search_by(|v| id.cmp(&v.id)) {
        Ok(idx) => m[idx].power.clone(),
        Err(_) => E::zero(),
    }
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

#[derive(Clone)]
struct MaskedMonomial<O: Ordering, I: Id, E: SignedExponent> {
    divmask: DivMask,
    monomial: Monomial<O, I, E>,
}

/// A k-dimensional tree index, indexed by the signatures/leading monomial ratio
/// and the exponents of the leading monomial.
///
/// The tree is accelerated by the having the divmask of the GCD between all
/// contained elements, to quickly rule out the branch on search for a divisor,
/// using the fact that if a divides b then GCD(a, c) also divides b, for any c.
pub struct RatioMonomialIndex<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    KDTree<Entry<O, I, F, E>, MaskedMonomial<O, I, E>>,
);

/// Maps a tree entry to its NodeData.
fn node_data_map<O: Ordering, I: Id, F: Field, E: SignedExponent>(
    div_map: &DivMap<E>,
    &Entry(p): &Entry<O, I, F, E>,
) -> MaskedMonomial<O, I, E> {
    let monomial = unsafe { (*p).polynomial.terms[0].monomial.clone() };
    let divmask = div_map.map(&monomial);
    MaskedMonomial { divmask, monomial }
}

/// Maps a tree entry to its NodeData.
fn node_data_builder<O: Ordering, I: Id, E: SignedExponent>(
    div_map: &DivMap<E>,
    a: MaskedMonomial<O, I, E>,
    b: &MaskedMonomial<O, I, E>,
) -> MaskedMonomial<O, I, E> {
    let gcd = a.monomial.gcd(&b.monomial);
    let divmask = div_map.map(&gcd);
    MaskedMonomial {
        divmask,
        monomial: gcd,
    }
}

impl<O: Ordering, I: Id, F: Field, E: SignedExponent> RatioMonomialIndex<O, I, F, E> {
    pub fn new(
        num_variables: usize,
        div_map: &DivMap<E>,
        elems: Vec<*const SignPoly<O, I, F, E>>,
    ) -> Self {
        let entries = elems.into_iter().map(|e| Entry(e)).collect();
        Self(KDTree::new(
            num_variables + 1,
            entries,
            &|e| node_data_map(div_map, e),
            &|a, b| node_data_builder(div_map, a, b),
        ))
    }

    pub fn insert(&mut self, div_map: &DivMap<E>, elem: *const SignPoly<O, I, F, E>) {
        let new_entry = Entry(elem);
        self.0
            .insert(new_entry, &|e| node_data_map(div_map, e), &|a, b| {
                node_data_builder(div_map, a, b)
            })
    }

    pub(super) fn find_high_base_divisor(
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

    pub(super) fn find_a_reducer(
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
}

/// Makes a dense vector with the exponents of a monomial, up to the largest
/// variable id.
fn make_dense_monomial<O: Ordering, I: Id, E: SignedExponent>(
    monomial: &Monomial<O, I, E>,
) -> Vec<E> {
    let largest_id = monomial.product.get(0).map_or(0, |var| var.id.to_idx());
    let mut dense_monomial = Vec::new();
    dense_monomial.resize(largest_id + 1, E::zero());
    for var in monomial.product.iter() {
        dense_monomial[var.id.to_idx()] = var.power.clone();
    }

    dense_monomial
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
