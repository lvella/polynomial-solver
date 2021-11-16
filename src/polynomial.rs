use super::ordered_sum;
use std::cmp::Ordering as CmpOrd;

trait Id: Eq + Ord {}

trait Coefficient: std::ops::AddAssign + num_traits::Zero + num_traits::One {}

trait Power: Eq + Ord + Clone + num_traits::Unsigned + num_traits::Zero + num_traits::One {}

#[derive(Debug, PartialEq, Eq, Clone)]
struct VariablePower<I, P> {
    id: I,
    power: P,
}

impl<I, P> ordered_sum::Term for VariablePower<I, P> {
    type Key = I;
    type Value = P;

    fn key(&self) -> &Self::Key {
        &self.id
    }
    fn value(self) -> Self::Value {
        self.power
    }
    fn value_ref(&self) -> &Self::Value {
        &self.power
    }
    fn value_ref_mut(&mut self) -> &mut Self::Value {
        &mut self.power
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Monomial<I, P> {
    // Product is sorted in decreasing order of id:
    product: Vec<VariablePower<I, P>>,
    total_power: P,
}

impl<I, P> std::cmp::PartialOrd for Monomial<I, P>
where
    I: Id,
    P: Power,
{
    // For now, just use lexicographical ordering, that is needed to solve the system.
    // For performance reasons, degree reversed lexicographical ordering can be implemented
    // in the future for the computation of the Gröbner Basis, and then converted to an lex ordering.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (a, b) in self.product.iter().zip(other.product.iter()) {
            let id_cmp = a.id.cmp(&b.id);
            if id_cmp != CmpOrd::Equal {
                return Some(id_cmp);
            }

            let power_cmp = a.power.cmp(&b.power);
            if power_cmp != CmpOrd::Equal {
                return Some(power_cmp);
            }
        }

        // If all the leading powers are equal, the one with most powers is bigger
        Some(self.product.len().cmp(&other.product.len()))
    }
}

impl<I, P> std::cmp::Ord for Monomial<I, P>
where
    I: Id,
    P: Power,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Term<I, C, P> {
    coefficient: C,
    monomial: Monomial<I, P>,
}

impl<I, C, P> Term<I, C, P>
where
    P: Power,
{
    fn new(coefficient: C, id: I, power: P) -> Self {
        Term {
            coefficient,
            monomial: Monomial {
                product: vec![VariablePower {
                    id,
                    power: power.clone(),
                }],
                total_power: power,
            },
        }
    }

    fn new_constant(value: C) -> Self {
        Term {
            coefficient: value,
            monomial: Monomial {
                product: Vec::new(),
                total_power: P::zero(),
            },
        }
    }
}

impl<I, C, P> ordered_sum::Term for Term<I, C, P> {
    type Key = Monomial<I, P>;
    type Value = C;

    fn key(&self) -> &Self::Key {
        &self.monomial
    }
    fn value(self) -> Self::Value {
        self.coefficient
    }
    fn value_ref(&self) -> &Self::Value {
        &self.coefficient
    }
    fn value_ref_mut(&mut self) -> &mut Self::Value {
        &mut self.coefficient
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Polynomial<I, C, P> {
    // Terms are sorted in decreasing order of monomials
    terms: Vec<Term<I, C, P>>,
}

impl<I, C, P> Polynomial<I, C, P>
where
    C: Coefficient,
    P: Power,
{
    fn new_variables(var_ids: impl IntoIterator<Item = I>) -> Vec<Self> {
        var_ids
            .into_iter()
            .map(|id| Self::new_monomial_term(C::one(), id, P::one()))
            .collect()
    }

    fn new_monomial_term(coefficient: C, id: I, power: P) -> Self {
        Self {
            terms: vec![Term::new(coefficient, id, power)],
        }
    }

    fn new_constant(value: C) -> Self {
        Self {
            terms: vec![Term::new_constant(value)],
        }
    }
}

impl<I, C, P> std::ops::Add<Polynomial<I, C, P>> for Polynomial<I, C, P>
where
    I: Id,
    C: Coefficient,
    P: Power,
{
    type Output = Polynomial<I, C, P>;

    fn add(self, rhs: Polynomial<I, C, P>) -> Self::Output {
        Self {
            terms: ordered_sum::ordered_sum(self.terms, rhs.terms),
        }
    }
}

/*
impl<I, C, P> std::ops::Mul<Polynomial<I, C, P>> for Polynomial<I, C, P>
where
    I: Id,
    C: Coefficient,
    P: Power,
{
    type Output = Polynomial<I, C, P>;

    fn mul(self, rhs: Polynomial<I, C, P>) -> Self::Output {
        let new_terms = std::collections::BTreeMap::new();
        let outer_iter = self.terms.into_iter();

        for a in self.terms {
            for b in rhs.terms.iter() {
                let new_coef = a.coefficient * b.coefficient;
            }
        }

        self
    }
}
*/

impl<I, C, P> std::ops::Add<C> for Polynomial<I, C, P>
where
    C: Coefficient,
    P: Power,
{
    type Output = Polynomial<I, C, P>;

    fn add(mut self, rhs: C) -> Self::Output {
        let size = self.terms.len();
        let last = &mut self.terms[size - 1];
        if last.monomial.product.is_empty() {
            last.coefficient += rhs;
        } else {
            self.terms.push(Term::new_constant(rhs));
        }

        self
    }
}

impl Id for u8 {}
impl Power for u32 {}
impl Coefficient for u32 {}

type SmallPoly = Polynomial<u8, u32, u32>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn addition_ordering() {
        let [z, y, x]: [SmallPoly; 3] = SmallPoly::new_variables([0u8, 1u8, 2u8])
            .try_into()
            .unwrap();
        let a = x.clone() + y.clone() + z.clone() + 42;
        let b = y + 42 + z + x;

        assert_eq!(a, b);
        println!("a = {:#?}", a);

        let c = a + b;
        println!("c = {:#?}", c);

        assert_eq!(c.terms.len(), 4);
        // For the first 3 terms:
        for i in 0..3 {
            // The coefficient is 2:
            assert_eq!(c.terms[i].coefficient, 2);
            // It has only one variable:
            assert_eq!(c.terms[i].monomial.product.len(), 1);
            // The power of such variable is 1:
            assert_eq!(c.terms[i].monomial.product[0].power, 1);
            // The terms are in decreasing order:
            assert_eq!(c.terms[i].monomial.product[0].id, 2 - i as u8);
        }

        // The last term has no variables and the coefficient is 84:
        assert!(c.terms[3].monomial.product.is_empty());
        assert_eq!(c.terms[3].coefficient, 84);
    }

    #[test]
    fn many_terms_addition() {
        let [x0, x1, x2, x3, x4, x5, x6, x7]: [SmallPoly; 8] =
            SmallPoly::new_variables(0u8..8).try_into().unwrap();

        let a = x0 + x1 + x3.clone() + x4;
        let b = x2 + x3 + x5 + x6 + x7 + 42;

        let c = a.clone() + b.clone();
        let d = b + a;

        println!("c = {:#?}", c);

        assert_eq!(c, d);
    }
}
