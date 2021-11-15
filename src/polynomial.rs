use std::cmp::Ordering;

#[derive(Debug, PartialEq, Eq, Clone)]
struct VariablePower<I, P> {
    id: I,
    power: P,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Monomial<I, P> {
    // Product is sorted in decreasing order of id:
    product: Vec<VariablePower<I, P>>,
    total_power: P,
}

impl<I, P> std::cmp::PartialOrd for Monomial<I, P>
where
    I: Eq + Ord,
    P: Eq + Ord + num_traits::Unsigned,
{
    // For now, just use lexicographical ordering, that is needed to solve the system.
    // For performance reasons, degree reversed lexicographical ordering can be implemented
    // in the future for the computation of the Gröbner Basis, and then converted to an lex ordering.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (a, b) in self.product.iter().zip(other.product.iter()) {
            let id_cmp = a.id.cmp(&b.id);
            if id_cmp != Ordering::Equal {
                return Some(id_cmp);
            }

            let power_cmp = a.power.cmp(&b.power);
            if power_cmp != Ordering::Equal {
                return Some(power_cmp);
            }
        }

        // If all the leading powers are equal, the one with most powers is bigger
        Some(self.product.len().cmp(&other.product.len()))
    }
}

impl<I, P> std::cmp::Ord for Monomial<I, P>
where
    I: Eq + Ord,
    P: Eq + Ord + num_traits::Unsigned,
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
    P: Clone + num_traits::Zero,
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct Polynomial<I, C, P> {
    // Terms are sorted in decreasing order of monomials
    terms: Vec<Term<I, C, P>>,
}

impl<I, C, P> Polynomial<I, C, P>
where
    P: Clone + num_traits::Zero + num_traits::One,
    C: num_traits::Zero + num_traits::One,
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
    I: Eq + Ord,
    C: std::ops::AddAssign + num_traits::Zero + std::cmp::Eq + num_traits::One,
    P: Eq + Ord + Clone + num_traits::Zero + num_traits::One + num_traits::Unsigned,
{
    type Output = Polynomial<I, C, P>;

    fn add(mut self, rhs: Polynomial<I, C, P>) -> Self::Output {
        let mut new_terms = Vec::new();
        let mut a_iter = self.terms.into_iter();
        let mut b_iter = rhs.terms.into_iter();

        let remainer;
        loop {
            let a = a_iter.next();
            let b = b_iter.next();

            match (a, b) {
                (Some(mut a), Some(mut b)) => loop {
                    if a.monomial == b.monomial {
                        a.coefficient += b.coefficient;
                        if a.coefficient != C::zero() {
                            new_terms.push(a);
                        }
                        break;
                    } else if b.monomial > a.monomial {
                        new_terms.push(b);
                        b = a;
                        std::mem::swap(&mut a_iter, &mut b_iter);
                    } else {
                        new_terms.push(a);
                    }

                    if let Some(v) = a_iter.next() {
                        a = v;
                    } else {
                        break;
                    }
                },
                (None, _) => {
                    remainer = b_iter;
                    break;
                }
                _ => {
                    remainer = a_iter;
                    break;
                }
            }
        }

        new_terms.extend(remainer);

        if new_terms.is_empty() {
            Self::new_constant(C::zero())
        } else {
            self.terms = new_terms;
            self
        }
    }
}

impl<I, C, P> std::ops::Add<C> for Polynomial<I, C, P>
where
    C: std::ops::AddAssign + num_traits::Zero + std::cmp::Eq + num_traits::One,
    P: Clone + num_traits::Zero + num_traits::One,
{
    type Output = Polynomial<I, C, P>;

    fn add(mut self, _rhs: C) -> Self::Output {
        let size = self.terms.len();
        let last = &mut self.terms[size - 1];
        if last.monomial.product.is_empty() {
            last.coefficient += _rhs;
        } else {
            self.terms.push(Term::new_constant(_rhs));
        }

        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn different_order_addition() {
        let [x, y, z]: [Polynomial<u8, u32, u32>; 3] = Polynomial::new_variables([0u8, 1u8, 2u8])
            .try_into()
            .unwrap();
        let a = x.clone() + y.clone() + z.clone() + 42;
        let b = y + x + z + 42;

        assert_eq!(a, b);
    }
}
