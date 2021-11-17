/// A term of the summable sequence with total order for the key, and
/// a summable type with null value.
/// In a polynomial term, Key is the monomial, and Value is the coefficient.
/// In a monomial term, Key is the variable, and Value is the power.
pub trait Term {
    type Key;
    type Value;

    fn key(&self) -> &Self::Key;
    fn value(self) -> Self::Value;
    fn value_ref(&self) -> &Self::Value;
    fn value_ref_mut(&mut self) -> &mut Self::Value;
}

/// Implements sum, when sum depends on summing two ordered sequence.
/// Used to multiply two monomials or sum two polynomials.
pub fn ordered_sum<T, K, V, I>(lhs: I, rhs: I) -> Vec<T>
where
    I: IntoIterator<Item = T>,
    K: Ord,
    V: std::ops::AddAssign + num_traits::Zero,
    T: Term<Key = K, Value = V>,
{
    let mut new_terms = Vec::new();
    let mut a_iter = lhs.into_iter();
    let mut b_iter = rhs.into_iter();

    let remainer;
    loop {
        let a = a_iter.next();
        let b = b_iter.next();

        match (a, b) {
            (Some(mut a), Some(mut b)) => loop {
                match a.key().cmp(b.key()) {
                    std::cmp::Ordering::Equal => {
                        *a.value_ref_mut() += b.value();
                        if !a.value_ref().is_zero() {
                            new_terms.push(a);
                        }
                        break;
                    }
                    std::cmp::Ordering::Less => {
                        new_terms.push(b);
                        b = a;
                        std::mem::swap(&mut a_iter, &mut b_iter);
                    }
                    std::cmp::Ordering::Greater => {
                        new_terms.push(a);
                    }
                }

                if let Some(v) = a_iter.next() {
                    a = v;
                } else {
                    new_terms.push(b);
                    break;
                }
            },
            (None, Some(b)) => {
                remainer = b_iter;
                new_terms.push(b);
                break;
            }
            (Some(a), None) => {
                remainer = a_iter;
                new_terms.push(a);
                break;
            }
            (None, None) => {
                remainer = a_iter;
                break;
            }
        }
    }

    new_terms.extend(remainer);

    new_terms
}
