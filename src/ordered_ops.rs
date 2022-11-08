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

/// Implements ordered sum, when sum depends on summing two ordered sequence.
/// Used to multiply two monomials or sum two polynomials.
pub fn sum<T>(
    mut a_iter: impl Iterator<Item = T>,
    mut b_iter: impl Iterator<Item = T>,
    cmp: impl Fn(&T, &T) -> std::cmp::Ordering,
    op: impl Fn(T, T) -> Option<T>,
    output: &mut Vec<T>,
) {
    let mut a = a_iter.next();
    let mut b = b_iter.next();

    loop {
        match (a, b) {
            (Some(va), Some(vb)) => match cmp(&va, &vb) {
                std::cmp::Ordering::Equal => {
                    // Do the operation
                    if let Some(r) = op(va, vb) {
                        output.push(r);
                    }
                    a = a_iter.next();
                    b = b_iter.next();
                }
                std::cmp::Ordering::Less => {
                    output.push(va);
                    a = a_iter.next();
                    b = Some(vb);
                }
                std::cmp::Ordering::Greater => {
                    output.push(vb);
                    a = Some(va);
                    b = b_iter.next();
                }
            },
            (None, Some(b)) => {
                output.push(b);
                output.extend(b_iter);
                break;
            }
            (Some(a), None) => {
                output.push(a);
                output.extend(a_iter);
                break;
            }
            (None, None) => {
                break;
            }
        }
    }
}

/// Implements ordered saturated difference.
/// Used to calculate the complementing monomial in spar algorithm
pub fn saturating_sub<T, U>(
    mut a_iter: impl Iterator<Item = T>,
    mut b_iter: impl Iterator<Item = U>,
    cmp: impl Fn(&T, &U) -> std::cmp::Ordering,
    op: impl Fn(T, U) -> Option<T>,
) -> Vec<T> {
    let mut new_terms = Vec::new();

    let mut a = a_iter.next();
    let mut b = b_iter.next();

    loop {
        match (a, b) {
            (Some(va), Some(vb)) => match cmp(&va, &vb) {
                std::cmp::Ordering::Equal => {
                    // Do the operation
                    if let Some(r) = op(va, vb) {
                        new_terms.push(r);
                    }
                    a = a_iter.next();
                    b = b_iter.next();
                }
                std::cmp::Ordering::Less => {
                    new_terms.push(va);
                    a = a_iter.next();
                    b = Some(vb);
                }
                std::cmp::Ordering::Greater => {
                    a = Some(va);
                    b = b_iter.next();
                }
            },
            (Some(a), None) => {
                new_terms.push(a);
                new_terms.extend(a_iter);
                break;
            }
            _ => {
                break;
            }
        }
    }

    new_terms
}
