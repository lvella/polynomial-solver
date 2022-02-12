use crate::polynomial::Polynomial;

pub struct FactorsIter<O, I, C, P> {
    p: Polynomial<O, I, C, P>, // placeholder
}

impl<O, I, C, P> Iterator for FactorsIter<O, I, C, P> {
    // we will be counting with usize
    type Item = Polynomial<O, I, C, P>;

    // next() is the only required method
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

/// Factorize a polynomial over finite_fields into its distinct irreducible factors.
pub fn finite_field_factorize<O, I, C, P>(poly: Polynomial<O, I, C, P>) -> FactorsIter<O, I, C, P> {
    todo!("factorization not implemented");
}
