use crate::polynomial::{Coefficient, Id, Monomial, Polynomial, Power};

/// Initial term of the polynomial
fn it<I, C, P>(p: &Polynomial<I, C, P>) -> Option<&Monomial<I, P>>
where
    I: Id,
    C: Coefficient,
    P: Power,
{
    Some(p.get_terms().get(0)?.get_monomial())
}

/// Reduce one polynomial with respect to another.
/// This is kind of a multi-variable division, and the return is the remainder.
fn reduce<I, C, P>(
    p: Polynomial<I, C, P>,
    reference: &Polynomial<I, C, P>,
) -> Option<Polynomial<I, C, P>>
where
    I: Id,
    C: Coefficient,
    P: Power,
{
    let factor_to_eliminate = it(&p)?.clone().whole_division(it(reference)?);

    // TODO: to be continued.
    None
}
