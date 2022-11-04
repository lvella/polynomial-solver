//! Print sets of polynomials in CoCoA CAS system format.

use std::{fmt::Display, io::Write};

use itertools::Itertools;

use super::{monomial_ordering::Ordering, CommutativeRing, Exponent, Id, Polynomial};

/// Sets the polynomial ring using a finite prime field.
pub fn set_prime_field_poly_ring<O: Ordering>(
    _ordering: O,
    dest: &mut impl Write,
    prime: rug::Integer,
    mut var_ids: Vec<impl Id>,
) -> std::io::Result<()> {
    // Sort from largest to smallest, so that the CoCoA ordering matches ours.
    var_ids.sort_unstable_by(|a, b| b.cmp(a));
    writeln!(
        dest,
        "use S ::= ZZ/({})[{}], {};",
        prime,
        var_ids
            .into_iter()
            .format_with(", ", |id, display| display(&format_args!(
                "x{}",
                id.to_idx()
            ))),
        O::cocoa_name()
    )?;

    Ok(())
}

/// Assigns a list of polynomials to a variable.
pub fn list_of_polys<
    'a,
    O: Ordering + 'a,
    I: Id + 'a,
    R: CommutativeRing + Display + 'a,
    E: Exponent + Display + 'a,
>(
    dest: &mut impl Write,
    var_name: &str,
    polynomials: impl IntoIterator<Item = &'a Polynomial<O, I, R, E>>,
) -> std::io::Result<()> {
    writeln!(
        dest,
        "{} := [{}];",
        var_name,
        polynomials.into_iter().format(",\n")
    )?;

    Ok(())
}
