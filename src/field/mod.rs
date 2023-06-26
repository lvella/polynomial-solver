use std::ops::MulAssign;

use rug::Complete;

pub mod fixed_size;
pub mod thread_prime;

pub trait CommutativeRing:
    core::fmt::Debug
    + PartialEq
    + Clone
    + std::ops::AddAssign
    + std::ops::SubAssign
    + for<'a> MulAssign<&'a Self>
    + num_traits::Zero
    + num_traits::One
{
}

pub trait Field
where
    Self: CommutativeRing
        + for<'a> std::ops::Mul<&'a Self, Output = Self>
        + num_traits::ops::inv::Inv<Output = Self>,
{
    /// Calculate elimination factor, so that self - factor*rhs = 0, and rhs_inv = 1/rhs.
    fn elimination_factor(self, rhs_inv: &Self) -> Self {
        let mut factor = Self::zero();
        factor -= self * rhs_inv;
        factor
    }
}

pub trait FiniteField: Field {
    fn get_order() -> rug::Integer;
}

pub trait PrimeField: FiniteField {}

fn mod_display(
    value: &rug::Integer,
    order: &rug::Integer,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let halfway = (order / 2u8).complete();

    if value > &halfway {
        std::fmt::Display::fmt(&(value - order).complete(), f)
    } else {
        std::fmt::Display::fmt(&value, f)
    }
}
