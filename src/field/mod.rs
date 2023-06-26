use std::ops::MulAssign;

#[cfg(feature = "arbitrary_size_field")]
pub mod arbitrary_size;
pub mod fixed_size;

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
