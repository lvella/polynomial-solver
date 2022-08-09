use crate::polynomial::{self, division::Field};

use rug::{self, Complete};
use std::{cell::RefCell, fmt::Display, str::FromStr};
use zokrates_field::Field as ZkField;

use crate::polynomial::CommutativeRing;

pub trait FiniteField: polynomial::division::Field {
    fn get_order() -> rug::Integer;
}

pub trait PrimeField: FiniteField {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ThreadPrimeField {
    value: rug::Integer,
}

impl ThreadPrimeField {
    thread_local! {
        static PRIME: std::cell::RefCell<rug::Integer>  = RefCell::new(rug::Integer::from(3));
    }

    /// Changing the prime when there are instances created
    /// will denormalize the values >= the new prime.
    pub fn set_prime<T>(prime: T) -> Result<(), &'static str>
    where
        rug::Integer: From<T>,
    {
        let prime = rug::Integer::from(prime);
        if let rug::integer::IsPrime::No = prime.is_probably_prime(50) {
            return Err("The number is not prime");
        }

        Self::PRIME.with(|p| *p.borrow_mut() = prime);

        Ok(())
    }

    fn normalize(&mut self) {
        Self::PRIME.with(|prime| {
            let p = &*prime.borrow();
            self.value %= p;
            if self.value < 0 {
                self.value += p
            }
        })
    }
}

impl FiniteField for ThreadPrimeField {
    fn get_order() -> rug::Integer {
        Self::PRIME.with(|prime| prime.borrow().clone())
    }
}

impl PrimeField for ThreadPrimeField {}

impl Display for ThreadPrimeField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.value.fmt(f)
    }
}

impl<T> From<T> for ThreadPrimeField
where
    rug::Integer: From<T>,
{
    fn from(value: T) -> Self {
        let mut v = ThreadPrimeField {
            value: rug::Integer::from(value),
        };
        v.normalize();
        v
    }
}

impl FromStr for ThreadPrimeField {
    type Err = <rug::Integer as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = ThreadPrimeField { value: s.parse()? };
        result.normalize();

        Ok(result)
    }
}

impl std::ops::Add for ThreadPrimeField {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let mut r = Self {
            value: self.value + rhs.value,
        };
        r.normalize();
        r
    }
}

impl std::ops::Mul for ThreadPrimeField {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut r = Self {
            value: self.value * rhs.value,
        };
        r.normalize();
        r
    }
}

impl std::ops::Mul<&Self> for ThreadPrimeField {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self {
        let mut r = Self {
            value: self.value * &rhs.value,
        };
        r.normalize();
        r
    }
}

impl std::ops::AddAssign for ThreadPrimeField {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        self.normalize();
    }
}

impl std::ops::SubAssign for ThreadPrimeField {
    fn sub_assign(&mut self, rhs: Self) {
        self.value -= rhs.value;
        self.normalize();
    }
}

impl std::ops::MulAssign<&Self> for ThreadPrimeField {
    fn mul_assign(&mut self, rhs: &Self) {
        self.value *= &rhs.value;
        self.normalize();
    }
}

impl num_traits::pow::Pow<u32> for ThreadPrimeField {
    type Output = Self;

    fn pow(mut self, rhs: u32) -> Self {
        Self::PRIME.with(|prime| {
            self.value
                .pow_mod_mut(&rug::Integer::from(rhs), &*prime.borrow())
                .unwrap();
            self
        })
    }
}

impl num_traits::Zero for ThreadPrimeField {
    fn zero() -> Self {
        ThreadPrimeField {
            value: rug::Integer::from(0),
        }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl num_traits::One for ThreadPrimeField {
    fn one() -> Self {
        ThreadPrimeField {
            value: rug::Integer::from(1),
        }
    }
}

impl num_traits::ops::inv::Inv for ThreadPrimeField {
    type Output = Self;

    fn inv(self) -> Self {
        Self {
            value: Self::PRIME.with(|prime| self.value.invert(&*prime.borrow()).unwrap()),
        }
    }
}

impl CommutativeRing for ThreadPrimeField {}

impl Field for ThreadPrimeField {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZkFieldWrapper<T>(pub T);

impl<T: ZkField> ZkFieldWrapper<T> {
    pub fn get_prime() -> rug::Integer {
        ZkFieldWrapper(T::max_value()).to_rug() + 1u8
    }

    pub fn to_rug(&self) -> rug::Integer {
        rug::Integer::from_digits(&self.0.to_byte_vector()[..], rug::integer::Order::Lsf)
    }
}

impl<T: ZkField> std::ops::Add for ZkFieldWrapper<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0.add(rhs.0))
    }
}

impl<T: ZkField> std::ops::Mul for ZkFieldWrapper<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(self.0.mul(rhs.0))
    }
}

impl<'a, T: ZkField> std::ops::Mul<&'a ZkFieldWrapper<T>> for ZkFieldWrapper<T> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self {
        Self(self.0.mul(&rhs.0))
    }
}

impl<T: ZkField> std::ops::AddAssign for ZkFieldWrapper<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = std::mem::take(&mut self.0) + rhs.0;
    }
}

impl<T: ZkField> std::ops::SubAssign for ZkFieldWrapper<T> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = std::mem::take(&mut self.0) - rhs.0
    }
}

impl<'a, T: ZkField> std::ops::MulAssign<&'a ZkFieldWrapper<T>> for ZkFieldWrapper<T> {
    fn mul_assign(&mut self, rhs: &'a ZkFieldWrapper<T>) {
        self.0 = std::mem::take(&mut self.0) * &rhs.0
    }
}

impl<'a, T: ZkField> num_traits::Pow<u32> for ZkFieldWrapper<T> {
    type Output = Self;

    fn pow(self, rhs: u32) -> Self {
        ZkFieldWrapper(self.0.pow(rhs as usize))
    }
}

impl<T: ZkField> FromStr for ZkFieldWrapper<T> {
    type Err = zokrates_field::FieldParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        T::try_from_dec_str(s).map(|v| ZkFieldWrapper(v))
    }
}

impl<T: ZkField> std::fmt::Display for ZkFieldWrapper<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prime = ZkFieldWrapper::<T>::get_prime();
        let halfway = (&prime / 2u8).complete();
        let val = self.to_rug();

        if val > halfway {
            std::fmt::Display::fmt(&(val - prime), f)
        } else {
            std::fmt::Display::fmt(&val, f)
        }
    }
}

impl<T: ZkField> num_traits::Inv for ZkFieldWrapper<T> {
    type Output = Self;

    fn inv(self) -> Self {
        Self(self.0.inverse_mul().unwrap())
    }
}

impl<T: ZkField> num_traits::One for ZkFieldWrapper<T> {
    fn one() -> Self {
        Self(T::one())
    }
}

impl<T: ZkField> num_traits::Zero for ZkFieldWrapper<T> {
    fn zero() -> Self {
        Self(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<T: ZkField> CommutativeRing for ZkFieldWrapper<T> {}
impl<T: ZkField> Field for ZkFieldWrapper<T> {}

#[cfg(test)]
mod tests {
    use num_traits::{Inv, Pow};

    use crate::polynomial::{self, Polynomial};

    use super::*;

    type GFPoly = Polynomial<polynomial::monomial_ordering::Lex, u8, ThreadPrimeField, u16>;

    fn gf<T>(v: T) -> ThreadPrimeField
    where
        ThreadPrimeField: From<T>,
    {
        ThreadPrimeField::from(v)
    }

    #[test]
    fn big_grobner_basis() {
        ThreadPrimeField::set_prime(13u8).unwrap();

        let [z, y, x]: [GFPoly; 3] = GFPoly::new_variables([0, 1, 2]).try_into().unwrap();
        let input = [
            &x.clone().pow(3u8) * gf(4u8)
                + x.clone().pow(2u8) * (&y.clone().pow(2u8) * gf(2u8))
                + &x.clone() * gf(12u8)
                - y.clone()
                - gf(5u8),
            y.clone().pow(3u8)
                - &x.clone().pow(2u8) * gf(3u8)
                - x.clone() * (&y.clone().pow(3u8) * gf(7u8))
                - z,
        ];

        let gb = polynomial::grobner_basis::grobner_basis(&mut input.into_iter());
        for e in gb {
            let inv = e.get_terms()[0].get_coefficient().clone().inv();
            println!("{}", &e * inv);
        }
    }
}
