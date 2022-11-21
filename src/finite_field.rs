use crate::polynomial::{self, division::Field};

use rug::{self, Complete};
use std::{cell::RefCell, fmt::Display, num::ParseIntError, str::FromStr};
use zokrates_field::Field as ZkField;

use crate::polynomial::CommutativeRing;

pub trait FiniteField: polynomial::division::Field {
    fn get_order() -> rug::Integer;
}

pub trait PrimeField: FiniteField {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ThreadPrimeField(rug::Integer);

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
            self.0 %= p;
            if self.0 < 0 {
                self.0 += p
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
        self.0.fmt(f)
    }
}

impl<T> From<T> for ThreadPrimeField
where
    rug::Integer: From<T>,
{
    fn from(value: T) -> Self {
        let mut v = ThreadPrimeField(rug::Integer::from(value));
        v.normalize();
        v
    }
}

impl FromStr for ThreadPrimeField {
    type Err = <rug::Integer as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut result = ThreadPrimeField(s.parse()?);
        result.normalize();

        Ok(result)
    }
}

impl std::ops::Add for ThreadPrimeField {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let mut r = Self(self.0 + rhs.0);

        r.normalize();
        r
    }
}

impl std::ops::Mul for ThreadPrimeField {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        let mut r = Self(self.0 * rhs.0);
        r.normalize();
        r
    }
}

impl std::ops::Mul<&Self> for ThreadPrimeField {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self {
        let mut r = Self(self.0 * &rhs.0);
        r.normalize();
        r
    }
}

impl std::ops::AddAssign for ThreadPrimeField {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.normalize();
    }
}

impl std::ops::SubAssign for ThreadPrimeField {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
        self.normalize();
    }
}

impl std::ops::MulAssign<&Self> for ThreadPrimeField {
    fn mul_assign(&mut self, rhs: &Self) {
        self.0 *= &rhs.0;
        self.normalize();
    }
}

impl num_traits::pow::Pow<u32> for ThreadPrimeField {
    type Output = Self;

    fn pow(mut self, rhs: u32) -> Self {
        Self::PRIME.with(|prime| {
            self.0
                .pow_mod_mut(&rug::Integer::from(rhs), &*prime.borrow())
                .unwrap();
            self
        })
    }
}

impl num_traits::Zero for ThreadPrimeField {
    fn zero() -> Self {
        ThreadPrimeField(rug::Integer::from(0))
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl num_traits::One for ThreadPrimeField {
    fn one() -> Self {
        ThreadPrimeField(rug::Integer::from(1))
    }
}

impl num_traits::ops::inv::Inv for ThreadPrimeField {
    type Output = Self;

    fn inv(self) -> Self {
        Self(Self::PRIME.with(|prime| self.0.invert(&*prime.borrow()).unwrap()))
    }
}

impl CommutativeRing for ThreadPrimeField {}

impl Field for ThreadPrimeField {}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZkFieldWrapper<T>(pub T);

impl<T: ZkField> ZkFieldWrapper<T> {
    pub fn to_rug(&self) -> rug::Integer {
        rug::Integer::from_digits(&self.0.to_byte_vector()[..], rug::integer::Order::Lsf)
    }
}

impl<T: ZkField> FiniteField for ZkFieldWrapper<T> {
    fn get_order() -> rug::Integer {
        ZkFieldWrapper(T::max_value()).to_rug() + 1u8
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
        let prime = Self::get_order();
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct U32PrimeField<const PRIME: u32>(u32);

impl<const PRIME: u32> U32PrimeField<PRIME> {
    pub fn new(value: u32) -> Self {
        Self(value % PRIME)
    }

    pub fn into_inner(self) -> u32 {
        self.0
    }
}

impl<const PRIME: u32> std::ops::Add for U32PrimeField<PRIME> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(((self.0 as u64 + rhs.0 as u64) % PRIME as u64) as u32)
    }
}

impl<const PRIME: u32> std::ops::Mul for U32PrimeField<PRIME> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(((self.0 as u64 * rhs.0 as u64) % PRIME as u64) as u32)
    }
}

impl<'a, const PRIME: u32> std::ops::Mul<&'a U32PrimeField<PRIME>> for U32PrimeField<PRIME> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self {
        self * (*rhs)
    }
}

impl<const PRIME: u32> std::ops::AddAssign for U32PrimeField<PRIME> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const PRIME: u32> std::ops::SubAssign for U32PrimeField<PRIME> {
    fn sub_assign(&mut self, rhs: Self) {
        *self += Self(PRIME - rhs.0);
    }
}

impl<'a, const PRIME: u32> std::ops::MulAssign<&'a U32PrimeField<PRIME>> for U32PrimeField<PRIME> {
    fn mul_assign(&mut self, rhs: &Self) {
        *self = *self * rhs;
    }
}

impl<const PRIME: u32> num_traits::Pow<u32> for U32PrimeField<PRIME> {
    type Output = Self;

    fn pow(mut self, mut rhs: u32) -> Self {
        let mut result = Self(1);

        while rhs != 0 {
            if rhs & 1 == 1 {
                result *= &self;
            }
            rhs >>= 1;
            self = self * self;
        }

        result
    }
}

impl<const PRIME: u32> FromStr for U32PrimeField<PRIME> {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        s.parse::<u32>().map(|val| Self::new(val))
    }
}

impl<const PRIME: u32> std::fmt::Display for U32PrimeField<PRIME> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<const PRIME: u32> num_traits::Inv for U32PrimeField<PRIME> {
    type Output = Self;

    /// Calculates the inverse of the value.
    ///
    /// Straight from wikipedia:
    /// https://en.wikipedia.org/w/index.php?title=Extended_Euclidean_algorithm&oldid=1113184203#Modular_integers
    fn inv(self) -> Self {
        assert!(self.0 != 0 && self.0 < PRIME);
        let mut t = 0;
        let mut newt = 1;
        let mut r = PRIME as i64;
        let mut newr = self.0 as i64;

        while newr != 0 {
            let quot = r / newr;
            (t, newt) = (newt, t - quot * newt);
            (r, newr) = (newr, r - quot * newr);
        }

        if t < 0 {
            t += PRIME as i64;
        }

        assert!(t > 0 && t < PRIME as i64);
        Self(t as u32)
    }
}

impl<const PRIME: u32> num_traits::One for U32PrimeField<PRIME> {
    fn one() -> Self {
        Self(1)
    }
}

impl<const PRIME: u32> num_traits::Zero for U32PrimeField<PRIME> {
    fn zero() -> Self {
        Self(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl<const PRIME: u32> CommutativeRing for U32PrimeField<PRIME> {}
impl<const PRIME: u32> Field for U32PrimeField<PRIME> {}
impl<const PRIME: u32> FiniteField for U32PrimeField<PRIME> {
    fn get_order() -> rug::Integer {
        rug::Integer::from(PRIME)
    }
}

#[cfg(test)]
mod tests {
    use num_traits::{Inv, One, Pow};
    use rand::{rngs::StdRng, Rng, SeedableRng};

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

    #[test]
    fn u32_field_ops() {
        const PRIME: u32 = 2147483647;
        type Field = U32PrimeField<PRIME>;
        let mut rng = StdRng::seed_from_u64(42);

        for _i in 0..1000 {
            let a = rng.gen_range(0..PRIME);
            let b = rng.gen_range(0..PRIME);

            // exponentiation
            let tested = rug::Integer::from(Field::new(a).pow(b).into_inner());
            let control = rug::Integer::from(a)
                .pow_mod(&b.into(), &PRIME.into())
                .unwrap();
            assert_eq!(tested, control);

            // inverse
            for v in [a, b] {
                let v = Field::new(v);
                let inv = v.inv();
                let test = v * inv;
                assert!(test.is_one());
            }
        }
    }
}
