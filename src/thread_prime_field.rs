use crate::polynomial::{division::InvertibleCoefficient, grobner_basis as gb};

use rug;
use std::{cell::RefCell, fmt::Display};

use crate::polynomial::Coefficient;

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

impl Coefficient for ThreadPrimeField {}

impl InvertibleCoefficient for ThreadPrimeField {}

#[cfg(test)]
mod tests {
    use num_traits::{Inv, Pow};

    use crate::polynomial::{self, Polynomial};

    use super::*;

    type GFPoly = Polynomial<polynomial::monomial_ordering::Lex, u8, ThreadPrimeField, u32>;

    fn F<T>(v: T) -> ThreadPrimeField
    where
        ThreadPrimeField: From<T>,
    {
        ThreadPrimeField::from(v)
    }

    #[test]
    fn big_grobner_basis() {
        ThreadPrimeField::set_prime(13u8);

        let [z, y, x]: [GFPoly; 3] = GFPoly::new_variables([0, 1, 2]).try_into().unwrap();
        let input = [
            &x.clone().pow(3u8) * F(4u8)
                + x.clone().pow(2u8) * (&y.clone().pow(2u8) * F(2u8))
                + &x.clone() * F(12u8)
                - y.clone()
                - F(5u8),
            y.clone().pow(3u8)
                - &x.clone().pow(2u8) * F(3u8)
                - x.clone() * (&y.clone().pow(3u8) * F(7u8))
                - z,
        ];

        let gb = gb::grobner_basis(input.into_iter());
        for e in gb {
            let inv = e.get_terms()[0].get_coefficient().clone().inv();
            println!("{}", &*e * inv);
        }
    }
}
