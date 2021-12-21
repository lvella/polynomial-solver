use std::{
    fmt::Display,
    ops::{Add, AddAssign, Div, Mul, Rem, Sub, SubAssign},
};

use num_traits::{Num, One, SaturatingSub, Unsigned, Zero};
use rug::{self, Assign};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BigUnsigned {
    value: rug::Integer,
}

impl BigUnsigned {
    pub fn new<T>(value: T) -> Result<Self, &'static str>
    where
        rug::Integer: From<T>,
    {
        let value = rug::Integer::from(value);
        if value >= 0 {
            Ok(Self { value })
        } else {
            Err("value must not be negative")
        }
    }
}

impl<T> From<T> for BigUnsigned
where
    rug::Integer: From<T>,
{
    fn from(v: T) -> Self {
        let value = rug::Integer::from(v);
        if value < 0 {
            panic!("value must not be negative");
        }
        Self { value }
    }
}

impl AddAssign for BigUnsigned {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value
    }
}

impl<'a> AddAssign<&'a Self> for BigUnsigned {
    fn add_assign(&mut self, rhs: &'a Self) {
        self.value += &rhs.value
    }
}

impl<'a> SubAssign<&'a Self> for BigUnsigned {
    fn sub_assign(&mut self, rhs: &'a Self) {
        self.value -= &rhs.value;
        if self.value < 0 {
            panic!("unsigned subtraction underflow");
        }
    }
}

impl SaturatingSub for BigUnsigned {
    fn saturating_sub(&self, v: &Self) -> Self {
        let mut ret = self.clone();
        ret.value -= &v.value;
        if ret.value < 0 {
            ret.value.assign(0);
        }
        ret
    }
}

impl Unsigned for BigUnsigned {}

impl Zero for BigUnsigned {
    fn zero() -> Self {
        Self {
            value: rug::Integer::from(0),
        }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl One for BigUnsigned {
    fn one() -> Self {
        Self {
            value: rug::Integer::from(1),
        }
    }
}

impl Num for BigUnsigned {
    type FromStrRadixErr = rug::integer::ParseIntegerError;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(Self {
            value: rug::Integer::from_str_radix(str, radix as i32)?,
        })
    }
}

impl Add for BigUnsigned {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self {
        self.value += rhs.value;
        self
    }
}

impl Sub for BigUnsigned {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self {
        self.value -= rhs.value;
        if self.value < 0 {
            panic!("unsigned subtraction underflow");
        }
        self
    }
}

impl Mul for BigUnsigned {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self {
        self.value *= rhs.value;
        self
    }
}

impl Div for BigUnsigned {
    type Output = Self;

    fn div(mut self, rhs: Self) -> Self {
        self.value /= rhs.value;
        self
    }
}

impl Rem for BigUnsigned {
    type Output = Self;

    fn rem(mut self, rhs: Self) -> Self {
        self.value %= rhs.value;
        self
    }
}

impl crate::polynomial::Power for BigUnsigned {}

impl Display for BigUnsigned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;

    use crate::{
        polynomial::{grobner_basis, monomial_ordering::Grevlex, Polynomial},
        thread_prime_field::ThreadPrimeField as GF,
    };

    use super::BigUnsigned;

    type BigPowerPoly = Polynomial<Grevlex, u8, GF, BigUnsigned>;

    fn big_prime() -> rug::Integer {
        "5692679106393598585927913904127626585090608726104001845670672525072835817369"
            .parse()
            .unwrap()
    }

    // The following tests uses a plain Gröbner Basis together with Fermat's Little
    // Theorem to decide if a set of polynomials equations is SAT or UNSAT.

    /// The polynomial representing Fermat's little theorem: x^p - x = 0 (mod p)
    fn fermat(id: u8) -> BigPowerPoly {
        BigPowerPoly::new_monomial_term(GF::from(1u8), id, BigUnsigned::from(big_prime()))
            - BigPowerPoly::new_monomial_term(GF::from(1u8), id, BigUnsigned::from(1u8))
    }

    /// It seems this would take many times the age of the universe to compute, so
    /// it is better to disable this test.
    #[test]
    #[ignore]
    fn huge_prime_field_sat() {
        GF::set_prime(big_prime()).unwrap();

        let [z, y, x]: [BigPowerPoly; 3] =
            BigPowerPoly::new_variables([0, 1, 2]).try_into().unwrap();

        let sat_p = x.clone().pow(5u8) + &(x.clone().pow(2u8) * y.clone()) * GF::from(785u16)
            - &z.clone().pow(3u8) * GF::from(536u16)
            + &(x.clone() * z.clone()) * GF::from(13u8)
            - z.clone().pow(2u8)
            + &x * GF::from(57u8)
            - GF::from(
                "574944840199502972987147917790544307331452874763714516398436502385615357071"
                    .parse::<rug::Integer>()
                    .unwrap(),
            );

        let input = [sat_p, fermat(0), fermat(1), fermat(2)];

        let result = grobner_basis::grobner_basis(&mut input.into_iter());

        for p in result {
            println!("{}", p);
        }
    }
}
