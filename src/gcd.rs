use num_traits::Zero;

pub fn gcd<T>(mut bigger: T, mut smaller: T) -> T
where
    T: Zero + for<'a> std::ops::Rem<&'a T, Output = T>,
{
    while !smaller.is_zero() {
        let tmp = bigger % &smaller;
        bigger = smaller;
        smaller = tmp;
    }
    bigger
}

#[cfg(test)]
mod tests {
    use num_traits::Pow;

    use super::*;
    use crate::polynomial::division::tests::{r, QPoly};

    #[test]
    fn polynomial_gcd() {
        let x = QPoly::new_monomial_term(r(1), 0, 1);

        let a = x.clone().pow(2u8) + &x.clone() * r(7) + r(6);
        let b = x.clone().pow(2u8) - &x.clone() * r(5) - r(6);

        println!("a: {}\nb: {}", a, b);

        let d = gcd(a, b).normalized_by_coefs();

        println!("gcd(a, b): {}", d);

        let expected_d = x.clone() + r(1);
        assert_eq!(d, expected_d);
    }
}
