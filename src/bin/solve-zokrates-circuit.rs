use polynomial_solver::polynomial::division::InvertibleCoefficient;
use polynomial_solver::polynomial::grobner_basis::reorder_vars_for_easier_gb;
use polynomial_solver::polynomial::monomial_ordering::Grevlex;
use polynomial_solver::polynomial::{Coefficient, Term};
use rug::Complete;
use std::{env, fs::File, io::BufReader};
use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::Statement::Constraint;
use zokrates_core::ir::{self, LinComb, ProgEnum};
use zokrates_field::Field;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FieldWrapper<T>(T);

impl<T: Field> std::ops::Add for FieldWrapper<T> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self(self.0.add(rhs.0))
    }
}

impl<T: Field> std::ops::Mul for FieldWrapper<T> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        Self(self.0.mul(rhs.0))
    }
}

impl<'a, T: Field> std::ops::Mul<&'a FieldWrapper<T>> for FieldWrapper<T> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self {
        Self(self.0.mul(&rhs.0))
    }
}

impl<T: Field> std::ops::AddAssign for FieldWrapper<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.0 = std::mem::take(&mut self.0) + rhs.0;
    }
}

impl<T: Field> std::ops::SubAssign for FieldWrapper<T> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 = std::mem::take(&mut self.0) - rhs.0
    }
}

impl<'a, T: Field> std::ops::MulAssign<&'a FieldWrapper<T>> for FieldWrapper<T> {
    fn mul_assign(&mut self, rhs: &'a FieldWrapper<T>) {
        self.0 = std::mem::take(&mut self.0) * &rhs.0
    }
}

impl<T: Field> std::fmt::Display for FieldWrapper<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let prime = to_rug(&T::max_value()) + 1u8;
        let halfway = (&prime / 2u8).complete();
        let val = to_rug(&self.0);

        if val > halfway {
            std::fmt::Display::fmt(&(val - prime), f)
        } else {
            std::fmt::Display::fmt(&val, f)
        }
    }
}

impl<T: Field> num_traits::Inv for FieldWrapper<T> {
    type Output = Self;

    fn inv(self) -> Self {
        Self(self.0.inverse_mul().unwrap())
    }
}

impl<T: Field> num_traits::One for FieldWrapper<T> {
    fn one() -> Self {
        Self(T::one())
    }
}

impl<T: Field> num_traits::Zero for FieldWrapper<T> {
    fn zero() -> Self {
        Self(T::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<T: Field> Coefficient for FieldWrapper<T> {}
impl<T: Field> InvertibleCoefficient for FieldWrapper<T> {}

fn main() -> Result<(), String> {
    let filename = env::args()
        .skip(1)
        .next()
        .ok_or_else(|| "Missing ZoKrates circuit file.")?;

    let file =
        File::open(&filename).map_err(|why| format!("Could not open {}: {}", filename, why))?;

    match ProgEnum::deserialize(&mut BufReader::new(file))? {
        ProgEnum::Bls12_381Program(a) => solve(a),
        ProgEnum::Bn128Program(a) => solve(a),
        ProgEnum::Bls12_377Program(a) => solve(a),
        ProgEnum::Bw6_761Program(a) => solve(a),
    }

    Ok(())
}

fn to_rug(v: &impl Field) -> rug::Integer {
    rug::Integer::from_digits(&v.to_byte_vector()[..], rug::integer::Order::Lsf)
}

type Poly<C> = polynomial_solver::polynomial::Polynomial<Grevlex, usize, C, u32>;

fn to_poly<T: Field>(lin: LinComb<T>) -> Poly<FieldWrapper<T>> {
    let mut terms = Vec::new();

    for (var, coeff) in lin.0 {
        let term = if var == FlatVariable::one() {
            Term::new_constant(FieldWrapper(coeff))
        } else {
            Term::new(FieldWrapper(coeff), var.id(), 1)
        };
        terms.push(term);
    }

    Poly::from_terms(terms)
}

fn solve<T: Field, I: Iterator<Item = ir::Statement<T>>>(ir_prog: ir::ProgIterator<T, I>) {
    let prime = to_rug(&T::max_value()) + 1u8;
    println!("Prime number: {}", prime);

    let mut poly_set = Vec::new();

    for s in ir_prog.statements.into_iter() {
        if let Constraint(quad, lin, _) = s {
            let ql = to_poly(quad.left);
            let qr = to_poly(quad.right);
            let rhs = to_poly(lin);

            let p = ql * qr - rhs;
            poly_set.push(p);
        }
    }

    println!("\nVariables reordered to:");
    let var_map = reorder_vars_for_easier_gb(&mut poly_set);
    for (from, to) in var_map {
        println!("{} → {}", from, to);
    }

    println!("Set of polynomials constrained to 0:");
    for p in poly_set.iter() {
        println!("  {}", p);
    }

    println!("\nGröbner Basis:");

    let gb = polynomial_solver::polynomial::grobner_basis::grobner_basis(&mut poly_set.into_iter());
    for p in gb.iter() {
        println!("  {}", p);
    }
    println!("Size of the Gröbner Basis: {} polynomials.", gb.len());
}
