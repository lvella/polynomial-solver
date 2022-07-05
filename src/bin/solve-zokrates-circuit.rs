use polynomial_solver::{
    finite_field::ZkFieldWrapper,
    polynomial::{grobner_basis::reorder_vars_for_easier_gb, monomial_ordering::Grevlex, Term},
};
use std::{env, fs::File, io::BufReader};
use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::Statement::Constraint;
use zokrates_core::ir::{self, LinComb, ProgEnum};
use zokrates_field::Field;

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

type Poly<C> = polynomial_solver::polynomial::Polynomial<Grevlex, usize, C, i32>;

fn to_poly<T: Field>(lin: LinComb<T>) -> Poly<ZkFieldWrapper<T>> {
    let mut terms = Vec::new();

    for (var, coeff) in lin.0 {
        let term = if var == FlatVariable::one() {
            Term::new_constant(ZkFieldWrapper(coeff))
        } else {
            Term::new(ZkFieldWrapper(coeff), var.id(), 1)
        };
        terms.push(term);
    }

    Poly::from_terms(terms)
}

fn solve<T: Field, I: Iterator<Item = ir::Statement<T>>>(ir_prog: ir::ProgIterator<T, I>) {
    let prime = ZkFieldWrapper::<T>::get_prime();
    println!("Field type: {}", std::any::type_name::<T>());
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

    let gb = polynomial_solver::polynomial::signature_basis::grobner_basis(poly_set);
    for p in gb.iter() {
        println!("  {}", p);
    }
    println!("Size of the Gröbner Basis: {} polynomials.", gb.len());
}
