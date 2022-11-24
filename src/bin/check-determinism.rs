#![feature(array_zip)]

use std::{collections::HashMap, fs::File};

use clap::Parser;
use itertools::Itertools;
use polynomial_solver::{
    finite_field::{FiniteField, ZkFieldWrapper},
    polynomial::Term,
};
use r1cs_file::{FieldElement, R1csFile};
use rug::{integer::Order, Integer};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field as ZkField};

/// Given a zero-knowledge circuit in R1CS format, try to determine if the circuit is deterministic
/// or not.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input R1CS file
    r1cs_file: String,
}

fn main() -> std::io::Result<()> {
    let args = Args::parse();

    // Load R1CS from file. Parameter 32 is the field size, in bytes.
    //
    // Increase it if ever needed.
    const FS: usize = 32;
    let r1cs = R1csFile::<FS>::read(File::open(args.r1cs_file)?)?;

    // This can be improved with a fixed size field type where prime is set per
    // thread, but for now, we only support a fixed set of primes.
    let prime = Integer::from_digits(r1cs.header.prime.as_bytes(), Order::Lsf);

    println!(
        "{}",
        match if ZkFieldWrapper::<Bn128Field>::get_order() == prime {
            is_deterministic::<Bn128Field, FS>(r1cs)
        } else if ZkFieldWrapper::<Bls12_381Field>::get_order() == prime {
            is_deterministic::<Bls12_381Field, FS>(r1cs)
        } else if ZkFieldWrapper::<Bls12_377Field>::get_order() == prime {
            is_deterministic::<Bls12_377Field, FS>(r1cs)
        } else if ZkFieldWrapper::<Bw6_761Field>::get_order() == prime {
            is_deterministic::<Bw6_761Field, FS>(r1cs)
        } else {
            panic!(concat!(
                "Prime field used is not supported.\n",
                "TODO: implement a generic, fixed size, large prime field."
            ));
        } {
            Conclusion::Deterministic => "DETERMINISTIC",
            //Conclusion::NonDeterministic => "NON DETERMINISTIC",
            Conclusion::Unknown => "UNKNOWN",
        }
    );

    Ok(())
}

type Poly<F> = polynomial_solver::polynomial::Polynomial<
    polynomial_solver::polynomial::monomial_ordering::Grevlex,
    u32,
    ZkFieldWrapper<F>,
    i32,
>;

/// Converts r1cs_file::FieldElement to the field type we are using.
fn to_f<F: ZkField, const FS: usize>(num: &FieldElement<FS>) -> ZkFieldWrapper<F> {
    ZkFieldWrapper(F::from_byte_vector(num.to_vec()))
}

enum Conclusion {
    Deterministic,
    //NonDeterministic
    Unknown,
}

fn is_deterministic<F: ZkField, const FS: usize>(r1cs: R1csFile<FS>) -> Conclusion {
    if r1cs.header.n_pub_out == 0 {
        println!("Has no public outputs, so this is certainly deterministic.");
        return Conclusion::Deterministic;
    }

    // We will encode the same circuit twice, lets call "even" and "odd"
    // systems. Each has its own set of variables, except for the input
    // variables which are shared. The following will map the wires from the
    // R1CS file to a pair of variable IDs, one for each of the even and odd
    // systems.
    let mut wire_map = HashMap::new();

    // Build the polynomial constraint for the ONE signal, which has id 0. This
    // will be automatically simplified as the first step of Gröbner Basis as
    // each polynomial is processed.
    let mut poly_set = vec![Poly::<F>::new_var(0) - Poly::<F>::one()];
    wire_map.insert(0u32, (0u32, 0u32));

    let mut var_id_gen = 1..;

    // For each of public output, we generate 3 variables: 2 for the even and
    // odd constraint systems, and one to write the constraint that says they
    // should be different from each other. This is what connects the even and
    // odd systems and ensures that, if UNSAT, the circuit is deterministic
    // (i.e., for the same inputs, it is not possible to have 2 different
    // outputs).
    //
    // TODO: maybe this should be one huge polynomial constraint, multiplying
    // all the non-equal encodings together.
    for i in 0..r1cs.header.n_pub_out {
        let out_wire = 1 + i;
        let even = var_id_gen.next().unwrap();
        let odd = var_id_gen.next().unwrap();
        wire_map.insert(out_wire, (even, odd));

        // We need an extra variable to encode a negative constraint.
        let extra = var_id_gen.next().unwrap();
        poly_set
            .push(Poly::new_var(extra) * (Poly::new_var(even) - Poly::new_var(odd)) - Poly::one());
    }

    // The input wires are shared between even and odd systems:
    for i in 0..(r1cs.header.n_pub_in + r1cs.header.n_prvt_in) {
        let in_wire = 1 + r1cs.header.n_pub_out + i;
        let var = var_id_gen.next().unwrap();
        wire_map.insert(in_wire, (var, var));
    }

    // For every other wire, we generate variables as needed:
    let mut get_vars = |wire| {
        *wire_map
            .entry(wire)
            .or_insert_with(|| var_id_gen.next_tuple().unwrap())
    };

    // Add each constraint twice, once with even variables, another with odd
    // variables. If even and odd constraints ends up identical, Gröbner Basis
    // will immediately reduce one of them to zero, so there is no problem.
    for constraint in r1cs.constraints.0 {
        let [a, b, c] = [constraint.0, constraint.1, constraint.2].map(|terms| {
            let (even, odd) = terms
                .into_iter()
                .map(|(coef, wire)| {
                    let coef = to_f::<F, FS>(&coef);
                    let (even_var, odd_var) = get_vars(wire);
                    (
                        Term::new(coef.clone(), even_var, 1),
                        Term::new(coef, odd_var, 1),
                    )
                })
                .unzip();
            [Poly::<F>::from_terms(even), Poly::<F>::from_terms(odd)]
        });

        let quad = a.zip(b).map(|(a, b)| a * b);
        let new_polys = quad.zip(c).map(|(quad, c)| quad - c);
        poly_set.extend(new_polys);
    }

    let gb = polynomial_solver::polynomial::signature_basis::grobner_basis(poly_set);

    // If we have a non-zero constant polynomial in GB, the system is UNSAT:
    if gb.into_iter().any(|p| p.is_constant() && !p.is_zero()) {
        Conclusion::Deterministic
    } else {
        Conclusion::Unknown
    }
}
