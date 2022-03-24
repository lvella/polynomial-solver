// I don't know what is the format of this benchmark.txt file found at
// https://web.archive.org/web/20201202185136/http://www.cecm.sfu.ca/~rpearcea/mgb.html
// but it is easy enough to parse.

use polynomial_solver::{finite_field::ThreadPrimeField, polynomial::monomial_ordering::Grevlex};

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;

type Poly = polynomial_solver::polynomial::Polynomial<Grevlex, u32, ThreadPrimeField, u32>;

fn main() -> Result<(), String> {
    ThreadPrimeField::set_prime(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse::<rug::Integer>()
            .unwrap(),
    )
    .unwrap();

    let filename = std::env::args()
        .skip(1)
        .next()
        .ok_or_else(|| "Missing benchmark file.")?;

    let string = std::fs::read_to_string(filename).expect("cannot read file");
    let systems: Vec<Vec<Poly>> = parser::parse(&string);

    for system in systems {
        println!("\n\nSystem:");
        for p in system.iter() {
            println!("  : {}", p);
        }

        println!("\nGröbner Basis:");
        let gb =
            polynomial_solver::polynomial::grobner_basis::grobner_basis(&mut system.into_iter());
        for p in gb {
            println!("  : {}", p);
        }
    }

    Ok(())
}
