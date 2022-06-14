// I don't know what is the format of this benchmark.txt file found at
// https://web.archive.org/web/20201202185136/http://www.cecm.sfu.ca/~rpearcea/mgb.html
// but it is easy enough to parse.

use polynomial_solver::{finite_field::ThreadPrimeField, polynomial::monomial_ordering::Grevlex};

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod parser;

type Poly = polynomial_solver::polynomial::Polynomial<Grevlex, u32, ThreadPrimeField, i32>;

fn main() -> Result<(), String> {
    ThreadPrimeField::set_prime(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            .parse::<rug::Integer>()
            .unwrap(),
    )
    .unwrap();

    let mut args = std::env::args().skip(1);
    let filename = args.next().ok_or_else(|| "Missing benchmark file.")?;
    let indices = args
        .map(|x| {
            x.parse::<usize>()
                .map_err(|err| format!("Failed to parce index: {}", err))
        })
        .collect::<Result<Vec<_>, _>>()?;

    let string = std::fs::read_to_string(filename).expect("cannot read file");
    let mut systems: Vec<Vec<Poly>> = parser::parse(&string)?;

    if !indices.is_empty() {
        let filtered = indices
            .into_iter()
            .map(|idx| systems.get_mut(idx).map(|s| std::mem::take(s)))
            .collect::<Option<Vec<_>>>()
            .ok_or(format!(
                "Index too large, benchmark file only has {} systems.",
                systems.len()
            ))?;

        systems = filtered;
    }

    for system in systems {
        println!("\n\nSystem:");
        for p in system.iter() {
            println!("  : {}", p);
        }

        println!("\nGröbner Basis:");
        let gb =
            polynomial_solver::polynomial::signature_basis::grobner_basis(&mut system.into_iter());
        for p in gb {
            println!("  : {}", p);
        }
    }

    Ok(())
}
