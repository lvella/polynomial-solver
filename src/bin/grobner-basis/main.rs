mod maple_like;

use clap::{command, ArgGroup, Parser};
use mimalloc::MiMalloc;
use polynomial_solver::{
    finite_field::{FiniteField, U32PrimeField, ZkFieldWrapper},
    polynomial::{
        cocoa_print, monomial_ordering::Grevlex, signature_basis::make_dense_variable_set, Term,
    },
};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use std::{
    fmt::Display,
    fs::File,
    io::{BufReader, Write},
    time::Instant,
};
use zokrates_core::flat_absy::FlatVariable;
use zokrates_core::ir::Statement::Constraint;
use zokrates_core::ir::{self, LinComb, ProgEnum};
use zokrates_field::Field as ZkField;

type Poly<F> = polynomial_solver::polynomial::Polynomial<Grevlex, u32, F, i32>;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

/// Computes the Gröbner Basis of a polynomial system.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
#[command(group(
    ArgGroup::new("input")
        .required(true)
        .args(["maple_file", "zokrates_file"]),
))]
struct Args {
    /// Read polynomial systems from Maple-like file
    #[arg(short, long, group = "input")]
    maple_file: Option<String>,

    /// Specify which of the systems in the Maple-like file to process, indexed
    /// from 0
    #[arg(short = 'i', long, value_name = "INDEX")]
    system_index: Vec<usize>,

    /// Read polynomial system from given ZoKrates binary file
    #[arg(short, long, group = "input", conflicts_with = "system_index")]
    zokrates_file: Option<String>,

    /// Randomize the order of polynomials before computing the Gröbner Basis
    #[arg(short, long)]
    randomize: bool,

    /// Outputs a CoCoA 5 verification script to a file
    #[arg(short, long)]
    verification_output: Option<String>,
}

fn main() -> Result<(), String> {
    let args = Args::parse();

    if let Some(zk_file) = &args.zokrates_file {
        let file = File::open(&zk_file)
            .map_err(|why| format!("Could not open file \"{}\": {}", zk_file, why))?;

        match ProgEnum::deserialize(&mut BufReader::new(file))? {
            ProgEnum::Bls12_381Program(a) => zok_solve(a, &args),
            ProgEnum::Bn128Program(a) => zok_solve(a, &args),
            ProgEnum::Bls12_377Program(a) => zok_solve(a, &args),
            ProgEnum::Bw6_761Program(a) => zok_solve(a, &args),
        }
    } else if let Some(maple_file) = &args.maple_file {
        // Field to use for systems loaded from maple-like file:
        type Field = U32PrimeField<2147483647>; // 2**31 - 1

        // Load polynomial systems from file and filter the provided indices.
        let systems = {
            let unparsed_contents = std::fs::read_to_string(maple_file)
                .map_err(|why| format!("Could not read file \"{}\": {}", maple_file, why))?;
            let mut systems: Vec<Vec<Poly<Field>>> =
                maple_like::parse_maple_like(&unparsed_contents)?;

            if !args.system_index.is_empty() {
                let assemble = args
                    .system_index
                    .into_iter()
                    .map(|idx| systems.get_mut(idx).map(|s| (idx, std::mem::take(s))))
                    .collect::<Option<Vec<_>>>();
                match assemble {
                    Some(a) => a,
                    None => {
                        println!(
                            "Index too large, benchmark file only has {} systems.",
                            systems.len()
                        );
                        return Err("Wrong index provided.".to_string());
                    }
                }
            } else {
                println!(
                    "No system index specified, using all the {} systems provided.",
                    systems.len()
                );
                systems.into_iter().enumerate().collect()
            }
        };

        for (idx, system) in systems {
            println!("Solving system index {idx}");
            solve(system, args.randomize, &args.verification_output);
        }
    }

    Ok(())
}

fn zok_solve<T: ZkField, I: Iterator<Item = ir::Statement<T>>>(
    ir_prog: ir::ProgIterator<T, I>,
    args: &Args,
) {
    fn to_poly<T: ZkField>(lin: LinComb<T>) -> Poly<ZkFieldWrapper<T>> {
        let mut terms = Vec::new();

        for (var, coeff) in lin.0 {
            let term = if var == FlatVariable::one() {
                Term::new_constant(ZkFieldWrapper(coeff))
            } else {
                Term::new(ZkFieldWrapper(coeff), var.id() as u32, 1)
            };
            terms.push(term);
        }

        Poly::from_terms(terms)
    }

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

    solve(poly_set, args.randomize, &args.verification_output)
}

fn solve<T: FiniteField + Display>(
    mut poly_set: Vec<Poly<T>>,
    randomize: bool,
    verification_output: &Option<String>,
) {
    let prime = T::get_order();
    println!("Field type: {}", std::any::type_name::<T>());
    println!("Prime number: {}", prime);

    let mut cocoa5_file = verification_output
        .as_ref()
        .map(|filename| File::create(filename).unwrap());

    println!("\nVariables renamed to to:");
    let mut var_ids = Vec::new();
    let var_map = make_dense_variable_set(&mut poly_set);
    for (from, to) in var_map {
        println!("{} → {}", from, to);
        var_ids.push(to as u32);
    }

    println!("Set of polynomials constrained to 0:");
    for p in poly_set.iter() {
        println!("  {}", p);
    }

    if let Some(cocoa5_file) = &mut cocoa5_file {
        cocoa_print::set_prime_field_poly_ring(Grevlex, cocoa5_file, prime, var_ids).unwrap();
        cocoa_print::list_of_polys(cocoa5_file, "original", poly_set.iter()).unwrap();
    }

    // The algorithm performance depends on the order the polynomials are given
    // in the input. From my tests, sorting makes it run much faster.
    if !randomize {
        poly_set.sort_unstable();
    } else {
        let seed = rand::random();
        println!("Rng seed: {}", seed);
        let mut rng: StdRng = SeedableRng::seed_from_u64(seed);
        poly_set.shuffle(&mut rng);
    }

    let start = Instant::now();
    let gb = polynomial_solver::polynomial::signature_basis::grobner_basis(poly_set);
    let duration = start.elapsed();

    println!("Size of the Gröbner Basis: {} polynomials.", gb.len());

    if let Some(cocoa5_file) = &mut cocoa5_file {
        cocoa_print::list_of_polys(cocoa5_file, "gb", gb.iter()).unwrap();

        // Tests if the grobner basis are the same.
        write!(
            cocoa5_file,
            r#"
I_orig := ideal(original);

LTI_orig := LT(I_orig);
LTI_mine := ideal([LT(p) | p in gb]);
is_a_gb := LTI_orig = LTI_mine;

println "Was the ideal preserved? ", I_orig = ideal(gb);
println "Is the new set a Gröbner Basis? ", is_a_gb;

if not(is_a_gb) then
    GBI_orig := ReducedGBasis(LTI_orig);
    GBI_mine := ReducedGBasis(LTI_mine);
    isect := intersection(GBI_orig, GBI_mine);

    println "What they have I don't: ", diff(GBI_orig, isect);
    println "What I have they don't: ", diff(GBI_mine, isect);
endif;
"#
        )
        .unwrap();

        println!("CoCoA 5 verification file written.");
    }
    println!(
        "### Gröbner Base calculation time: {:.} s",
        duration.as_secs_f64()
    );
}
