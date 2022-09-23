use polynomial_solver::{
    finite_field::ZkFieldWrapper,
    polynomial::{
        cocoa_print, grobner_basis::reorder_vars_for_easier_gb, monomial_ordering::Grevlex, Term,
    },
};
use rand::{rngs::StdRng, seq::SliceRandom, SeedableRng};
use std::{
    env,
    fs::File,
    io::{BufReader, Write},
};
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

    let mut cocoa5_file = File::create("verification.cocoa5").unwrap();

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
    let mut var_ids = Vec::new();
    let var_map = reorder_vars_for_easier_gb(&mut poly_set);
    for (from, to) in var_map {
        println!("{} → {}", from, to);
        var_ids.push(to);
    }

    cocoa_print::set_prime_field_poly_ring(Grevlex, &mut cocoa5_file, prime, var_ids).unwrap();

    println!("Set of polynomials constrained to 0:");
    for p in poly_set.iter() {
        println!("  {}", p);
    }

    cocoa_print::list_of_polys(&mut cocoa5_file, "original", poly_set.iter()).unwrap();

    println!("\nGröbner Basis:");

    // The algorithm performance might depend on the order the elements are
    // given in the input. From my tests with a single input, sorting makes it
    // run much faster.
    //poly_set.sort_unstable();

    ///// DEBUG: lets find out if the order is really important //
    let seed = 4268529541343527472; //rand::random();
    println!("Rng seed: {}", seed);
    let mut rng: StdRng = SeedableRng::seed_from_u64(seed);
    poly_set.shuffle(&mut rng);
    //////////////////////////////////////////////////////////////
    let gb = polynomial_solver::polynomial::signature_basis::grobner_basis(poly_set);

    println!("Size of the Gröbner Basis: {} polynomials.", gb.len());

    /*println!("===== DEBUG: Second pass in a different order =========");
    let mut gb = polynomial_solver::polynomial::signature_basis::grobner_basis(gb);
    std::fs::remove_dir_all("polys");
    std::fs::create_dir("polys").unwrap();
    for (idx, p) in gb.iter_mut().enumerate() {
        *p = std::mem::replace(p, Polynomial::zero()).normalized_by_coefs();
        let mut fd = File::create(format!("polys/{}.txt", idx)).unwrap();
        for t in p.get_terms().iter() {
            writeln!(fd, "{}", t).unwrap();
        }
    }
    println!("=======================================================");*/

    cocoa_print::list_of_polys(&mut cocoa5_file, "gb", gb.iter()).unwrap();

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

    drop(cocoa5_file);
    println!("CoCoA 5 verification file written.");

    println!("============ DEBUG =============");
    polynomial_solver::polynomial::grobner_basis::grobner_basis(&mut gb.into_iter());
    println!("================================");
}
