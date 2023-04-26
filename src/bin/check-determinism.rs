#![feature(array_zip)]
#![feature(pointer_is_aligned)]

use std::{
    cmp::min,
    collections::HashMap,
    fs::File,
    num::NonZeroU32,
    sync::atomic::{AtomicU32, Ordering::Relaxed},
    thread::available_parallelism,
};

use clap::Parser;
use itertools::Itertools;
use nix::{
    sys::wait::{wait, WaitStatus},
    unistd::{getpid, Pid},
};
use polynomial_solver::{
    finite_field::{FiniteField, ZkFieldWrapper},
    polynomial::Term,
};
use r1cs_file::{FieldElement, R1csFile};
use rug::{integer::Order, Integer};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field as ZkField};

/// Number of outputs to constraint per process.
const N: NonZeroU32 = unsafe { NonZeroU32::new_unchecked(4) };

/// Given a zero-knowledge circuit in R1CS format, try to determine if the circuit is deterministic
/// or not.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The maximum number of worker processes to use. Default uses the value
    /// returned by std::thread::available_parallelism().
    #[arg(short, long)]
    process_count: Option<NonZeroU32>,

    /// Input R1CS file
    r1cs_file: String,

    /// Do nothing, just read and dump R1CS file
    #[arg(short, long)]
    just_dump: bool,
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
    //
    // TODO: improve this
    let prime = Integer::from_digits(r1cs.header.prime.as_bytes(), Order::Lsf);

    if args.just_dump {
        just_dump::just_dump(prime, r1cs);
        return Ok(());
    }

    let num_procs = match args.process_count.ok_or_else(|| available_parallelism()) {
        Ok(num) => num,
        Err(Ok(num)) => NonZeroU32::new(min(num.get(), u32::MAX as usize) as u32).unwrap(),
        Err(Err(e)) => {
            println!("Error: could not get available parallelism.\nPlease specify the process count explicitly.");
            return Err(e);
        }
    };

    println!(
        "{}",
        match if ZkFieldWrapper::<Bn128Field>::get_order() == prime {
            is_deterministic::<Bn128Field, FS>(num_procs, r1cs)
        } else if ZkFieldWrapper::<Bls12_381Field>::get_order() == prime {
            is_deterministic::<Bls12_381Field, FS>(num_procs, r1cs)
        } else if ZkFieldWrapper::<Bls12_377Field>::get_order() == prime {
            is_deterministic::<Bls12_377Field, FS>(num_procs, r1cs)
        } else if ZkFieldWrapper::<Bw6_761Field>::get_order() == prime {
            is_deterministic::<Bw6_761Field, FS>(num_procs, r1cs)
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

/// It would be nice if there was a full featured portable multiprocessing
/// library like we have in Python. But there isn't, and rust community doesn't
/// seem to like processes, so we do with our own version based on nix crate.
mod multiprocessing {
    use core::{ffi::c_void, num::NonZeroUsize};
    use nix::{
        sys::{
            mman::{mmap, munmap, MapFlags, ProtFlags},
            signal::{kill, Signal::SIGKILL},
            wait::waitpid,
        },
        unistd::{fork, getpid, Pid},
    };
    use std::{mem::size_of, ops::Deref, panic::AssertUnwindSafe, ptr};

    /// Similar to a Box, but in shared memory, so that the containing object
    /// will be shared between processes after a fork.
    ///
    /// There is no way for this struct to track how many times it has been
    /// forked into other processes, and which of the process have finished
    /// and/or dropped the object, so destruction is manually controlled.
    ///
    /// The process that created the object will be the only one to drop its
    /// contents: so you must ensure that the SharedBox object in the parent
    /// process outlives its counterparts in the children processes.
    ///
    /// T is Sync because if you can't share it between threads, even less
    /// between processes. But being Sync is not sufficient to be safe for use
    /// across processes, it is just that Rust lacks a trait for inter-process
    /// sharing safety, and being Sync is the least we can do.
    pub struct SharedBox<T: Sync> {
        ptr: *mut T,
        creator: Pid,
    }

    impl<T: Sync> SharedBox<T> {
        /// This is unsafe because any type T that contains a pointer will most
        /// likely be broken. I don't know of any Rust trait that help us
        /// restrict T here, so I am making this unsafe.
        pub unsafe fn new(value: T) -> nix::Result<Self> {
            Ok(SharedBox {
                ptr: unsafe {
                    let ptr = mmap(
                        None,
                        NonZeroUsize::new(size_of::<T>()).unwrap(),
                        ProtFlags::PROT_WRITE | ProtFlags::PROT_READ,
                        MapFlags::MAP_SHARED | MapFlags::MAP_ANONYMOUS,
                        -1,
                        0,
                    )? as *mut T;
                    assert!(!ptr.is_null());
                    assert!(ptr.is_aligned());

                    ptr::write(ptr, value);
                    ptr
                },
                creator: getpid(),
            })
        }
    }

    impl<T: Sync> Drop for SharedBox<T> {
        fn drop(&mut self) {
            unsafe {
                if self.creator == getpid() {
                    ptr::drop_in_place(self.ptr);
                }

                munmap(self.ptr as *mut c_void, size_of::<T>()).unwrap();
            }
        }
    }

    impl<T: Sync> Deref for SharedBox<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            unsafe { &*self.ptr }
        }
    }

    /// Tracks a child process.
    ///
    /// The process is killed and collected upon dropping. This is a minimal
    /// effort to not leave processes running after parent crashes.
    pub struct Process(Pid);

    impl Process {
        pub unsafe fn new(func: impl FnOnce() -> u8) -> Self {
            match fork().unwrap() {
                nix::unistd::ForkResult::Parent { child } => Self(child),
                nix::unistd::ForkResult::Child => {
                    match std::panic::catch_unwind(AssertUnwindSafe(func)) {
                        Ok(return_code) => std::process::exit(return_code as i32),
                        Err(err) => {
                            eprint!("Child process function panicked");
                            if let Some(msg) = err.downcast_ref::<&'static str>() {
                                eprintln!(": {}", msg);
                            } else {
                                eprint!("! ");
                            }
                            eprintln!("Aborting...");
                            std::process::abort();
                        }
                    }
                }
            }
        }

        /// Get the process Pid.
        pub fn get_pid(&self) -> Pid {
            self.0
        }

        /// Stop tracking this process and don't kill or wait for it.
        pub fn detach(self) {
            {
                // This is a no-op because self.0 is Copy, but in the event it
                // changes, this should cause some error to be fixed.
                std::mem::drop(self.0);
            }
            std::mem::forget(self);
        }
    }

    impl Drop for Process {
        fn drop(&mut self) {
            kill(self.0, SIGKILL).unwrap();
            waitpid(self.0, None).unwrap();
        }
    }
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

fn ceil_div(a: NonZeroU32, b: NonZeroU32) -> NonZeroU32 {
    NonZeroU32::new((a.get() - 1) / b + 1).unwrap()
}

/// Multiprocess function to try to find if the r1cs file is deterministic.
///
/// It performs one Gröbner Basis per N output variables, in parallel across
/// num_procs forked processes. It decides for deterministic when all processes
/// exits and decides for deterministic on the variables they are handling.
///
/// Why processes an not threads? Because processes are interruptible: once a
/// the first process decides for possibly non-deterministic, I can kill all the
/// other processes and return.
fn is_deterministic<F: ZkField, const FS: usize>(
    num_procs: NonZeroU32,
    r1cs: R1csFile<FS>,
) -> Conclusion {
    let num_outs = match NonZeroU32::new(r1cs.header.n_pub_out) {
        None => {
            println!("Has no public outputs, so this is certainly deterministic.");
            return Conclusion::Deterministic;
        }
        Some(v) => v,
    };

    // Compute how to split the load.
    // Maybe we can handle less variables per process:
    let outs_per_run = min(ceil_div(num_outs, num_procs), N);
    // Maybe we need less processes:
    let num_procs = min(ceil_div(num_outs, outs_per_run), num_procs);

    println!(
        "Using {} processes, each with at most {} output variables",
        num_procs, outs_per_run
    );

    let (system, wire_map) = build_shared_system::<F, FS>(r1cs, outs_per_run.get());

    // Shared atomic variable with the next output to be processed.
    let out_counter = unsafe { multiprocessing::SharedBox::new(AtomicU32::new(0)) }.unwrap();

    // Run the worker subprocesses and collect the handles in a hash map.
    let mut subprocesses: HashMap<Pid, multiprocessing::Process> = (0..num_procs.get())
        .map(|_| {
            let new_proc_func = || {
                // Process the out variables until there are none left.
                'outer: loop {
                    // Build the constraint saying that at least one output
                    // variable must be non unique, using at most `outs_per_run`
                    // vars at a time.
                    let mut non_unique_constraint = Poly::one();
                    let mut vars = Vec::new();
                    'inner: for inverse_var in 1..=outs_per_run.get() {
                        let var = out_counter.fetch_add(1, Relaxed);
                        if var >= num_outs.get() {
                            if inverse_var == 1 {
                                // There are no variables left to process, break outer loop.
                                break 'outer;
                            } else {
                                // We have some output variables to process.
                                break 'inner;
                            }
                        }

                        // Get the even and odd identifiers for output variable,
                        // (they start counting from 1).
                        vars.push(var + 1);
                        let (even, odd) = wire_map[&(var + 1)];

                        let factor = Poly::new_var(inverse_var)
                            * (Poly::new_var(even) - Poly::new_var(odd))
                            - Poly::one();
                        non_unique_constraint = non_unique_constraint * factor;
                    }

                    println!(
                        "%% {} %% processing vars {:?}, num terms: {}",
                        getpid(),
                        vars,
                        non_unique_constraint.get_terms().len()
                    );
                    drop(vars);

                    // Create the system to be tested and include the constraint to the outputs
                    let mut system = system.clone();
                    system.push(non_unique_constraint);

                    // Run the grobner basis
                    system.sort_unstable();
                    let gb = polynomial_solver::polynomial::signature_basis::grobner_basis(system);

                    // Return 1 immediately if the processed output may be non-deterministic.
                    if gb.into_iter().all(|p| p.is_zero() || !p.is_constant()) {
                        return 1;
                    }
                }

                // Return 0 means every variable tested was found to be deterministic.
                0
            };

            let new_proc = unsafe { multiprocessing::Process::new(new_proc_func) };

            (new_proc.get_pid(), new_proc)
        })
        .collect();

    // Wait for the subprocesses to finish:
    while !subprocesses.is_empty() {
        let wait_result;
        {
            // This is a critical region, where a pid has been waited, but we
            // still hold the handle that will try to kill and wait that same
            // process upon dropping. We need to forget it.
            //
            // The problem here is the possibility of killing some random
            // process whose PID happens to reuse the collected process, and we
            // don't want that.
            wait_result = wait().unwrap();
            if let Some(pid) = wait_result.pid() {
                subprocesses.remove(&pid).unwrap().detach();
            }
        }

        match wait_result {
            WaitStatus::Exited(_, status) => {
                if status == 1 {
                    // There is at least one output that can be non-deterministic,
                    // we can return immediately:
                    return Conclusion::Unknown;
                }
            }
            WaitStatus::Signaled(pid, signal, _) => {
                panic!("Subprocess {} was killed by signal {}!", pid, signal);
            }
            _ => unreachable!(),
        }
    }

    // Every process has finished with status != 1, which means all outputs are
    // deterministic.
    Conclusion::Deterministic
}

/// Encodes the zk circuit twice, sharing the input variables.
///
/// The uniqueness of output constraints is not encoded, and must be added to the system.
fn build_shared_system<F: ZkField, const FS: usize>(
    r1cs: R1csFile<FS>,
    num_reserved: u32,
) -> (Vec<Poly<F>>, HashMap<u32, (u32, u32)>) {
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

    // Skip id 0 and reserved var ids:
    let mut var_id_gen = (1 + num_reserved)..;

    // For each of public output, we generate 2 variables: one for each of the
    // even and odd constraint systems.
    for i in 0..r1cs.header.n_pub_out {
        let out_wire = 1 + i;
        let even = var_id_gen.next().unwrap();
        let odd = var_id_gen.next().unwrap();
        wire_map.insert(out_wire, (even, odd));
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

    (poly_set, wire_map)
}

mod just_dump {
    use std::cell::RefCell;

    use polynomial_solver::{
        finite_field::ThreadPrimeField,
        polynomial::{Id, Term},
    };
    use r1cs_file::R1csFile;
    use rug::Integer;

    /// Id wrapper for better display of R1CS wire roles.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct R1csId(u32);

    impl R1csId {
        thread_local! {
            pub static INFO: std::cell::RefCell<Option<VarInfo>>  = RefCell::new(None);
        }
    }

    impl Id for R1csId {
        fn to_idx(&self) -> usize {
            self.0 as usize
        }

        fn from_idx(idx: usize) -> Self {
            Self(idx as u32)
        }

        fn display(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            Self::INFO.with(|info| {
                let r = info.borrow();
                let info = r.as_ref().unwrap();

                if self.0 == 0 {
                    return write!(f, "𒁹");
                }

                let (prefix, delta) = if self.0 >= info.first_internal {
                    ('w', info.first_internal)
                } else if self.0 >= info.first_private_input {
                    ('i', info.first_private_input)
                } else if self.0 >= info.first_public_input {
                    ('I', info.first_public_input)
                } else {
                    ('O', 1)
                };

                write!(f, "{}{}", prefix, self.0 - delta)
            })
        }
    }

    struct VarInfo {
        first_internal: u32,
        first_private_input: u32,
        first_public_input: u32,
    }

    impl VarInfo {
        fn new<const FS: usize>(r1cs: &R1csFile<FS>) -> Self {
            let h = &r1cs.header;
            let first_public_input = 1 + h.n_pub_out;
            let first_private_input = first_public_input + h.n_pub_in;
            let first_internal = first_private_input + h.n_prvt_in;

            Self {
                first_internal,
                first_private_input,
                first_public_input,
            }
        }
    }

    type DumpPoly = polynomial_solver::polynomial::Polynomial<
        polynomial_solver::polynomial::monomial_ordering::Grevlex,
        R1csId,
        ThreadPrimeField,
        i32,
    >;

    pub(crate) fn just_dump<const FS: usize>(prime: Integer, r1cs: R1csFile<FS>) {
        println!("i: private input, I: public input, O: public output, w: internal wire, 𒁹: one");

        ThreadPrimeField::set_prime(prime).unwrap();
        R1csId::INFO.with(|info| {
            info.replace(Some(VarInfo::new(&r1cs)));
        });

        // Read the constraints
        for (cnum, constraint) in r1cs.constraints.0.into_iter().enumerate() {
            let [a, b, c] = [constraint.0, constraint.1, constraint.2].map(|terms| {
                let terms = terms
                    .into_iter()
                    .map(|(coeff, wire_id)| {
                        Term::new(
                            Integer::from_digits(coeff.as_bytes(), rug::integer::Order::Lsf).into(),
                            R1csId(wire_id),
                            1,
                        )
                    })
                    .collect();

                DumpPoly::from_terms(terms)
            });

            println!("\nConstraint {cnum}:\n  A: {a}\n  B: {b}\n  C: {c}");
        }
    }
}
