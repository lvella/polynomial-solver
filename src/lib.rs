#![feature(drain_filter)]
#![feature(binary_heap_into_iter_sorted)]
#![feature(map_first_last)]
#![feature(vec_retain_mut)]

pub mod big_unsigned;
pub mod factorization;
pub mod finite_field;
pub mod gcd;
pub mod polynomial;
pub mod solvability;

mod ordered_ops;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;
