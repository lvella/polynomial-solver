#![feature(drain_filter)]
#![feature(binary_heap_into_iter_sorted)]
#![feature(map_first_last)]
#![feature(is_some_with)]

pub mod factorization;
pub mod finite_field;
pub mod gcd;
pub mod polynomial;
pub mod prime_field_solvability;

mod ordered_ops;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;
