#![feature(drain_filter)]
#![feature(binary_heap_into_iter_sorted)]
#![feature(type_alias_impl_trait)]
#![feature(step_trait)]

pub mod factorization;
pub mod finite_field;
pub mod gcd;
pub mod kd_tree;
pub mod polynomial;
pub mod prime_field_solvability;

mod fast_compare;
mod ordered_ops;

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;
