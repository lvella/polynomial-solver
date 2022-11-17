#![feature(
    step_trait,
    box_into_inner,
    type_alias_impl_trait,
    binary_heap_into_iter_sorted,
    drain_filter
)]

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
