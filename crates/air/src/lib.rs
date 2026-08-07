//! Shared AIR schema for the stark-v zkVM.
//!
//! Trace table definitions, LogUp relation metadata, preprocessed lookup tables,
//! and the Poseidon2 permutation live here so the runner can fill traces and
//! the prover can prove them from the same source.

#![feature(allocator_api)]

// Generated dynamic components use the same owner path in this crate and its consumers.
extern crate self as air;

#[macro_use]
mod schema;
pub use schema::relations;

pub mod clock;
pub mod digest;
pub mod instructions;
pub mod opcodes;
pub mod poseidon2;
pub mod preprocessed;
pub mod relation_eval;

#[macro_use]
pub mod trace;
pub mod vm;

/// Maximum binary Merkle tree height for memory and proof commitments.
///
/// Addresses are M31 field elements, so a binary tree over the address space
/// has at most 31 levels. Leaf depth in trace lookups is
/// `MAX_TREE_HEIGHT - 1` because depth counts edges from the root to a leaf
/// index.
pub const MAX_TREE_HEIGHT: u32 = 31;
