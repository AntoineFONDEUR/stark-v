//! Opcode AIRs expressed as felt functions (`define_air_fns!`).
//!
//! Each module defines one opcode's table, columns, and prover component, and
//! is folded into the `Tracer` via the `external:` section of `define_air!`
//! and wired into the prover through `components! { … name: module … }`.

pub mod auipc;
pub mod jal;
pub mod jalr;
pub mod lui;
