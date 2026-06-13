//! Re-export trace tables from the shared air crate.
//!
//! Every RISC-V opcode now records its row through the fn-DSL `*_fill` entry
//! points (`air::opcodes::<op>::<op>_fill`), so the schema-generated
//! `trace_op!` macro is no longer forwarded here.

pub use air::trace::*;
