//! AIR components and protocol types for binary recursive proving.
//!
//! The crate defines one verifier circuit that accepts either a stark-v
//! segment proof or two proofs produced by this same circuit. It does not yet
//! expose a complete recursive prover or root-verifier API; `docs/recursion.md`
//! tracks the remaining integration work.
//!
//! Every recursion-owned roster component is authored in `define_air!` or
//! `define_air_fns!`, so its AIR evaluation and interaction witness share one
//! source definition.
#![allow(clippy::too_many_arguments)] // generated table push takes one arg per column

pub mod air_expression_circuit;
pub mod air_relation_parameters;
pub mod circuit;
pub mod control_air;
mod dynamic_logup;
pub mod fri_merkle_air;
pub mod fri_verifier_circuit;
pub mod fri_verifier_control_air;
pub mod fri_verifier_input_air;
pub mod fri_verifier_lowering;
pub mod kernel;
pub mod linear_ops;
pub mod merkle_path;
pub mod merkle_root_air;
pub mod oods_circuit;
pub mod pcs_deep_circuit;
pub mod pcs_deep_input_air;
pub mod pcs_deep_lowering;
pub mod pow;
pub mod profile;
pub mod profiled_channel;
pub mod protocol;
pub mod qm31_inv;
pub mod qm31_mul;
pub mod query_position_air;
pub mod recorder;
pub mod recursion_air_program;
pub mod relation_challenge_air;
pub mod relations;
pub mod segment_leaf;
pub mod statement;
pub mod statement_input_air;
pub mod statement_semantics_circuit;
pub mod statement_semantics_input_air;
pub mod statement_semantics_lowering;
pub mod trace_merkle_air;
pub mod transcript;
pub mod transcript_air;
pub mod transcript_binding_air;
pub mod transcript_layout;
pub mod transcript_payload_air;
pub mod transcript_program;
pub mod transcript_state_air;
pub mod transcript_word_air;
pub mod universal_relations;
pub mod universal_witness;
pub mod verifier_randomness_air;
pub mod vm_air_composition_circuit;
pub mod vm_air_composition_control_air;
pub mod vm_air_composition_input_air;
pub mod vm_air_composition_lowering;
pub mod vm_air_program;
pub mod vm_pcs_layout;
pub mod vm_public_claim;
pub mod vm_public_claim_hash_air;
pub mod vm_public_claim_input_air;
pub mod vm_public_claim_semantics_circuit;
pub mod vm_public_claim_semantics_input_air;
pub mod vm_public_claim_semantics_lowering;
pub mod vm_public_io_hash_air;
pub mod vm_public_logup_circuit;
pub mod vm_public_logup_control_air;
pub mod vm_public_logup_input_air;
pub mod vm_public_logup_lowering;
pub mod wire;

pub use linear_ops::LinearOpsTable;
pub use merkle_path::MerklePathTable;
pub use qm31_inv::Qm31InvTable;
pub use qm31_mul::Qm31MulTable;

#[cfg(test)]
mod fri_verifier_binding_tests;
#[cfg(test)]
pub(crate) mod test_fixtures;
#[cfg(test)]
mod vm_leaf_binding_tests;
