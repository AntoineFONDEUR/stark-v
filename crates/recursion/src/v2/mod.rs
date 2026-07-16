//! Versioned foundations for the sound binary recursion protocol.

pub mod air_expression_circuit;
pub mod air_relation_parameters;
pub mod control_air;
pub mod kernel;
pub mod oods_circuit;
pub mod pow;
pub mod protocol;
pub mod query_position_air;
pub mod relation_challenge_air;
pub mod statement;
pub mod statement_input_air;
pub mod statement_semantics_circuit;
pub mod statement_semantics_input_air;
pub mod statement_semantics_lowering;
pub mod transcript;
pub mod transcript_air;
pub mod transcript_binding_air;
pub mod transcript_layout;
pub mod transcript_payload_air;
pub mod transcript_program;
pub mod transcript_state_air;
pub mod transcript_word_air;
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

#[cfg(test)]
pub(crate) mod test_fixtures;
#[cfg(test)]
mod vm_leaf_binding_tests;
