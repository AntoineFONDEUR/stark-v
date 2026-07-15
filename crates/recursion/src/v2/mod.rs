//! Versioned foundations for the sound binary recursion protocol.

pub mod control_air;
pub mod kernel;
pub mod pow;
pub mod protocol;
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
pub mod vm_public_claim;
pub mod wire;

#[cfg(test)]
pub(crate) mod test_fixtures;
