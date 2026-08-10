//! zkVM implementation for stark-v.
//!
//! This module provides the [`StarkV`] struct which implements the
//! [`ere_zkvm_interface::zkVM`] trait.

use crate::compiler::StarkVProgram;
use crate::{ProverBackend, DEFAULT_MAX_CYCLES};
use anyhow::{anyhow, bail};
use ere_zkvm_interface::{
    zkVM, CommonError, Input, ProgramExecutionReport, ProgramProvingReport, Proof as EreProof,
    ProofKind, PublicValues,
};
use prover::PcsConfig;
use std::collections::BTreeMap;
use std::time::Instant;

/// stark-v zkVM instance.
///
/// Holds a compiled program, configuration, and cached preprocessing data.
pub struct StarkV {
    /// Compiled ELF program.
    program: StarkVProgram,
    /// Maximum cycles before aborting.
    max_cycles: u64,
    /// PCS configuration.
    config: PcsConfig,
    /// Proving backend policy.
    backend: ProverBackend,
    /// Cached preprocessing data (Merkle tree + extended evals).
    preprocessing: prover::Preprocessing,
}

impl StarkV {
    /// Create a new stark-v instance with a compiled program.
    pub fn new(program: StarkVProgram, config: PcsConfig) -> Self {
        Self {
            program,
            max_cycles: DEFAULT_MAX_CYCLES,
            backend: ProverBackend::Simd,
            preprocessing: prover::preprocess(config),
            config,
        }
    }

    /// Set the maximum cycles for execution.
    pub fn with_max_cycles(mut self, max_cycles: u64) -> Self {
        self.max_cycles = max_cycles;
        self
    }

    /// Select the proving backend policy. The default is [`ProverBackend::Simd`].
    pub fn with_backend(mut self, backend: ProverBackend) -> Self {
        self.backend = backend;
        self
    }

    /// Return the configured proving backend policy.
    pub fn backend(&self) -> ProverBackend {
        self.backend
    }

    /// Set the PCS configuration.
    ///
    /// Regenerates preprocessing data since it depends on the blowup factor.
    pub fn with_config(mut self, config: PcsConfig) -> Self {
        self.config = config;
        self.preprocessing = prover::preprocess(config);
        self
    }

    /// Get the ELF bytes.
    pub fn elf_bytes(&self) -> &[u8] {
        &self.program.elf_bytes
    }
}

fn reject_unsupported_input(input: &Input) -> anyhow::Result<()> {
    if input.proofs.is_some() {
        bail!(CommonError::unsupported_input("no dedicated proofs stream"));
    }
    Ok(())
}

fn extract_output_payload_bytes(
    output_data_addr: u32,
    output_len: u32,
    output_words: &[(u32, u32)],
) -> anyhow::Result<Vec<u8>> {
    if output_len == 0 {
        return Ok(Vec::new());
    }

    let output_len = output_len as usize;
    let mut words_by_addr = BTreeMap::new();
    for &(addr, value) in output_words {
        words_by_addr.insert(addr, value);
    }

    let mut output = Vec::with_capacity(output_len);
    for offset in 0..output_len {
        let byte_addr = output_data_addr.wrapping_add(offset as u32);
        let aligned_addr = byte_addr & !3;
        let byte_idx = (byte_addr & 3) as usize;

        let word = words_by_addr.get(&aligned_addr).ok_or_else(|| {
            CommonError::deserialize(
                "proof public output",
                "stark-v",
                anyhow!("missing output word at address 0x{aligned_addr:08x}"),
            )
        })?;

        output.push(word.to_le_bytes()[byte_idx]);
    }

    Ok(output)
}

impl zkVM for StarkV {
    fn execute(&self, input: &Input) -> anyhow::Result<(PublicValues, ProgramExecutionReport)> {
        reject_unsupported_input(input)?;

        let start = Instant::now();
        let run_result =
            runner::run_with_input(&self.program.elf_bytes, input.stdin(), self.max_cycles)?;

        let output = run_result.output.clone().unwrap_or_default();
        let report = ProgramExecutionReport {
            total_num_cycles: run_result.cycles,
            execution_duration: start.elapsed(),
            ..Default::default()
        };

        Ok((output, report))
    }

    fn prove(
        &self,
        input: &Input,
        proof_kind: ProofKind,
    ) -> anyhow::Result<(PublicValues, EreProof, ProgramProvingReport)> {
        reject_unsupported_input(input)?;
        if proof_kind != ProofKind::Compressed {
            bail!(CommonError::unsupported_proof_kind(
                proof_kind,
                [ProofKind::Compressed]
            ));
        }

        let start = Instant::now();
        let run_result =
            runner::run_with_input(&self.program.elf_bytes, input.stdin(), self.max_cycles)?;
        let output = run_result.output.clone().unwrap_or_default();

        let outcome = prover::prove_rv32im_with_backend(
            run_result,
            self.config,
            &self.preprocessing,
            self.backend,
        )
        .map_err(|err| anyhow!("Proof generation failed: {err}"))?;
        let proof = outcome.proof;
        let proof_bytes = postcard::to_allocvec(&proof)
            .map_err(|err| CommonError::serialize("proof", "postcard", err))?;

        Ok((
            output,
            EreProof::Compressed(proof_bytes),
            ProgramProvingReport::new(start.elapsed()),
        ))
    }

    fn verify(&self, proof: &EreProof) -> anyhow::Result<PublicValues> {
        use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

        let EreProof::Compressed(proof_bytes) = proof else {
            bail!(CommonError::unsupported_proof_kind(
                proof.kind(),
                [ProofKind::Compressed]
            ));
        };

        let proof: prover::Proof<Blake2sMerkleHasher> = postcard::from_bytes(proof_bytes)
            .map_err(|err| CommonError::deserialize("proof", "postcard", err))?;

        let output_words = proof
            .public_data
            .io_entries
            .output_words
            .iter()
            .map(|word| (word.addr, word.value))
            .collect::<Vec<_>>();
        let output = extract_output_payload_bytes(
            proof.public_data.io_entries.output_data_addr,
            proof.public_data.io_entries.output_len,
            &output_words,
        )?;

        prover::verify_rv32im(proof, self.config, &self.preprocessing)
            .map_err(|err| anyhow!("Proof verification failed: {err}"))?;

        Ok(output)
    }

    fn name(&self) -> &'static str {
        "stark-v"
    }

    fn sdk_version(&self) -> &'static str {
        env!("CARGO_PKG_VERSION")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_starkv_creation() {
        let program = StarkVProgram {
            elf_bytes: vec![1, 2, 3],
        };
        let vm = StarkV::new(program, PcsConfig::default());
        assert_eq!(vm.elf_bytes(), &[1, 2, 3]);
        assert_eq!(vm.max_cycles, DEFAULT_MAX_CYCLES);
        assert_eq!(vm.backend(), ProverBackend::Simd);
    }

    #[test]
    fn test_starkv_backend_builder() {
        let program = StarkVProgram {
            elf_bytes: vec![1, 2, 3],
        };
        let vm =
            StarkV::new(program, PcsConfig::default()).with_backend(ProverBackend::MetalPrefer);
        assert_eq!(vm.backend(), ProverBackend::MetalPrefer);
    }

    #[test]
    fn test_extract_output_payload_bytes_skips_output_len_word() {
        let output_words = vec![
            (0x1004, 5),
            (0x1008, u32::from_le_bytes(*b"ABCD")),
            (0x100c, u32::from_le_bytes([b'E', 0, 0, 0])),
        ];

        let output = extract_output_payload_bytes(0x1008, 5, &output_words).unwrap();
        assert_eq!(output, b"ABCDE");
    }

    #[test]
    fn test_extract_output_payload_bytes_handles_unaligned_output_start() {
        let output_words = vec![
            (0x1004, 6),
            (0x1008, u32::from_le_bytes([0xaa, 0x11, 0x22, 0x33])),
            (0x100c, u32::from_le_bytes([0x44, 0x55, 0x66, 0xbb])),
        ];

        let output = extract_output_payload_bytes(0x1009, 6, &output_words).unwrap();
        assert_eq!(output, [0x11, 0x22, 0x33, 0x44, 0x55, 0x66]);
    }

    #[test]
    fn test_extract_output_payload_bytes_errors_when_word_missing() {
        let output_words = vec![(0x1004, 5), (0x1008, u32::from_le_bytes(*b"ABCD"))];

        let err = extract_output_payload_bytes(0x1008, 5, &output_words).unwrap_err();
        assert!(err
            .to_string()
            .contains("missing output word at address 0x0000100c"));
    }
}
