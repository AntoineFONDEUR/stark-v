//! stark-v SDK - Build and prove RISC-V programs.
//!
//! This crate provides a unified interface for external consumers of stark-v,
//! including implementation of the [`ere_zkvm_interface`] traits for interoperability
//! with other zkVMs.
//!
//! # Modules
//!
//! - [`guest`] - Guest program utilities (I/O constants, helpers)
//! - [`prover`] - Proving and verification functions
//! - [`runner`] - Program execution and tracing
//!
//! # Example using ere-zkvm-interface
//!
//! ```ignore
//! use ere_zkvm_interface::{Compiler, Input, ProofKind, zkVM};
//! use stark_v_sdk::{secure_pcs_config, StarkV, StarkVCompiler};
//! use std::path::Path;
//!
//! // Compile a guest program
//! let compiler = StarkVCompiler::new();
//! let program = compiler.compile(Path::new("guest/sha256"))?;
//!
//! // Create VM instance and prove
//! let vm = StarkV::new(program, secure_pcs_config());
//! let input = Input::new().with_stdin(input_bytes);
//! let (public_values, proof, report) = vm.prove(&input, ProofKind::Compressed)?;
//!
//! // Verify
//! vm.verify(&proof)?;
//! ```

/// Guest program utilities: I/O memory layout, constants, and helpers.
pub use guest_lib as guest;

/// Proving and verification for RV32IM programs.
pub use prover;

/// Program execution and tracing.
pub use runner;

// Re-export key types for convenience
pub use prover::{FriConfig, PcsConfig, Proof, ProverBackend};
pub use runner::{RunError, RunResult};

mod compiler;
mod proof_serde;
mod vm;

pub use compiler::{StarkVCompiler, StarkVCompilerError, StarkVProgram};
pub use vm::StarkV;

/// Maximum cycles for program execution (default).
pub const DEFAULT_MAX_CYCLES: u64 = 100_000_000;

/// Returns the PCS configuration targeting 96 bits of proven security under the
/// Unique Decoding Regime (UDR) from the BCHKS25 FRI soundness analysis.
///
/// # Security computation (soundcalc)
///
/// Security is `min(query_phase, batching, commit_rounds)`:
///
/// **Query phase** (UDR, rate ρ=1/2 over QM31):
///   - Proximity parameter θ = (1−ρ)/2 = 0.25, giving ~0.415 bits per query.
///   - `query_bits = pow_bits + n_queries × log2(1/(1−θ)) = 16 + 193 × 0.415 ≈ 96`.
///
/// **Batching** (power batching, ~1051 columns):
///   - `batch_bits = floor(−log2((batch_size−1) × (θ·n+1) / |QM31|))`.
///   - For trace ≤ 2^20: 94 bits. For trace 2^22: 92 bits.
///   - Batching is not strengthened by PoW (randomness drawn before grind).
///   - This is the hard ceiling for large traces without protocol changes.
///
/// **Commit rounds** (fold_step=4, fold by 16 per round): ≥80 bits — not the
/// bottleneck. Using fold_step=4 reduces FRI from ~22 rounds to ~6 rounds, saving
/// ~1.5 MB of Merkle auth paths in the proof (with 193 queries). Commit-phase
/// security drops from ~103 bits (fold by 2) to ~80 bits, still above the query
/// phase and batching bottlenecks.
///
/// References:
///   - BCHKS25 (Improved FRI bounds): <https://eprint.iacr.org/2025/2055>
///   - Fenzi & Sanso (small-field soundness): <https://eprint.iacr.org/2025/2197>
///   - Ethereum soundcalc: <https://github.com/ethereum/soundcalc>
pub fn secure_pcs_config() -> PcsConfig {
    PcsConfig {
        // 16 bits of proof-of-work grinding (~65ms on M3).
        pow_bits: 16,
        // FriConfig::new(log_last_layer_degree_bound, log_blowup_factor, n_queries, fold_step)
        //   - log_blowup_factor=1: rate ρ=1/2 (2x evaluation domain).
        //   - n_queries=193: 193 × 0.415 ≈ 80 bits from queries, + 16 pow = 96 bits.
        //   - fold_step=4: each FRI round folds by 2^4=16, reducing ~22 rounds
        //     to ~6. Saves ~1.5 MB of Merkle auth paths at the cost of opening 16
        //     siblings per round instead of 2.
        fri_config: FriConfig::new(0, 1, 193, 4),
        lifting_log_size: None,
    }
}

#[cfg(test)]
mod tests {
    use super::secure_pcs_config;

    #[test]
    fn test_secure_pcs_config_matches_expected_parameters() {
        let config = secure_pcs_config();
        assert_eq!(config.pow_bits, 16);
        assert_eq!(config.fri_config.log_last_layer_degree_bound, 0);
        assert_eq!(config.fri_config.log_blowup_factor, 1);
        assert_eq!(config.fri_config.n_queries, 193);
        assert_eq!(config.fri_config.fold_step, 4);
        assert_eq!(config.lifting_log_size, None);
    }

    #[test]
    fn test_secure_pcs_config_security_bits() {
        let config = secure_pcs_config();
        // Stwo's built-in formula: pow_bits + log_blowup * n_queries = 16 + 1 * 193 = 209.
        // This uses the conjectured 1 bit/query; proven UDR security is 96 bits
        // (each query gives ~0.415 bits at rate 1/2 over QM31).
        assert_eq!(config.security_bits(), 16 + 1 * 193);
    }
}
