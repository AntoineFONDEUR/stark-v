//! End-to-end n-to-1 recursive aggregation of a real RISC-V execution, plus a
//! tunable benchmark harness.
//!
//! The correctness test runs a small guest, segments it, and folds the
//! segments into one constant-size root which then verifies. The benchmark is
//! `#[ignore]`d and reads its parameters from the environment so the fan-in
//! can be swept on a given machine:
//!
//!   RECURSION_GUEST=long_run RECURSION_ARITY=4 RECURSION_SEGMENT_CYCLES=1048575 \
//!     cargo test -p recursion --release --test aggregate_tree -- \
//!     --ignored --nocapture bench_guest_recursive
//!
//! Per-phase wall-clock (continuation, segment proofs, base nodes, tree fold)
//! is logged by `prove_guest_recursive` at `info` level; `#[test_log::test]`
//! installs the subscriber.

use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
use prover::{PcsConfig, preprocess_with_channel};
use recursion::aggregate_tree::prove_guest_recursive;
use recursion::node::verify_node_compressed;
use runner::run;

/// A small execution folded 2-to-1 to one root that verifies: the full
/// guest -> segments -> base nodes -> tree pipeline end to end.
#[test_log::test]
fn test_guest_recursive_arity_2_verifies() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("fib")).expect("read fib ELF");
    let reference = run(&elf, 10_000_000).expect("run fib");

    // Split into ~3 segments so arity-2 base grouping yields >= 2 leaves.
    let segment_cycles = u32::try_from(reference.cycles / 3 + 1).expect("fits u32");
    let config = PcsConfig::default();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);

    let root = prove_guest_recursive(
        &elf,
        &[],
        2,
        segment_cycles,
        10_000_000,
        config,
        &preprocessing,
    )
    .expect("recursive proving failed");
    verify_node_compressed(root, config).expect("root verification failed");
}

/// Tunable harness: sweep `RECURSION_ARITY` (and guest / segment size) on the
/// host to find the throughput-optimal fan-in. Logs per-phase timings and
/// checks the root verifies.
#[test_log::test]
#[ignore]
fn bench_guest_recursive() {
    let guest = std::env::var("RECURSION_GUEST").unwrap_or_else(|_| "long_run".to_string());
    let arity: usize = std::env::var("RECURSION_ARITY")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2);
    // Default segment bound is the RangeCheck20 clock limit (2^20 - 1).
    let segment_cycles: u32 = std::env::var("RECURSION_SEGMENT_CYCLES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or((1 << 20) - 1);

    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join(&guest))
        .unwrap_or_else(|e| panic!("read {guest} ELF: {e}"));

    let config = PcsConfig::default();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);
    let root = prove_guest_recursive(
        &elf,
        &[],
        arity,
        segment_cycles,
        20_000_000,
        config,
        &preprocessing,
    )
    .expect("recursive proving failed");
    verify_node_compressed(root, config).expect("root verification failed");
}
