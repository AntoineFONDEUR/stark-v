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
use recursion::aggregate_tree::{prove_guest_recursive, prove_guest_recursive_by_capacity};
use recursion::node::verify_node_compressed;
use runner::run;

/// A small execution folded 2-to-1 through a multi-level tree to one root
/// that verifies AND exposes the boundary of the whole run: the full
/// guest -> segments -> base nodes -> tree pipeline end to end, with the
/// root's boundary claim checked against an independent unsegmented run.
#[test_log::test]
fn test_guest_recursive_arity_2_root_spans_the_run() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("fib")).expect("read fib ELF");
    let reference = run(&elf, 10_000_000).expect("run fib");

    // Split into ~5 segments: arity-2 base grouping yields 3 leaves, so the
    // fold has an intermediate level (a node child and a ridden-up leaf).
    let segment_cycles = u32::try_from(reference.cycles / 5 + 1).expect("fits u32");
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
    let boundary = verify_node_compressed(root, config)
        .expect("root verification failed")
        .expect("an execution tree carries a boundary");
    assert_eq!(boundary.entry_pc, reference.initial_pc);
    assert_eq!(boundary.exit_pc, reference.final_pc);
    assert_eq!(boundary.entry_regs, reference.initial_regs);
    assert_eq!(boundary.exit_regs, reference.final_regs);
    assert!(boundary.program_root.is_some());
}

/// The degenerate tree: a run small enough for one base group still yields
/// a root (a 1-child wrap) whose boundary spans the run.
#[test_log::test]
fn test_guest_recursive_single_segment_wraps() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("fib")).expect("read fib ELF");
    let reference = run(&elf, 10_000_000).expect("run fib");

    // A budget above the whole run: only the forced output-tail boundary
    // splits it, so arity-2 base grouping folds everything into one leaf.
    let segment_cycles = u32::try_from(reference.cycles + 1).expect("fits u32");
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
    assert_eq!(root.children.len(), 1);
    let boundary = verify_node_compressed(root, config)
        .expect("root verification failed")
        .expect("an execution tree carries a boundary");
    assert_eq!(boundary.entry_pc, reference.initial_pc);
    assert_eq!(boundary.exit_pc, reference.final_pc);
    assert_eq!(boundary.exit_regs, reference.final_regs);
}

/// Capacity-aware segmentation end to end: a small run split on a row budget
/// (not a cycle count), folded 2-to-1 to one root that verifies.
#[test_log::test]
fn test_guest_recursive_by_capacity_verifies() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("fib")).expect("read fib ELF");
    let reference = run(&elf, 10_000_000).expect("run fib");

    // A budget of ~1/3 the run yields >= 3 segments, so arity-2 base grouping
    // gives >= 2 leaves (clamped to the range check's 2^20 limit).
    let max_rows = u32::try_from(reference.cycles / 3 + 1)
        .expect("fits u32")
        .clamp(2, (1 << 20) - 1);
    let config = PcsConfig::default();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);

    let root = prove_guest_recursive_by_capacity(
        &elf,
        &[],
        2,
        max_rows,
        10_000_000,
        config,
        &preprocessing,
    )
    .expect("recursive proving failed");
    let boundary = verify_node_compressed(root, config)
        .expect("root verification failed")
        .expect("an execution tree carries a boundary");
    assert_eq!(boundary.entry_pc, reference.initial_pc);
    assert_eq!(boundary.exit_pc, reference.final_pc);
    assert_eq!(boundary.exit_regs, reference.final_regs);
}

/// Tunable harness: sweep `RECURSION_ARITY` and the per-segment row budget
/// `RECURSION_MAX_ROWS` (capacity-aware) on the host to find the
/// throughput-optimal fan-in. Logs per-phase timings and checks the root
/// verifies.
#[test_log::test]
#[ignore]
fn bench_guest_recursive() {
    let guest = std::env::var("RECURSION_GUEST").unwrap_or_else(|_| "long_run".to_string());
    let arity: usize = std::env::var("RECURSION_ARITY")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(recursion::aggregate_tree::DEFAULT_RECURSION_ARITY);
    // Default budget is the RangeCheck20 clock limit (2^20 - 1).
    let max_rows: u32 = std::env::var("RECURSION_MAX_ROWS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or((1 << 20) - 1);

    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join(&guest))
        .unwrap_or_else(|e| panic!("read {guest} ELF: {e}"));

    let config = PcsConfig::default();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);
    let root = prove_guest_recursive_by_capacity(
        &elf,
        &[],
        arity,
        max_rows,
        20_000_000,
        config,
        &preprocessing,
    )
    .expect("recursive proving failed");
    verify_node_compressed(root, config).expect("root verification failed");
}
