//! The single final proof over a real segmented execution: every segment's
//! composition check and every Merkle opening proven in ONE recursion proof,
//! verified without ever touching an inner proof or a decommitment.

use prover::e2e::prove_segments_with_channel;
use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
use prover::{PcsConfig, preprocess_with_channel, prove_rv32im_with_channel};
use recursion::final_proof::{FinalProof, prove_final, verify_final};
use runner::{run, run_segments_with_input};

static SHARED: std::sync::OnceLock<(FinalProof, u32, u32, [u32; 32])> = std::sync::OnceLock::new();

/// Prove once, share across the roundtrip and tamper tests (proving is the
/// expensive part; tampering only needs a clone of the artifact).
fn shared_final() -> &'static (FinalProof, u32, u32, [u32; 32]) {
    SHARED.get_or_init(|| {
        let (final_proof, reference) = prove_two_segment_final();
        (
            final_proof,
            reference.initial_pc,
            reference.final_pc,
            reference.final_regs,
        )
    })
}

fn prove_two_segment_final() -> (FinalProof, runner::RunResult) {
    prover::e2e::ensure_guest_built();
    let elf_path = prover::e2e::guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");

    let reference = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");
    let segment_cycles = u32::try_from(reference.cycles / 2 + 1).expect("fits u32");
    let segments = run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 10_000_000)
        .expect("segmented run failed");
    assert_eq!(segments.len(), 2);

    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());
    let proofs = prove_segments_with_channel::<Poseidon2M31MerkleChannel>(
        segments,
        PcsConfig::default(),
        &preprocessing,
    );
    let final_proof = prove_final(proofs, PcsConfig::default(), &preprocessing);
    (final_proof, reference)
}

#[test]
fn test_final_proof_roundtrip_two_segments() {
    let (final_proof, entry_pc, exit_pc, exit_regs) = shared_final();
    let final_proof = final_proof.clone();

    // The inner bodies carry no decommitment at all (the recursion proof,
    // being a regular stwo proof, keeps its own).
    for segment in &final_proof.segments {
        for decommitment in &segment.stark_proof.0.decommitments.0 {
            assert!(decommitment.hash_witness.is_empty());
        }
        assert!(
            segment
                .stark_proof
                .0
                .fri_proof
                .first_layer
                .decommitment
                .hash_witness
                .is_empty()
        );
    }

    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());
    let boundary = verify_final(final_proof, PcsConfig::default(), &preprocessing)
        .expect("final proof verification failed");

    assert_eq!(boundary.entry_pc, *entry_pc);
    assert_eq!(boundary.exit_pc, *exit_pc);
    assert_eq!(boundary.exit_regs, *exit_regs);
}

/// The goal condition: a >10M-cycle RISC-V execution proven as ONE final
/// proof. The run segments into 2^20-cycle-bounded pieces, every segment is
/// proven over the Poseidon2-M31 channel, and `prove_final` folds all
/// composition checks and Merkle openings into a single recursion proof;
/// `verify_final` checks that one proof (plus public-transcript
/// recomputation) and returns the boundary spanning the whole run.
#[test]
fn test_final_proof_of_10m_cycle_run() {
    prover::e2e::ensure_guest_built();
    let elf_path = prover::e2e::guest_bin_dir().join("long_run");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read long_run ELF");

    let reference = run(&elf_bytes, 20_000_000).expect("Failed to run long_run");
    assert!(
        reference.cycles > 10_000_000,
        "long_run must exceed 10M cycles, got {}",
        reference.cycles
    );

    // RangeCheck20 bounds per-segment clocks below 2^20.
    let segment_cycles = (1u32 << 20) - 1;
    let segments = run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 20_000_000)
        .expect("segmented run failed");
    assert!(segments.len() >= 10, "expected >= 10 segments");

    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());
    let proofs = prove_segments_with_channel::<Poseidon2M31MerkleChannel>(
        segments,
        PcsConfig::default(),
        &preprocessing,
    );
    let final_proof = prove_final(proofs, PcsConfig::default(), &preprocessing);

    let boundary = verify_final(final_proof, PcsConfig::default(), &preprocessing)
        .expect("final proof verification failed");
    assert_eq!(boundary.entry_pc, reference.initial_pc);
    assert_eq!(boundary.exit_pc, reference.final_pc);
    assert_eq!(boundary.exit_regs, reference.final_regs);
}

/// The simplest end-to-end case: a single small RISC-V execution proven as
/// one Poseidon2-channel segment, wrapped by `prove_final` into one recursion
/// proof, and checked by `verify_final` — the leaf-level
/// "stark-v proof -> AIR-verifier proof" step on its own.
#[test]
fn test_final_proof_of_single_small_segment() {
    prover::e2e::ensure_guest_built();
    let elf_path = prover::e2e::guest_bin_dir().join("mul_output");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output ELF");

    let reference = run(&elf_bytes, 10_000_000).expect("Failed to run mul_output");
    let (entry_pc, exit_pc, exit_regs) = (
        reference.initial_pc,
        reference.final_pc,
        reference.final_regs,
    );

    let config = PcsConfig::default();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(config);
    let proof =
        prove_rv32im_with_channel::<Poseidon2M31MerkleChannel>(reference, config, &preprocessing);

    let final_proof = prove_final(vec![proof], config, &preprocessing);
    let boundary =
        verify_final(final_proof, config, &preprocessing).expect("final proof verification failed");

    assert_eq!(
        (boundary.entry_pc, boundary.exit_pc, boundary.exit_regs),
        (entry_pc, exit_pc, exit_regs),
    );
}

#[test]
fn test_final_proof_rejects_tampered_queried_value() {
    let mut final_proof = shared_final().0.clone();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());

    // A forged queried value changes the recomputed leaf digest, which the
    // in-AIR opening paths no longer anchor.
    let column = &mut final_proof.segments[0].stark_proof.0.queried_values.0[1][0];
    column[0] += stwo::core::fields::m31::BaseField::from(1);

    assert!(verify_final(final_proof, PcsConfig::default(), &preprocessing).is_err());
}

#[test]
fn test_final_proof_rejects_forged_root_claim() {
    let mut final_proof = shared_final().0.clone();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());

    // Root claims must equal the transcript commitments exactly.
    final_proof.recursion_proof.roots[0].root[0] ^= 1;

    assert!(verify_final(final_proof, PcsConfig::default(), &preprocessing).is_err());
}

#[test]
fn test_final_proof_rejects_boundary_break() {
    let mut final_proof = shared_final().0.clone();
    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());

    // Tampering a segment's public exit state breaks its own transcript
    // binding (public data is the first thing the channel absorbs).
    final_proof.segments[0].public_data.final_pc ^= 4;

    assert!(verify_final(final_proof, PcsConfig::default(), &preprocessing).is_err());
}
