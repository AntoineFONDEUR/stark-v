//! Real-proof composition binding (docs/recursion.md, M5): the recorded
//! circuit over an actual stark-v proof's sampled values must reproduce the
//! composition value the proof claims at the OODS point.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use prover::{PcsConfig, prove_rv32im};
use recursion::binding::CompositionRecorder;
use recursion::transcript::composition_binding_data;
use runner::run;

#[test]
fn test_recorded_composition_matches_real_proof() {
    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");

    let preprocessing = prover::preprocess(PcsConfig::default());
    let proof = prove_rv32im(run_result, PcsConfig::default(), &preprocessing);

    let data = composition_binding_data(&proof, PcsConfig::default(), &preprocessing)
        .expect("transcript replay failed");

    // Record every inner component's point evaluation into one arena —
    // through the same evaluate() the prover and host verifier run.
    let recorder = CompositionRecorder::new(&data).record(&data.components);

    assert_eq!(
        recorder.accumulation.value(),
        data.claimed_composition,
        "recorded composition circuit must reproduce the proof's OODS claim"
    );
    // The arena is a real circuit, ready for lowering.
    assert!(recorder.arena.borrow().nodes.len() > 1000);
}

/// The full M5 loop on real data: record the composition check of an actual
/// stark-v proof, lower the circuit into recursion rows, prove the recursion
/// AIR, and verify it against the re-recorded canonical circuit.
#[test]
fn test_real_proof_composition_proven_in_recursion_air() {
    use num_traits::Zero;
    use recursion::circuit::lower_arena;
    use recursion::prover::{RecursionTraces, prove_recursion, verify_recursion};
    use recursion::recorder::Rec;
    use stwo::core::fields::qm31::SecureField;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");

    let preprocessing = prover::preprocess(PcsConfig::default());
    let proof = prove_rv32im(run_result, PcsConfig::default(), &preprocessing);
    let data = composition_binding_data(&proof, PcsConfig::default(), &preprocessing)
        .expect("transcript replay failed");

    let recorder = CompositionRecorder::new(&data).record(&data.components);
    let output = match &recorder.accumulation {
        Rec::Node { id, .. } => *id,
        Rec::Const(_) => panic!("constant accumulation"),
    };
    assert_eq!(recorder.accumulation.value(), data.claimed_composition);

    // Lower the real circuit and prove it in the recursion AIR. The
    // re-record context is the multi-component binding, so the
    // single-component re-record fields of the claim are unused here.
    let mut traces = RecursionTraces::default();
    let claim = lower_arena(
        &mut traces,
        0,
        &recorder.arena.borrow(),
        output,
        0,
        SecureField::zero(),
    );
    let recursion_proof = prove_recursion(
        traces,
        vec![],
        vec![],
        vec![],
        vec![claim],
        PcsConfig::default(),
    );

    // Verifier side: re-record the canonical circuit from the proof data.
    let verifier_recorder = CompositionRecorder::new(&data).record(&data.components);
    let verifier_output = match &verifier_recorder.accumulation {
        Rec::Node { id, .. } => *id,
        Rec::Const(_) => panic!("constant accumulation"),
    };
    assert!(!data.claimed_composition.is_zero());
    verify_recursion(
        recursion_proof,
        &[(verifier_recorder.arena, verifier_output)],
        PcsConfig::default(),
    )
    .expect("real-proof composition recursion verification failed");
}

/// The 2-to-1 tree with recursion-proof leaves (docs/recursion.md, M6): a
/// real execution split into segments, each segment's composition check
/// proven in the recursion AIR, leaves verified through their recursion
/// proofs, and boundaries folded to a root spanning the whole run.
#[test]
fn test_aggregate_with_recursion_proof_leaves() {
    use prover::e2e::prove_segments;
    use recursion::aggregate::{aggregate_with_recursion, prove_segment_composition};
    use runner::run_segments_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");

    let reference = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");
    let segment_cycles = u32::try_from(reference.cycles / 2 + 1).expect("fits u32");
    let segments = run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 10_000_000)
        .expect("segmented run failed");
    // Two halves plus the forced boundary at the first output-region store.
    assert_eq!(segments.len(), 3);

    let preprocessing = prover::preprocess(PcsConfig::default());
    let proofs = prove_segments(segments, PcsConfig::default(), &preprocessing);

    // Each leaf: a recursion proof of the segment's composition check.
    let nodes: Vec<_> = proofs
        .iter()
        .map(|proof| {
            let node = prove_segment_composition(proof, PcsConfig::default(), &preprocessing);
            (proof.clone(), node)
        })
        .collect();

    let root = aggregate_with_recursion(nodes, PcsConfig::default(), &preprocessing)
        .expect("recursion-leaf aggregation failed");
    assert_eq!(root.entry_pc, reference.initial_pc);
    assert_eq!(root.exit_pc, reference.final_pc);
    assert_eq!(root.exit_regs, reference.final_regs);
}

/// The complete recursion pipeline over a >10M-cycle RISC-V run: segment the
/// execution, prove every segment, prove each segment's composition check in
/// the recursion AIR, and aggregate the recursion-verified leaves up the
/// 2-to-1 tree to a root boundary spanning the whole run.
#[test]
fn test_recursion_pipeline_proves_10m_cycle_run() {
    use prover::e2e::prove_segments;
    use recursion::aggregate::{aggregate_with_recursion, prove_segment_composition};
    use runner::run_segments_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("long_run");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read long_run ELF");

    let reference = run(&elf_bytes, 20_000_000).expect("Failed to run long_run");
    assert!(
        reference.cycles >= 10_000_000,
        "long_run must exceed 10M cycles, got {}",
        reference.cycles
    );

    // Segments bounded by the range-checkable clock window.
    let segment_cycles = (1u32 << 20) - 1;
    let segments = run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 20_000_000)
        .expect("segmented run failed");
    assert!(segments.len() >= 10, "expected >= 10 segments");

    let preprocessing = prover::preprocess(PcsConfig::default());
    let proofs = prove_segments(segments, PcsConfig::default(), &preprocessing);

    let nodes: Vec<_> = proofs
        .iter()
        .map(|proof| {
            let node = prove_segment_composition(proof, PcsConfig::default(), &preprocessing);
            (proof.clone(), node)
        })
        .collect();

    let root = aggregate_with_recursion(nodes, PcsConfig::default(), &preprocessing)
        .expect("recursion aggregation failed");
    assert_eq!(root.entry_pc, reference.initial_pc);
    assert_eq!(root.exit_pc, reference.final_pc);
    assert_eq!(root.exit_regs, reference.final_regs);
}
