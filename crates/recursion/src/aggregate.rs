//! 2-to-1 aggregation with recursion-proof leaves (docs/recursion.md, M6).
//!
//! Each segment leaf carries a recursion proof of its composition check —
//! the inner verifier's component-coupled core, proven in-AIR from the
//! proof's transcript — alongside its boundary. Aggregation verifies the
//! constant-size recursion proof per leaf and folds boundaries pairwise to
//! the root, exactly as the host-only tree does.
//!
//! Trust split at this stage: the composition check (all inner constraints,
//! LogUp columns, alpha weighting, vanishing denominators) is attested by
//! the recursion proof; the inner proof's FRI/Merkle openings, LogUp-sum,
//! and PoW checks run host-side via `verify_rv32im` inside
//! `verify_segment_composition`. Each further in-AIR binding (draws, FRI
//! queries) moves work from the host remainder into the recursion proof
//! without changing this structure.

use prover::Proof;
use prover::{PcsConfig, Preprocessing};
use stwo::core::channel::MerkleChannel;
use stwo::core::fields::qm31::SecureField;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};

use crate::binding::CompositionRecorder;
use crate::circuit::lower_arena;
use crate::prover::{RecursionProof, RecursionTraces, prove_recursion, verify_recursion};
use crate::recorder::Rec;
use crate::transcript::composition_binding_data;

pub use crate::boundary::Boundary;

/// A segment leaf: its boundary and the recursion proof of its composition
/// check.
pub struct SegmentNode {
    pub boundary: Boundary,
    pub recursion_proof: RecursionProof<<Blake2sMerkleChannel as MerkleChannel>::H>,
}

/// Prove a segment's composition check in the recursion AIR.
pub fn prove_segment_composition(
    proof: &Proof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> SegmentNode {
    let data =
        composition_binding_data(proof, config, preprocessing).expect("transcript replay failed");
    let recorder = CompositionRecorder::new(&data).record(&data.components);
    assert_eq!(
        recorder.accumulation.value(),
        data.claimed_composition,
        "recorded composition must match the proof's OODS claim"
    );
    let output = match &recorder.accumulation {
        Rec::Node { id, .. } => *id,
        Rec::Const(_) => panic!("composition accumulated to a constant"),
    };

    let mut traces = RecursionTraces::default();
    let claim = lower_arena(
        &mut traces,
        0,
        &recorder.arena.borrow(),
        output,
        0,
        SecureField::default(),
    );
    let recursion_proof = prove_recursion(traces, vec![], vec![], vec![], vec![claim], config);

    SegmentNode {
        boundary: Boundary::of_segment(proof),
        recursion_proof,
    }
}

/// Verify a segment leaf: the full host verification of the inner proof
/// (commitments, FRI, LogUp sum, proof of work) plus the recursion proof of
/// its composition check against the canonical circuit re-recorded from the
/// public transcript.
pub fn verify_segment_composition(
    node: SegmentNode,
    proof: &Proof<Blake2sMerkleHasher>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<(), prover::VerificationError> {
    // Host remainder: everything the in-AIR bindings have not yet absorbed.
    // Without this the sampled values are unanchored to the commitments.
    prover::verify_rv32im(proof.clone(), config, preprocessing)?;

    let data = composition_binding_data(proof, config, preprocessing)?;
    let recorder = CompositionRecorder::new(&data).record(&data.components);
    let output = match &recorder.accumulation {
        Rec::Node { id, .. } => *id,
        Rec::Const(_) => panic!("composition accumulated to a constant"),
    };
    // The canonical circuit must claim exactly the proof's composition value.
    if recorder.accumulation.value() != data.claimed_composition {
        return Err(prover::VerificationError::Stwo(
            stwo::core::verifier::VerificationError::OodsNotMatching,
        ));
    }
    verify_recursion(node.recursion_proof, &[(recorder.arena, output)], config)
        .map_err(prover::VerificationError::from)
}

/// Aggregate segment proofs with recursion-proof leaves: verify each leaf's
/// recursion proof and fold the boundaries pairwise up the 2-to-1 tree.
pub fn aggregate_with_recursion(
    segments: Vec<(Proof<Blake2sMerkleHasher>, SegmentNode)>,
    config: PcsConfig,
    preprocessing: &Preprocessing,
) -> Result<Boundary, prover::VerificationError> {
    assert!(!segments.is_empty(), "cannot aggregate zero segments");

    let mut level: Vec<Boundary> = Vec::with_capacity(segments.len());
    for (proof, node) in segments {
        level.push(node.boundary.clone());
        verify_segment_composition(node, &proof, config, preprocessing)?;
    }

    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for pair in level.chunks(2) {
            match pair {
                [left, right] => next.push(left.chain(right).map_err(|what| {
                    prover::VerificationError::SegmentChainMismatch {
                        prev: 0,
                        next: 1,
                        what,
                    }
                })?),
                [odd] => next.push(odd.clone()),
                _ => unreachable!("chunks(2)"),
            }
        }
        level = next;
    }
    Ok(level.pop().expect("non-empty"))
}
