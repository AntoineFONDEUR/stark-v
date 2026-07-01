//! The single final proof of a segmented execution.
//!
//! `prove_final` folds an arbitrary number of segment proofs into ONE
//! recursion-AIR proof attesting, for every segment, (a) the composition
//! check — the inner constraint system, recorded from the same
//! `define_trace_tables!`-generated `evaluate()` the prover ran — and (b)
//! every Merkle opening of the inner commitment scheme, trace trees and FRI
//! layer trees alike. The Merkle decommitments are *dropped* from the final
//! artifact: the recursion proof replaces them.
//!
//! `verify_final` is the only verification entry point: it replays the
//! public transcripts natively (Fiat-Shamir hashing, DEEP quotients, FRI
//! folds, last-layer and proof-of-work checks — deterministic recomputation
//! over public data), checks the segment boundaries chain, and verifies the
//! ONE recursion proof. It never sees a decommitment and never verifies an
//! inner proof.

use crate::boundary::Boundary;
use crate::transcript::full_binding_data_with_channel;
use prover::Proof;
use prover::poseidon2_channel::{Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher};
use prover::{PcsConfig, Preprocessing};
use stwo::core::channel::MerkleChannel;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::vcs_lifted::verifier::MerkleDecommitmentLifted;
use stwo::core::verifier::VerificationError as StwoVerificationError;

use crate::binding::CompositionRecorder;
use crate::circuit::lower_arena;
use crate::openings::{TREE_ID_STRIDE, replay_pcs_openings};
use crate::prover::{RecursionProof, RecursionTraces, prove_recursion, verify_recursion};
use crate::recorder::Rec;

/// The single final proof: one recursion proof over all segments, plus the
/// segments' public bodies (no decommitments anywhere).
#[derive(Clone)]
pub struct FinalProof {
    /// One recursion proof: all composition circuits and Merkle openings.
    pub recursion_proof: RecursionProof<<Blake2sMerkleChannel as MerkleChannel>::H>,
    /// Per segment, the public proof body: claims, commitments, sampled and
    /// queried values, FRI witness values, last layer, proof-of-work nonces.
    /// Decommitments are stripped — the recursion proof carries them.
    pub segments: Vec<Proof<Poseidon2M31MerkleHasher>>,
}

fn invalid(what: &str) -> prover::VerificationError {
    prover::VerificationError::Stwo(StwoVerificationError::InvalidStructure(what.to_string()))
}

/// Remove every Merkle decommitment from a proof body: the final artifact
/// carries openings as a recursion proof, not as hash witnesses.
fn strip_decommitments(proof: &mut Proof<Poseidon2M31MerkleHasher>) {
    let scheme_proof = &mut proof.stark_proof.0;
    for decommitment in scheme_proof.decommitments.0.iter_mut() {
        *decommitment = MerkleDecommitmentLifted::empty();
    }
    scheme_proof.fri_proof.first_layer.decommitment = MerkleDecommitmentLifted::empty();
    for layer in &mut scheme_proof.fri_proof.inner_layers {
        layer.decommitment = MerkleDecommitmentLifted::empty();
    }
}

/// Fold segment proofs into the single final proof.
///
/// # Panics
///
/// Panics if any segment proof is malformed (they are this prover's own
/// freshly generated proofs).
pub fn prove_final(
    mut proofs: Vec<Proof<Poseidon2M31MerkleHasher>>,
    config: PcsConfig,
    preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
) -> FinalProof {
    assert!(!proofs.is_empty(), "cannot prove zero segments");

    let mut traces = RecursionTraces::default();
    let mut roots = Vec::new();
    let mut leaves = Vec::new();
    let mut circuits = Vec::new();

    for (segment, proof) in proofs.iter().enumerate() {
        let (data, pcs) = full_binding_data_with_channel::<Poseidon2M31MerkleChannel>(
            proof,
            config,
            preprocessing,
        )
        .expect("transcript replay failed");

        // Composition circuit: record the inner evaluate() over the proof's
        // sampled values and lower it into the shared traces.
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
        circuits.push(lower_arena(
            &mut traces,
            segment as u32,
            &recorder.arena.borrow(),
            output,
            0,
            stwo::core::fields::qm31::SecureField::default(),
        ));

        // Merkle openings: native value checks plus in-AIR path rows.
        let claims = replay_pcs_openings(
            &proof.stark_proof.0,
            &pcs,
            config,
            segment as u32 * TREE_ID_STRIDE,
            Some(&mut traces),
        )
        .expect("openings replay failed");
        roots.extend(claims.roots);
        leaves.extend(claims.leaves);
    }

    let recursion_proof = prove_recursion(traces, roots, leaves, vec![], circuits, config);

    for proof in &mut proofs {
        strip_decommitments(proof);
    }
    FinalProof {
        recursion_proof,
        segments: proofs,
    }
}

/// Verify the single final proof and return the root boundary spanning the
/// whole execution.
///
/// Host work is exclusively public-data recomputation: transcript hashing,
/// LogUp-sum and proof-of-work checks, DEEP quotients, FRI folds and the
/// last-layer check, leaf digests from the queried values, and boundary
/// chaining — plus ONE stwo verification of the recursion proof. No inner
/// proof is verified and no decommitment exists in the artifact.
pub fn verify_final(
    final_proof: FinalProof,
    config: PcsConfig,
    preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
) -> Result<Boundary, prover::VerificationError> {
    let FinalProof {
        recursion_proof,
        segments,
    } = final_proof;
    if segments.is_empty() {
        return Err(invalid("zero segments"));
    }
    if !recursion_proof.channels.is_empty() {
        return Err(invalid("unexpected channel claims"));
    }
    if recursion_proof.circuits.len() != segments.len() {
        return Err(invalid("one composition circuit per segment"));
    }

    let mut expected_roots = Vec::new();
    let mut expected_leaves = Vec::new();
    let mut arenas = Vec::new();
    let mut boundary: Option<Boundary> = None;

    for (segment, proof) in segments.iter().enumerate() {
        // Inner LogUp sum: components plus public data must cancel.
        use num_traits::Zero;
        let (data, pcs) = full_binding_data_with_channel::<Poseidon2M31MerkleChannel>(
            proof,
            config,
            preprocessing,
        )?;
        let total_sum = proof.interaction_claim.claimed_sum.total()
            + proof.public_data.logup_sum(&data.relations);
        if !total_sum.is_zero() {
            return Err(prover::VerificationError::InvalidLogupSum);
        }

        // Canonical composition circuit, re-recorded from the transcript.
        let recorder = CompositionRecorder::new(&data).record(&data.components);
        if recorder.accumulation.value() != data.claimed_composition {
            return Err(prover::VerificationError::Stwo(
                StwoVerificationError::OodsNotMatching,
            ));
        }
        let output = match &recorder.accumulation {
            Rec::Node { id, .. } => *id,
            Rec::Const(_) => return Err(invalid("composition accumulated to a constant")),
        };
        if recursion_proof.circuits[segment].circuit_id != segment as u32 {
            return Err(invalid("circuit ids must be the segment indices"));
        }
        arenas.push((recorder.arena, output));

        // Native post-OODS checks and the expected opening anchors.
        let claims = replay_pcs_openings(
            &proof.stark_proof.0,
            &pcs,
            config,
            segment as u32 * TREE_ID_STRIDE,
            None,
        )
        .map_err(|e| invalid(&e))?;
        expected_roots.extend(claims.roots);
        expected_leaves.extend(claims.leaves);

        // Boundary chaining.
        let segment_boundary = Boundary::of_segment(proof);
        boundary = Some(match boundary {
            None => segment_boundary,
            Some(prev) => prev.chain(&segment_boundary).map_err(|what| {
                prover::VerificationError::SegmentChainMismatch {
                    prev: segment - 1,
                    next: segment,
                    what,
                }
            })?,
        });
    }

    // The recursion proof must anchor exactly the openings this transcript
    // demands — roots from the commitments, leaves from the queried values.
    if recursion_proof.roots != expected_roots {
        return Err(invalid("root claims do not match the transcripts"));
    }
    if recursion_proof.leaves != expected_leaves {
        return Err(invalid("leaf claims do not match the queried values"));
    }

    verify_recursion(recursion_proof, &arenas, config).map_err(prover::VerificationError::from)?;

    Ok(boundary.expect("at least one segment"))
}
