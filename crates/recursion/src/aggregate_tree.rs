//! End-to-end n-to-1 recursive aggregation of a RISC-V execution.
//!
//! The pipeline mirrors how a real proof would be produced and shrunk:
//!
//! 1. **Continuation** — the run is split into segments bounded at 2^20 rows
//!    (the RangeCheck20 clock bound), each an independent stark-v statement.
//! 2. **Segment proofs** — every segment is proven over the Poseidon2-M31
//!    channel, the hash the recursion `merkle_path` component re-proves.
//! 3. **Base nodes** — segments are grouped `arity` at a time; each group is
//!    folded into one Poseidon2 *recursion leaf* attesting those segments'
//!    composition checks and openings in-AIR (the leaf analogue of
//!    [`crate::final_proof`], but emitting a recursion proof rather than a
//!    Blake2s root).
//! 4. **Tree** — the leaves fold `arity`-to-1 up [`prove_tree_compressed`] to
//!    one constant-size root.
//!
//! The fan-in `arity` is the tunable knob. A wider node packs more
//! verification work into one parent trace — closer to stwo's
//! peak-throughput cell budget — while keeping the root size independent of
//! the leaf count. The throughput-optimal value is machine-dependent
//! (RAM, cores, CPU generation); this module is the harness for measuring it,
//! not a claim about a universal optimum.

use std::time::Instant;

use prover::poseidon2_channel::{Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher};
use prover::{PcsConfig, Preprocessing, Proof};
use stwo::core::fields::qm31::SecureField;
use stwo::core::verifier::VerificationError;
use tracing::info;

use crate::binding::CompositionRecorder;
use crate::circuit::lower_arena;
use crate::node::{CompressedNode, prove_tree_compressed};
use crate::openings::{TREE_ID_STRIDE, replay_pcs_openings};
use crate::prover::{RecursionProof, RecursionTraces, prove_recursion_with_channel};
use crate::recorder::Rec;
use crate::transcript::full_binding_data_with_channel;

/// Fold a group of stark-v segment proofs into one Poseidon2 recursion leaf.
///
/// For each segment: record its composition through the inner `evaluate()`
/// and replay its Merkle/FRI openings as `merkle_path` rows, then prove ONE
/// recursion proof attesting them all. The result is itself a
/// [`RecursionProof`], so it is a valid leaf for [`prove_tree_compressed`].
pub fn prove_base_node(
    segments: &[Proof<Poseidon2M31MerkleHasher>],
    config: PcsConfig,
    preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
) -> Result<RecursionProof<Poseidon2M31MerkleHasher>, VerificationError> {
    if segments.is_empty() {
        return Err(VerificationError::InvalidStructure(
            "a base node folds at least one segment".to_string(),
        ));
    }
    let mut traces = RecursionTraces::default();
    let mut circuits = Vec::with_capacity(segments.len());
    let mut roots = Vec::new();
    let mut leaves = Vec::new();

    for (index, proof) in segments.iter().enumerate() {
        let (data, pcs) = full_binding_data_with_channel::<Poseidon2M31MerkleChannel>(
            proof,
            config,
            preprocessing,
        )
        .map_err(|e| {
            VerificationError::InvalidStructure(format!("transcript replay failed: {e:?}"))
        })?;
        let recorder = CompositionRecorder::new(&data).record(&data.components);
        if recorder.accumulation.value() != data.claimed_composition {
            return Err(VerificationError::InvalidStructure(
                "segment composition does not match its claim".to_string(),
            ));
        }
        let output = match &recorder.accumulation {
            Rec::Node { id, .. } => *id,
            Rec::Const(_) => {
                return Err(VerificationError::InvalidStructure(
                    "segment composition accumulated to a constant".to_string(),
                ));
            }
        };
        circuits.push(lower_arena(
            &mut traces,
            index as u32,
            &recorder.arena.borrow(),
            output,
            0,
            SecureField::default(),
        ));

        let claims = replay_pcs_openings(
            &proof.stark_proof.0,
            &pcs,
            config,
            index as u32 * TREE_ID_STRIDE,
            Some(&mut traces),
        )
        .map_err(VerificationError::InvalidStructure)?;
        roots.extend(claims.roots);
        leaves.extend(claims.leaves);
    }

    Ok(prove_recursion_with_channel::<Poseidon2M31MerkleChannel>(
        traces,
        roots,
        leaves,
        vec![],
        circuits,
        config,
    ))
}

/// Prove a whole RISC-V execution as one constant-size n-to-1 recursion root.
///
/// `segment_cycles` bounds each continuation segment (≤ 2^20 for the clock
/// range check); `arity` is the fan-in at every aggregation level. Returns
/// the root [`CompressedNode`], verifiable with
/// [`crate::node::verify_node_compressed`]. Per-phase wall-clock is emitted at
/// `info` level so a caller with a tracing subscriber can read the timings.
///
/// Requires the run to split into at least two base groups (otherwise there is
/// no tree to fold); size `segment_cycles` accordingly.
pub fn prove_guest_recursive(
    elf_bytes: &[u8],
    input: &[u8],
    arity: usize,
    segment_cycles: u32,
    max_cycles: u64,
    config: PcsConfig,
    preprocessing: &Preprocessing<Poseidon2M31MerkleHasher>,
) -> Result<CompressedNode, VerificationError> {
    let invalid = |what: &str| VerificationError::InvalidStructure(what.to_string());

    let t = Instant::now();
    let segments =
        runner::run_segments_with_input(elf_bytes, input, Some(segment_cycles), max_cycles)
            .map_err(|e| invalid(&format!("segmented run failed: {e:?}")))?;
    info!(
        segments = segments.len(),
        elapsed_ms = t.elapsed().as_millis(),
        "continuation"
    );

    let t = Instant::now();
    let proofs = prover::e2e::prove_segments_with_channel::<Poseidon2M31MerkleChannel>(
        segments,
        config,
        preprocessing,
    );
    info!(
        proofs = proofs.len(),
        elapsed_ms = t.elapsed().as_millis(),
        "segment proofs"
    );

    let t = Instant::now();
    let mut leaves = Vec::with_capacity(proofs.len().div_ceil(arity));
    for group in proofs.chunks(arity) {
        leaves.push(prove_base_node(group, config, preprocessing)?);
    }
    info!(
        leaves = leaves.len(),
        arity,
        elapsed_ms = t.elapsed().as_millis(),
        "base nodes"
    );

    if leaves.len() < 2 {
        return Err(invalid(
            "run produced fewer than two base groups; lower segment_cycles or arity",
        ));
    }

    let t = Instant::now();
    let root = prove_tree_compressed(leaves, arity, config)?;
    info!(
        children = root.children.len(),
        elapsed_ms = t.elapsed().as_millis(),
        "tree fold"
    );
    Ok(root)
}
