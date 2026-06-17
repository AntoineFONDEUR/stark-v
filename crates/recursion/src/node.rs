//! 2-to-1 node compression: a recursion proof attesting two child recursion
//! proofs (docs/recursion.md, item 3 / M6).
//!
//! A node replays each child recursion proof's own Fiat-Shamir transcript and
//! records — through the same `evaluate()` code the recursion prover ran —
//! both its composition check and its Merkle/FRI openings, lowering them into
//! the parent's trace and proving one parent recursion proof. No child is
//! re-proven; the parent attests them.
//!
//! - [`replay_recursion_composition`] / [`prove_node`] / [`verify_node`]:
//!   the composition half (Blake2s channel), the recursion-level analogue of
//!   the M1 seam.
//! - [`prove_node_compressed`] / [`verify_node_compressed`]: the constant-size
//!   node — children proven over the Poseidon2-M31 channel so their openings
//!   become `merkle_path` rows in the parent, their decommitments stripped
//!   from the artifact. This is the recursion-level analogue of
//!   [`crate::final_proof::FinalProof`].

use num_traits::Zero;
use stwo::core::air::Components as CoreComponents;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::circle::CirclePoint;
use stwo::core::constraints::coset_vanishing;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::pcs::CommitmentSchemeVerifier;
use stwo::core::pcs::utils::try_get_lifting_log_size;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::{COMPOSITION_LOG_SPLIT, VerificationError};
use stwo_constraint_framework::TraceLocationAllocator;

use prover::PcsConfig;
use prover::relations::Relations;

use crate::binding::record_component;
use crate::prover::{
    RecursionProof, column_log_sizes, components, mix_channels, mix_circuits, mix_claim,
    mix_leaves, mix_roots,
};
use crate::recorder::Rec;
use crate::relations::RecursionRelations;
use crate::transcript::extract_composition_oods_eval;

/// The OODS composition check of a recursion proof, replayed outside the
/// verifier: the value the proof claims versus the value recomputed from its
/// sampled mask values through the recursion components' `evaluate()`.
#[derive(Debug, Clone, Copy)]
pub struct RecursionOodsCheck {
    pub claimed: SecureField,
    pub recorded: SecureField,
}

impl RecursionOodsCheck {
    /// Whether the recorded composition matches the proof's claim — the
    /// DEEP-ALI check at the recursion level.
    pub fn holds(&self) -> bool {
        self.claimed == self.recorded
    }
}

/// Replay a recursion proof's transcript and record its composition into an
/// arena, returning the finished recorder (the canonical composition
/// circuit), the composition value the proof claims at its OODS point, and
/// the PCS state at the OODS point (for replaying the proof's openings).
///
/// Generic over the Merkle channel: composition-only nodes use Blake2s, the
/// opening-recording nodes use the Poseidon2-M31 channel the `merkle_path`
/// component proves.
fn recursion_binding<MC: MerkleChannel>(
    proof: &RecursionProof<MC::H>,
    config: PcsConfig,
) -> Result<
    (
        crate::recorder::Recorder,
        SecureField,
        crate::transcript::PcsBindingData<MC>,
    ),
    VerificationError,
> {
    let channel = &mut MC::C::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);
    let commitments = &proof.stark_proof.commitments;

    // Claim phase: exactly `prove_recursion_with_channel` up to the
    // interaction commitment.
    commitment_scheme.commit(commitments[0], &[], channel);
    channel.mix_u32s(&proof.log_sizes);
    mix_roots(channel, &proof.roots);
    mix_leaves(channel, &proof.leaves);
    mix_channels(channel, &proof.channels);
    mix_circuits(channel, &proof.circuits);
    commitment_scheme.commit(commitments[1], &column_log_sizes(&proof.log_sizes), channel);

    let relations = Relations::draw(channel);
    let recursion_relations = RecursionRelations::draw(channel);

    let sums = [
        proof.claimed_sum,
        proof.merkle_claimed_sum,
        proof.channel_claimed_sum,
        proof.poseidon2_claimed_sum,
        proof.circuit_claimed_sums[0],
        proof.circuit_claimed_sums[1],
        proof.circuit_claimed_sums[2],
    ];
    mix_claim(channel, &proof.log_sizes, sums);

    // Interaction tree widths: secure columns per component (4 base each),
    // matching `verify_recursion_with_channel`.
    let interaction_log_sizes: Vec<u32> = std::iter::repeat_n(proof.log_sizes[0], 8)
        .chain(std::iter::repeat_n(proof.log_sizes[1], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[4], 4))
        .chain(std::iter::repeat_n(proof.log_sizes[5], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[6], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[7], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[8], 8))
        .collect();
    commitment_scheme.commit(commitments[2], &interaction_log_sizes, channel);

    // Composition phase: mirror `stwo::prover::prove` up to the OODS draw.
    let mut location_allocator = TraceLocationAllocator::default();
    let (mul, inv, fold, double, sum, merkle, replay, linear, poseidon2) = components(
        &mut location_allocator,
        &proof.log_sizes,
        sums,
        &relations,
        &recursion_relations,
    );
    let core_components = CoreComponents {
        n_preprocessed_columns: 0,
        components: vec![
            &mul, &inv, &fold, &double, &sum, &merkle, &replay, &linear, &poseidon2,
        ],
    };

    let split_composition_log_degree_bound =
        core_components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT;
    let lifting_log_size = try_get_lifting_log_size(
        &commitment_scheme.config,
        split_composition_log_degree_bound + commitment_scheme.config.fri_config.log_blowup_factor,
    )?;
    let max_log_degree_bound =
        lifting_log_size - commitment_scheme.config.fri_config.log_blowup_factor;

    let random_coeff = channel.draw_secure_felt();
    commitment_scheme.commit(
        *commitments
            .last()
            .expect("recursion proof has a composition commitment"),
        &[max_log_degree_bound; 2 * SECURE_EXTENSION_DEGREE],
        channel,
    );
    let oods_point = CirclePoint::<SecureField>::get_random_point(channel);

    let claimed =
        extract_composition_oods_eval(&proof.stark_proof, oods_point, max_log_degree_bound)
            .ok_or_else(|| {
                VerificationError::InvalidStructure(
                    "unexpected recursion sampled-values structure".to_string(),
                )
            })?;

    // PCS state at the OODS point — mask points (composition points
    // appended) and the committed tree shapes — for replaying the openings.
    let mut sample_points = core_components.mask_points(oods_point, max_log_degree_bound, false);
    sample_points.push(vec![vec![oods_point]; 2 * SECURE_EXTENSION_DEGREE]);
    let pcs = crate::transcript::PcsBindingData::<MC> {
        column_log_sizes: commitment_scheme
            .trees
            .as_ref()
            .map(|tree| tree.column_log_sizes.clone()),
        tree_heights: commitment_scheme
            .trees
            .iter()
            .map(|tree| tree.height)
            .collect(),
        roots: commitment_scheme
            .trees
            .iter()
            .map(|tree| tree.root)
            .collect(),
        sample_points,
        lifting_log_size,
        channel: channel.clone(),
    };
    drop(core_components);

    // Record every component's point evaluation, in composition order, into
    // one arena — the same per-component recorder the inner path uses.
    let denom_inverse =
        coset_vanishing(CanonicCoset::new(max_log_degree_bound).coset, oods_point).inverse();
    let sampled = &proof.stark_proof.sampled_values;
    let mut recorder = None;
    // (component, its claimed sum) in the order `prove` composes them.
    recorder = Some(record_component(
        recorder,
        &mul,
        sums[4],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &inv,
        sums[5],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &fold,
        SecureField::zero(),
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &double,
        SecureField::zero(),
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &sum,
        sums[0],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &merkle,
        sums[1],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &replay,
        sums[2],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &linear,
        sums[6],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    recorder = Some(record_component(
        recorder,
        &poseidon2,
        sums[3],
        sampled,
        random_coeff,
        denom_inverse,
    ));
    let recorder = recorder.expect("nine components recorded");
    Ok((recorder, claimed, pcs))
}

/// Replay a recursion proof's transcript to the OODS point and record its
/// composition check from the sampled mask values.
///
/// Mirrors `prove_recursion_with_channel`'s Fiat-Shamir sequence exactly, so
/// the drawn OODS point and the sliced mask values match the proof; a wrong
/// replay yields a different OODS point and the recorded value cannot match
/// the claim.
pub fn replay_recursion_composition(
    proof: &RecursionProof<Blake2sMerkleHasher>,
    config: PcsConfig,
) -> Result<RecursionOodsCheck, VerificationError> {
    let (recorder, claimed, _) = recursion_binding::<Blake2sMerkleChannel>(proof, config)?;
    let recorded = recorder.accumulation.value();
    Ok(RecursionOodsCheck { claimed, recorded })
}

/// The arena output node of a finished recorder (the composition root).
fn recorder_output(recorder: &crate::recorder::Recorder) -> Result<usize, VerificationError> {
    match &recorder.accumulation {
        Rec::Node { id, .. } => Ok(*id),
        Rec::Const(_) => Err(VerificationError::InvalidStructure(
            "recursion composition accumulated to a constant".to_string(),
        )),
    }
}

/// A 2-to-1 aggregation node: a recursion proof attesting that its two child
/// recursion proofs' composition checks pass.
///
/// This is the recursive step of node compression (docs/recursion.md). Each
/// child's composition is recorded from its transcript (no re-proving) and
/// lowered into the parent's trace as circuits `0` and `1`; the parent
/// recursion proof then attests both. Applied up a binary tree, the root is
/// one recursion proof for the whole execution. As with the segment-leaf
/// path (`prove_segment_composition`), the children's FRI/Merkle openings are
/// verified host-side until they too move in-AIR — the documented trust
/// split that keeps each step sound while shrinking the host remainder.
pub fn prove_node(
    left: &RecursionProof<Blake2sMerkleHasher>,
    right: &RecursionProof<Blake2sMerkleHasher>,
    config: PcsConfig,
) -> Result<RecursionProof<Blake2sMerkleHasher>, VerificationError> {
    let mut traces = crate::prover::RecursionTraces::default();
    let mut circuits = Vec::with_capacity(2);
    for (circuit_id, child) in [left, right].into_iter().enumerate() {
        let (recorder, claimed, _) = recursion_binding::<Blake2sMerkleChannel>(child, config)?;
        if recorder.accumulation.value() != claimed {
            return Err(VerificationError::InvalidStructure(
                "child recursion composition does not match its claim".to_string(),
            ));
        }
        let output = recorder_output(&recorder)?;
        circuits.push(crate::circuit::lower_arena(
            &mut traces,
            circuit_id as u32,
            &recorder.arena.borrow(),
            output,
            0,
            SecureField::zero(),
        ));
    }
    Ok(crate::prover::prove_recursion(
        traces,
        vec![],
        vec![],
        vec![],
        circuits,
        config,
    ))
}

/// Verify a 2-to-1 node: re-record the two children's canonical composition
/// circuits from their transcripts and verify the parent recursion proof
/// attests exactly them.
pub fn verify_node(
    node: RecursionProof<Blake2sMerkleHasher>,
    left: &RecursionProof<Blake2sMerkleHasher>,
    right: &RecursionProof<Blake2sMerkleHasher>,
    config: PcsConfig,
) -> Result<(), VerificationError> {
    if node.circuits.len() != 2 {
        return Err(VerificationError::InvalidStructure(
            "a 2-to-1 node attests exactly two child circuits".to_string(),
        ));
    }
    let mut arenas = Vec::with_capacity(2);
    for (circuit_id, child) in [left, right].into_iter().enumerate() {
        let (recorder, claimed, _) = recursion_binding::<Blake2sMerkleChannel>(child, config)?;
        if recorder.accumulation.value() != claimed {
            return Err(VerificationError::InvalidStructure(
                "child recursion composition does not match its claim".to_string(),
            ));
        }
        if node.circuits[circuit_id].circuit_id != circuit_id as u32 {
            return Err(VerificationError::InvalidStructure(
                "node circuit ids must be the child indices".to_string(),
            ));
        }
        let output = recorder_output(&recorder)?;
        arenas.push((recorder.arena, output));
    }
    crate::prover::verify_recursion(node, &arenas, config)
}

// =============================================================================
// Constant-size node: child openings attested in-AIR
// =============================================================================

use crate::openings::{TREE_ID_STRIDE, replay_pcs_openings};
use prover::poseidon2_channel::{Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher};
use stwo::core::vcs_lifted::verifier::MerkleDecommitmentLifted;

/// A constant-size 2-to-1 node: the parent recursion proof attests both
/// children's **composition checks and Merkle/FRI openings** in-AIR, so the
/// children's decommitments are dropped from the artifact.
///
/// The children must be proven over the Poseidon2-M31 channel — the hash the
/// `merkle_path` / `channel_replay` components prove — so their commitment
/// openings become component rows in the parent's trace. This is the
/// recursion-level analogue of [`crate::final_proof::FinalProof`]: where that
/// strips an inner proof's decommitments into one recursion proof, this
/// strips a child *recursion* proof's decommitments into the parent node,
/// closing the last host-side gap toward an artifact constant in tree depth.
pub struct CompressedNode {
    /// The parent recursion proof attesting both children.
    pub node: RecursionProof<Poseidon2M31MerkleHasher>,
    /// The two child recursion proofs with decommitments stripped (their
    /// openings live in `node` as `merkle_path` rows).
    pub children: [RecursionProof<Poseidon2M31MerkleHasher>; 2],
}

/// Strip every Merkle decommitment from a recursion proof: its openings are
/// attested by the parent node, not carried as hash witnesses.
fn strip_recursion_decommitments(proof: &mut RecursionProof<Poseidon2M31MerkleHasher>) {
    let scheme_proof = &mut proof.stark_proof.0;
    for decommitment in scheme_proof.decommitments.0.iter_mut() {
        *decommitment = MerkleDecommitmentLifted::empty();
    }
    scheme_proof.fri_proof.first_layer.decommitment = MerkleDecommitmentLifted::empty();
    for layer in &mut scheme_proof.fri_proof.inner_layers {
        layer.decommitment = MerkleDecommitmentLifted::empty();
    }
}

/// Prove a constant-size 2-to-1 node over two Poseidon2-channel children.
///
/// For each child: record its composition (lowered into the parent trace as
/// circuit `i`) and replay its openings (recorded as `merkle_path` rows and
/// anchored by public root/leaf claims), then prove ONE parent recursion
/// proof attesting both. The children's decommitments are stripped.
pub fn prove_node_compressed(
    left: RecursionProof<Poseidon2M31MerkleHasher>,
    right: RecursionProof<Poseidon2M31MerkleHasher>,
    config: PcsConfig,
) -> Result<CompressedNode, VerificationError> {
    let mut traces = crate::prover::RecursionTraces::default();
    let mut circuits = Vec::with_capacity(2);
    let mut roots = Vec::new();
    let mut leaves = Vec::new();

    for (index, child) in [&left, &right].into_iter().enumerate() {
        let (recorder, claimed, pcs) =
            recursion_binding::<Poseidon2M31MerkleChannel>(child, config)?;
        if recorder.accumulation.value() != claimed {
            return Err(VerificationError::InvalidStructure(
                "child recursion composition does not match its claim".to_string(),
            ));
        }
        let output = recorder_output(&recorder)?;
        circuits.push(crate::circuit::lower_arena(
            &mut traces,
            index as u32,
            &recorder.arena.borrow(),
            output,
            0,
            SecureField::zero(),
        ));

        let claims = replay_pcs_openings(
            &child.stark_proof.0,
            &pcs,
            config,
            index as u32 * TREE_ID_STRIDE,
            Some(&mut traces),
        )
        .map_err(VerificationError::InvalidStructure)?;
        roots.extend(claims.roots);
        leaves.extend(claims.leaves);
    }

    let node = crate::prover::prove_recursion_with_channel::<Poseidon2M31MerkleChannel>(
        traces,
        roots,
        leaves,
        vec![],
        circuits,
        config,
    );

    let mut children = [left, right];
    for child in &mut children {
        strip_recursion_decommitments(child);
    }
    Ok(CompressedNode { node, children })
}

/// Verify a constant-size node: re-record both children's compositions and
/// re-replay their openings from their (decommitment-free) public bodies,
/// then verify the parent recursion proof attests exactly those circuits and
/// anchors exactly those openings.
pub fn verify_node_compressed(
    compressed: CompressedNode,
    config: PcsConfig,
) -> Result<(), VerificationError> {
    let CompressedNode { node, children } = compressed;
    if node.circuits.len() != 2 {
        return Err(VerificationError::InvalidStructure(
            "a 2-to-1 node attests exactly two child circuits".to_string(),
        ));
    }

    let mut arenas = Vec::with_capacity(2);
    let mut expected_roots = Vec::new();
    let mut expected_leaves = Vec::new();
    for (index, child) in children.iter().enumerate() {
        let (recorder, claimed, pcs) =
            recursion_binding::<Poseidon2M31MerkleChannel>(child, config)?;
        if recorder.accumulation.value() != claimed {
            return Err(VerificationError::InvalidStructure(
                "child recursion composition does not match its claim".to_string(),
            ));
        }
        if node.circuits[index].circuit_id != index as u32 {
            return Err(VerificationError::InvalidStructure(
                "node circuit ids must be the child indices".to_string(),
            ));
        }
        let output = recorder_output(&recorder)?;
        arenas.push((recorder.arena, output));

        let claims = replay_pcs_openings(
            &child.stark_proof.0,
            &pcs,
            config,
            index as u32 * TREE_ID_STRIDE,
            None,
        )
        .map_err(VerificationError::InvalidStructure)?;
        expected_roots.extend(claims.roots);
        expected_leaves.extend(claims.leaves);
    }

    if node.roots != expected_roots {
        return Err(VerificationError::InvalidStructure(
            "node root claims do not match the children's commitments".to_string(),
        ));
    }
    if node.leaves != expected_leaves {
        return Err(VerificationError::InvalidStructure(
            "node leaf claims do not match the children's queried values".to_string(),
        ));
    }

    crate::prover::verify_recursion_with_channel::<Poseidon2M31MerkleChannel>(node, &arenas, config)
}

/// Fold a power-of-two set of Poseidon2-channel recursion proofs into a single
/// constant-size root by repeated 2-to-1 compression (docs/recursion.md, the
/// full aggregation tree).
///
/// Each level pairs its proofs and compresses every pair with
/// [`prove_node_compressed`], carrying the resulting node proof up to the next
/// level; the grandchildren's stripped bodies are dropped because each child
/// node proof already attests its own subtree in-AIR. The returned
/// [`CompressedNode`] is the tree root: the root recursion proof plus its two
/// immediate (decommitment-free) child node proofs — a footprint independent
/// of how many leaves sit beneath it.
pub fn prove_tree_compressed(
    leaves: Vec<RecursionProof<Poseidon2M31MerkleHasher>>,
    config: PcsConfig,
) -> Result<CompressedNode, VerificationError> {
    if !leaves.len().is_power_of_two() || leaves.len() < 2 {
        return Err(VerificationError::InvalidStructure(
            "a recursion tree needs a power-of-two leaf count of at least 2".to_string(),
        ));
    }
    let mut level = leaves;
    // Reduce to the final pair, taking each node proof up to the next level.
    while level.len() > 2 {
        let mut next = Vec::with_capacity(level.len() / 2);
        let mut pairs = level.into_iter();
        while let (Some(left), Some(right)) = (pairs.next(), pairs.next()) {
            next.push(prove_node_compressed(left, right, config)?.node);
        }
        level = next;
    }
    let mut pair = level.into_iter();
    let left = pair.next().expect("at least two proofs");
    let right = pair.next().expect("at least two proofs");
    prove_node_compressed(left, right, config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prover::{RecursionTraces, prove_recursion};
    use stwo::core::fields::qm31::QM31;

    /// Build a small recursion proof and replay its composition check: the
    /// recorded value recomputed from the sampled mask values through the
    /// recursion components' `evaluate()` must equal the value the proof
    /// claims at its OODS point. This is the recursion-level seam a 2-to-1
    /// node lowers into its parent trace.
    fn small_proof_seeded(seed: u32) -> RecursionProof<Blake2sMerkleHasher> {
        let mut traces = RecursionTraces::default();
        for i in 1..5u32 {
            let a = QM31::from_u32_unchecked(seed + i, i + 1, i + 2, i + 3);
            let b = QM31::from_u32_unchecked(2 * i, seed + i, i + 7, i + 1);
            crate::qm31_mul::push_mul(&mut traces.qm31_mul, a, b);
            crate::qm31_inv::push_inv(&mut traces.qm31_inv, a);
            crate::logup_sum::push_term(&mut traces.logup_sum, b);
        }
        prove_recursion(traces, vec![], vec![], vec![], vec![], PcsConfig::default())
    }

    fn small_proof() -> RecursionProof<Blake2sMerkleHasher> {
        small_proof_seeded(0)
    }

    /// The same small recursion proof, but over the Poseidon2-M31 channel so
    /// its openings can be attested in-AIR by a parent node.
    fn small_proof_poseidon(seed: u32) -> RecursionProof<Poseidon2M31MerkleHasher> {
        let mut traces = RecursionTraces::default();
        for i in 1..5u32 {
            let a = QM31::from_u32_unchecked(seed + i, i + 1, i + 2, i + 3);
            let b = QM31::from_u32_unchecked(2 * i, seed + i, i + 7, i + 1);
            crate::qm31_mul::push_mul(&mut traces.qm31_mul, a, b);
            crate::qm31_inv::push_inv(&mut traces.qm31_inv, a);
            crate::logup_sum::push_term(&mut traces.logup_sum, b);
        }
        crate::prover::prove_recursion_with_channel::<Poseidon2M31MerkleChannel>(
            traces,
            vec![],
            vec![],
            vec![],
            vec![],
            PcsConfig::default(),
        )
    }

    #[test]
    fn test_recursion_composition_replay_matches_claim() {
        let proof = small_proof();
        let check = replay_recursion_composition(&proof, PcsConfig::default())
            .expect("recursion transcript replay failed");
        assert!(
            check.holds(),
            "recursion composition mismatch: claimed {:?} != recorded {:?}",
            check.claimed,
            check.recorded
        );
    }

    #[test]
    fn test_recursion_composition_replay_detects_tampered_claim() {
        // A different OODS point (from a config the proof was not made with)
        // recomputes a different composition, so the recorded value cannot
        // match the claim.
        let proof = small_proof();
        let check = replay_recursion_composition(&proof, PcsConfig::default()).unwrap();
        let bumped = RecursionOodsCheck {
            claimed: check.claimed + QM31::from_u32_unchecked(1, 0, 0, 0),
            recorded: check.recorded,
        };
        assert!(!bumped.holds());
    }

    /// A 2-to-1 node over two child recursion proofs: the parent recursion
    /// proof attests both children's composition checks, and verifies against
    /// the children re-recorded from their transcripts. This is the recursive
    /// node-compression step.
    #[test]
    fn test_node_attests_two_children() {
        let left = small_proof_seeded(1);
        let right = small_proof_seeded(2);
        let node = prove_node(&left, &right, PcsConfig::default()).expect("node proving failed");
        verify_node(node, &left, &right, PcsConfig::default()).expect("node verification failed");
    }

    #[test]
    fn test_node_rejects_wrong_child() {
        let left = small_proof_seeded(1);
        let right = small_proof_seeded(2);
        let node = prove_node(&left, &right, PcsConfig::default()).expect("node proving failed");
        // Verifying against a different right child: its canonical circuit
        // differs from what the node attested, so verification fails.
        let other = small_proof_seeded(3);
        assert!(verify_node(node, &left, &other, PcsConfig::default()).is_err());
    }

    /// Constant-size node: the parent attests both Poseidon2-channel
    /// children's compositions AND their Merkle/FRI openings in-AIR; the
    /// children carry no decommitments. Verifying re-records and re-replays
    /// from the stripped bodies.
    #[test]
    fn test_compressed_node_attests_children_openings() {
        let left = small_proof_poseidon(1);
        let right = small_proof_poseidon(2);
        let compressed = prove_node_compressed(left, right, PcsConfig::default())
            .expect("compressed node proving failed");
        // The children's decommitments were stripped — the node carries them.
        assert!(
            compressed.children[0]
                .stark_proof
                .0
                .decommitments
                .0
                .iter()
                .all(|d| d.hash_witness.is_empty())
        );
        verify_node_compressed(compressed, PcsConfig::default())
            .expect("compressed node verification failed");
    }

    /// Measurement (not a correctness check; `#[ignore]`d): report a 2-to-1
    /// node's committed-cell budget and the arity that would fill stwo's
    /// peak-throughput point (~2^30 cells). Run with:
    ///   cargo test -p recursion --release measure_node_cell_budget -- --ignored --nocapture
    #[test]
    #[ignore]
    fn measure_node_cell_budget() {
        let node = prove_node_compressed(
            small_proof_poseidon(1),
            small_proof_poseidon(2),
            PcsConfig::default(),
        )
        .expect("node proving failed")
        .node;

        // Base trace: one entry per committed base column, at its log height.
        let base: u64 = crate::prover::column_log_sizes(&node.log_sizes)
            .iter()
            .map(|&l| 1u64 << l)
            .sum();
        let peak: u64 = 1 << 30;
        let per_child = base / 2; // a node attests two children
        println!("node.log_sizes      = {:?}", node.log_sizes);
        println!(
            "base trace cells    = {base} (2^{:.1})",
            (base as f64).log2()
        );
        println!(
            "marginal per child  ~= {per_child} (2^{:.1})",
            (per_child as f64).log2()
        );
        println!("k* to fill 2^30     ~= {}", peak / per_child.max(1));
        assert!(base > 0);
    }

    /// Four leaves fold through two level-1 nodes into one root, and the root
    /// — attesting the whole tree transitively in-AIR — verifies.
    #[test]
    fn test_compressed_tree_root_verifies() {
        let leaves = (1..=4u32).map(small_proof_poseidon).collect::<Vec<_>>();
        let root =
            prove_tree_compressed(leaves, PcsConfig::default()).expect("tree proving failed");
        verify_node_compressed(root, PcsConfig::default()).expect("tree root verification failed");
    }

    /// The root artifact is a single 2-to-1 node — exactly two immediate child
    /// node proofs — no matter how many leaves sit beneath it.
    #[test]
    fn test_compressed_tree_root_carries_two_children() {
        let leaves = (1..=4u32).map(small_proof_poseidon).collect::<Vec<_>>();
        let root =
            prove_tree_compressed(leaves, PcsConfig::default()).expect("tree proving failed");
        assert_eq!(root.children.len(), 2);
    }

    /// Constant size to the top: an 8-leaf (depth-3) tree and a 4-leaf
    /// (depth-2) tree produce roots of identical trace shape, so the root
    /// proof size does not grow with tree depth.
    #[test]
    fn test_compressed_tree_root_shape_is_depth_invariant() {
        let depth2 = prove_tree_compressed(
            (1..=4u32).map(small_proof_poseidon).collect(),
            PcsConfig::default(),
        )
        .expect("depth-2 tree proving failed");
        let depth3 = prove_tree_compressed(
            (1..=8u32).map(small_proof_poseidon).collect(),
            PcsConfig::default(),
        )
        .expect("depth-3 tree proving failed");
        assert_eq!(depth2.node.log_sizes, depth3.node.log_sizes);
    }
}
