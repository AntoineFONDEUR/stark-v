//! Prove and verify the recursion verifier AIR.
//!
//! Assembles the verifier-AIR components into a stwo proof: commit the
//! component tables as one trace tree, build the components against a shared
//! `TraceLocationAllocator`, and run stwo's prover/verifier. The components
//! are pure-constraint (no LogUp interaction yet), so the proof has an empty
//! preprocessed tree and no interaction tree; lookup relations binding the
//! components together arrive with the channel/Merkle milestones
//! (docs/recursion.md, M4+).

use num_traits::Zero;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleChannel;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::core::verifier::VerificationError;
use stwo::core::verifier::verify;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::pcs::CommitmentSchemeProver;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::prove;
use stwo_constraint_framework::TraceLocationAllocator;

use air::trace::Poseidon2Table;
use prover::relations::Relations;

use crate::boundary::Boundary;
use crate::circuit::{CircuitClaim, public_circuit_terms};
use crate::recorder::Arena;
use crate::relations::RecursionRelations;

use crate::{
    ChannelReplayTable, CircleDoubleTable, FriFoldLineTable, LinearOpsTable, LogupSumTable,
    MerklePathTable, Qm31InvTable, Qm31MulTable, channel_replay, circle_double, fri_fold,
    linear_ops, logup_sum, merkle_path, prover_columns, qm31_inv, qm31_mul,
};

/// Witness tables of the recursion AIR, one per component.
#[derive(Default)]
pub struct RecursionTraces {
    pub qm31_mul: Qm31MulTable,
    pub qm31_inv: Qm31InvTable,
    pub fri_fold_line: FriFoldLineTable,
    pub circle_double: CircleDoubleTable,
    pub logup_sum: LogupSumTable,
    pub merkle_path: MerklePathTable,
    pub channel_replay: ChannelReplayTable,
    pub linear_ops: LinearOpsTable,
    pub poseidon2: Poseidon2Table,
}

/// Proof of the recursion AIR plus the public claim (per-component sizes
/// and the LogUp claimed sum).
#[derive(Clone)]
pub struct RecursionProof<H: MerkleHasherLifted> {
    /// Log sizes of (qm31_mul, qm31_inv, fri_fold_line, circle_double,
    /// logup_sum, merkle_path, channel_replay, linear_ops, poseidon2).
    pub log_sizes: [u32; 9],
    /// Claimed sum of the logup_sum component: Σ enabler / term.
    pub claimed_sum: SecureField,
    /// Claimed sums of the merkle_path and poseidon2 components; together
    /// with the public root terms their total must vanish (every hash claim
    /// discharged by a permutation row, every path anchored at a root).
    pub merkle_claimed_sum: SecureField,
    pub channel_claimed_sum: SecureField,
    pub poseidon2_claimed_sum: SecureField,
    /// Claimed sums of the circuit-lowering components (qm31_mul, qm31_inv,
    /// linear_ops); they cancel against the public circuit terms.
    pub circuit_claimed_sums: [SecureField; 3],
    /// Merkle roots the decommitment paths anchor to.
    pub roots: Vec<RootClaim>,
    /// Leaf digests the decommitment paths terminate at (recomputed by the
    /// verifier from the public queried values).
    pub leaves: Vec<LeafClaim>,
    /// Replayed Fiat-Shamir transcripts (public absorbed data).
    pub channels: Vec<ChannelClaim>,
    /// Lowered composition circuits (public inputs and outputs).
    pub circuits: Vec<CircuitClaim>,
    /// Execution boundary the attested subtree spans: chained from the
    /// segment public data at the base and folded upward node by node.
    /// `None` for proofs not tied to an execution (component tests,
    /// standalone circuits).
    pub boundary: Option<Boundary>,
    pub stark_proof: StarkProof<H>,
}

/// Mix the boundary claim into the Fiat-Shamir channel. Presence flags keep
/// the encoding injective: absent boundary and absent memory/program roots
/// each contribute a distinguishable word.
pub(crate) fn mix_boundary<C: Channel>(channel: &mut C, boundary: &Option<Boundary>) {
    let Some(boundary) = boundary else {
        channel.mix_u32s(&[0]);
        return;
    };
    let mut words = vec![1, boundary.entry_pc, boundary.exit_pc];
    words.extend_from_slice(&boundary.entry_regs);
    words.extend_from_slice(&boundary.exit_regs);
    for root in [
        boundary.entry_rw_root,
        boundary.exit_rw_root,
        boundary.program_root,
    ] {
        match root {
            Some(value) => words.extend_from_slice(&[1, value]),
            None => words.push(0),
        }
    }
    channel.mix_u32s(&words);
}

pub(crate) fn mix_circuits<C: Channel>(channel: &mut C, circuits: &[CircuitClaim]) {
    channel.mix_u32s(&[circuits.len() as u32]);
    for claim in circuits {
        channel.mix_u32s(&[
            claim.circuit_id,
            claim.inputs.len() as u32,
            claim.inner_log_size,
            claim.output.0,
        ]);
        channel.mix_felts(&[claim.inner_claimed_sum, claim.output.1]);
        for (node_id, value) in &claim.inputs {
            channel.mix_u32s(&[*node_id]);
            channel.mix_felts(&[*value]);
        }
    }
}

/// A public channel transcript: the words absorbed by sponge `channel_id`,
/// in rate-sized chunks.
#[derive(Clone, Debug)]
pub struct ChannelClaim {
    pub channel_id: u32,
    pub chunks: Vec<[u32; channel_replay::RATE]>,
}

pub(crate) fn mix_channels<C: Channel>(channel: &mut C, channels: &[ChannelClaim]) {
    channel.mix_u32s(&[channels.len() as u32]);
    for claim in channels {
        channel.mix_u32s(&[claim.channel_id, claim.chunks.len() as u32]);
        for chunk in &claim.chunks {
            channel.mix_u32s(chunk);
        }
    }
}

/// The LogUp contribution of the public channel transcripts: the initial
/// state and every data chunk are emitted, and the final digest (recomputed
/// host-side) is consumed.
fn public_channel_terms(
    channels: &[ChannelClaim],
    recursion_relations: &RecursionRelations,
) -> SecureField {
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo_constraint_framework::Relation;

    let mut total = SecureField::zero();
    for claim in channels {
        // Initial state claim: (channel_id, 0, zero state).
        let mut init = [M31::from(0u32); 18];
        init[0] = M31::from(claim.channel_id);
        let denom: SecureField = recursion_relations.sponge_step.combine(&init);
        total += denom.inverse();

        // Data chunks.
        for (step, chunk) in claim.chunks.iter().enumerate() {
            let mut tuple = [M31::from(0u32); 10];
            tuple[0] = M31::from(claim.channel_id);
            tuple[1] = M31::from(step as u32);
            for (slot, &word) in tuple[2..].iter_mut().zip(chunk.iter()) {
                *slot = M31::from(word);
            }
            let denom: SecureField = recursion_relations.sponge_data.combine(&tuple);
            total += denom.inverse();
        }

        // Final digest claim, recomputed by replaying the transcript.
        let digest = channel_replay::replay_digest(&claim.chunks);
        let mut last = [M31::from(0u32); 18];
        last[0] = M31::from(claim.channel_id);
        last[1] = M31::from(claim.chunks.len() as u32);
        for (slot, &word) in last[2..].iter_mut().zip(digest.iter()) {
            *slot = M31::from(word);
        }
        let denom: SecureField = recursion_relations.sponge_step.combine(&last);
        total -= denom.inverse();
    }
    total
}

/// A public root anchor: `n_paths` decommitment paths of tree `tree_id`
/// terminate at `root`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RootClaim {
    pub tree_id: u32,
    pub root: [u32; 8],
    pub n_paths: u32,
}

pub(crate) fn mix_roots<C: Channel>(channel: &mut C, roots: &[RootClaim]) {
    channel.mix_u32s(&[roots.len() as u32]);
    for root in roots {
        channel.mix_u32s(&[root.tree_id, root.n_paths]);
        channel.mix_u32s(&root.root);
    }
}

/// A public leaf anchor: one decommitment path of tree `tree_id` terminates
/// at node `(depth, index)` with digest `digest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafClaim {
    pub tree_id: u32,
    pub depth: u32,
    pub index: u32,
    pub digest: [u32; 8],
}

pub(crate) fn mix_leaves<C: Channel>(channel: &mut C, leaves: &[LeafClaim]) {
    channel.mix_u32s(&[leaves.len() as u32]);
    for leaf in leaves {
        channel.mix_u32s(&[leaf.tree_id, leaf.depth, leaf.index]);
        channel.mix_u32s(&leaf.digest);
    }
}

/// The LogUp contribution of the public leaf anchors: each path's bottom row
/// emits its leaf-level node claim, so the public side consumes it.
fn public_leaf_terms(
    leaves: &[LeafClaim],
    recursion_relations: &RecursionRelations,
) -> SecureField {
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo_constraint_framework::Relation;

    let mut total = SecureField::zero();
    for leaf in leaves {
        let mut tuple = [M31::from(0u32); 11];
        tuple[0] = M31::from(leaf.tree_id);
        tuple[1] = M31::from(leaf.depth);
        tuple[2] = M31::from(leaf.index);
        for (slot, &word) in tuple[3..].iter_mut().zip(leaf.digest.iter()) {
            *slot = M31::from(word);
        }
        let denom: SecureField = recursion_relations.merkle_node.combine(&tuple);
        total -= denom.inverse();
    }
    total
}

/// The LogUp contribution of the public root anchors: each path's top row
/// consumes the root claim, so the public side emits it `n_paths` times.
fn public_root_terms(roots: &[RootClaim], recursion_relations: &RecursionRelations) -> SecureField {
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo_constraint_framework::Relation;

    let mut total = SecureField::zero();
    for root in roots {
        let mut tuple = [M31::from(0u32); 11];
        tuple[0] = M31::from(root.tree_id);
        // depth = 0, index = 0
        for (slot, &word) in tuple[3..].iter_mut().zip(root.root.iter()) {
            *slot = M31::from(word);
        }
        let denom: SecureField = recursion_relations.merkle_node.combine(&tuple);
        total += denom.inverse() * SecureField::from(M31::from(root.n_paths));
    }
    total
}

pub(crate) fn mix_claim<C: Channel>(channel: &mut C, log_sizes: &[u32; 9], sums: [SecureField; 7]) {
    channel.mix_u32s(log_sizes);
    channel.mix_felts(&sums);
}

/// Trace-tree column log sizes in commit order.
pub(crate) fn column_log_sizes(log_sizes: &[u32; 9]) -> Vec<u32> {
    let widths = [
        prover_columns::Qm31MulColumns::<()>::SIZE,
        prover_columns::Qm31InvColumns::<()>::SIZE,
        prover_columns::FriFoldLineColumns::<()>::SIZE,
        prover_columns::CircleDoubleColumns::<()>::SIZE,
        prover_columns::LogupSumColumns::<()>::SIZE,
        prover_columns::MerklePathColumns::<()>::SIZE,
        prover_columns::ChannelReplayColumns::<()>::SIZE,
        prover_columns::LinearOpsColumns::<()>::SIZE,
        air::trace::prover_columns::Poseidon2Columns::<()>::SIZE,
    ];
    log_sizes
        .iter()
        .zip(widths)
        .flat_map(|(&log_size, width)| std::iter::repeat_n(log_size, width))
        .collect()
}

/// Build the four components in commit order against a shared allocator.
#[allow(clippy::type_complexity)]
pub(crate) fn components(
    location_allocator: &mut TraceLocationAllocator,
    log_sizes: &[u32; 9],
    sums: [SecureField; 7],
    relations: &Relations,
    recursion_relations: &RecursionRelations,
) -> (
    qm31_mul::Component,
    qm31_inv::Component,
    fri_fold::Component,
    circle_double::Component,
    logup_sum::Component,
    merkle_path::Component,
    channel_replay::Component,
    linear_ops::Component,
    air::poseidon2::component::air::Component,
) {
    (
        qm31_mul::Component::new(
            location_allocator,
            qm31_mul::Eval {
                log_size: log_sizes[0],
                recursion_relations: recursion_relations.clone(),
            },
            sums[4],
        ),
        qm31_inv::Component::new(
            location_allocator,
            qm31_inv::Eval {
                log_size: log_sizes[1],
                recursion_relations: recursion_relations.clone(),
            },
            sums[5],
        ),
        fri_fold::Component::new(
            location_allocator,
            fri_fold::Eval {
                log_size: log_sizes[2],
            },
            SecureField::zero(),
        ),
        circle_double::Component::new(
            location_allocator,
            circle_double::Eval {
                log_size: log_sizes[3],
            },
            SecureField::zero(),
        ),
        logup_sum::Component::new(
            location_allocator,
            logup_sum::Eval {
                log_size: log_sizes[4],
            },
            sums[0],
        ),
        merkle_path::Component::new(
            location_allocator,
            merkle_path::Eval {
                log_size: log_sizes[5],
                relations: relations.clone(),
                recursion_relations: recursion_relations.clone(),
            },
            sums[1],
        ),
        channel_replay::Component::new(
            location_allocator,
            channel_replay::Eval {
                log_size: log_sizes[6],
                relations: relations.clone(),
                recursion_relations: recursion_relations.clone(),
            },
            sums[2],
        ),
        linear_ops::Component::new(
            location_allocator,
            linear_ops::Eval {
                log_size: log_sizes[7],
                recursion_relations: recursion_relations.clone(),
            },
            sums[6],
        ),
        air::poseidon2::component::air::Component::new(
            location_allocator,
            air::poseidon2::component::air::Eval {
                log_size: log_sizes[8],
                relations: relations.clone(),
            },
            sums[3],
        ),
    )
}

/// Prove the recursion AIR over the given witness tables (Blake2s channel).
pub fn prove_recursion(
    traces: RecursionTraces,
    roots: Vec<RootClaim>,
    leaves: Vec<LeafClaim>,
    channels: Vec<ChannelClaim>,
    circuits: Vec<CircuitClaim>,
    config: PcsConfig,
) -> RecursionProof<<Blake2sMerkleChannel as MerkleChannel>::H> {
    prove_recursion_with_channel::<Blake2sMerkleChannel>(
        traces, roots, leaves, channels, circuits, None, config,
    )
}

/// Verify a recursion AIR proof (Blake2s channel).
pub fn verify_recursion(
    proof: RecursionProof<<Blake2sMerkleChannel as MerkleChannel>::H>,
    circuit_arenas: &[(std::rc::Rc<core::cell::RefCell<Arena>>, usize)],
    config: PcsConfig,
) -> Result<(), VerificationError> {
    verify_recursion_with_channel::<Blake2sMerkleChannel>(proof, circuit_arenas, config)
}

/// Prove the recursion AIR over the given witness tables with any Merkle
/// channel — in particular the Poseidon2-M31 channel whose hash the
/// recursion AIR itself proves.
pub fn prove_recursion_with_channel<MC: MerkleChannel>(
    traces: RecursionTraces,
    roots: Vec<RootClaim>,
    leaves: Vec<LeafClaim>,
    channels: Vec<ChannelClaim>,
    circuits: Vec<CircuitClaim>,
    boundary: Option<Boundary>,
    config: PcsConfig,
) -> RecursionProof<MC::H>
where
    SimdBackend: BackendForChannel<MC>,
{
    let qm31_mul_trace = traces.qm31_mul.into_witness();
    let qm31_inv_trace = traces.qm31_inv.into_witness();
    let fri_fold_trace = traces.fri_fold_line.into_witness();
    let circle_double_trace = traces.circle_double.into_witness();
    let logup_sum_trace = traces.logup_sum.into_witness();
    let merkle_path_trace = traces.merkle_path.into_witness();
    let channel_replay_trace = traces.channel_replay.into_witness();
    let linear_ops_trace = traces.linear_ops.into_witness();
    let poseidon2_trace = traces.poseidon2.into_witness();

    let log_size_of = |trace: &[stwo::prover::poly::circle::CircleEvaluation<
        SimdBackend,
        stwo::core::fields::m31::BaseField,
        stwo::prover::poly::BitReversedOrder,
    >]| {
        trace
            .first()
            .map(|t| t.domain.log_size())
            .expect("component trace is never empty after padding")
    };
    let log_sizes = [
        log_size_of(&qm31_mul_trace),
        log_size_of(&qm31_inv_trace),
        log_size_of(&fri_fold_trace),
        log_size_of(&circle_double_trace),
        log_size_of(&logup_sum_trace),
        log_size_of(&merkle_path_trace),
        log_size_of(&channel_replay_trace),
        log_size_of(&linear_ops_trace),
        log_size_of(&poseidon2_trace),
    ];
    let max_log_size = *log_sizes.iter().max().expect("non-empty");

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let channel = &mut MC::C::default();
    let mut commitment_scheme = CommitmentSchemeProver::<_, MC>::new(config, &twiddles);

    // Tree 0: empty preprocessed trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![]);
    tree_builder.commit(channel);

    channel.mix_u32s(&log_sizes);
    mix_roots(channel, &roots);
    mix_leaves(channel, &leaves);
    mix_channels(channel, &channels);
    mix_circuits(channel, &circuits);
    mix_boundary(channel, &boundary);

    // Tree 1: all component tables, in the fixed commit order.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(
        qm31_mul_trace
            .iter()
            .cloned()
            .chain(qm31_inv_trace.iter().cloned())
            .chain(fri_fold_trace)
            .chain(circle_double_trace)
            .chain(logup_sum_trace.iter().cloned())
            .chain(merkle_path_trace.iter().cloned())
            .chain(channel_replay_trace.iter().cloned())
            .chain(linear_ops_trace.iter().cloned())
            .chain(poseidon2_trace.iter().cloned())
            .collect::<Vec<_>>(),
    );
    tree_builder.commit(channel);

    // Lookup elements are drawn after the main commitment (Fiat-Shamir).
    let relations = Relations::draw(channel);
    let recursion_relations = RecursionRelations::draw(channel);

    // Interaction traces, in component order.
    let (logup_interaction, claimed_sum) = logup_sum::gen_interaction_trace(&logup_sum_trace);
    let (merkle_interaction, merkle_claimed_sum) =
        merkle_path::gen_interaction_trace(&merkle_path_trace, &relations, &recursion_relations);
    let (channel_interaction, channel_claimed_sum) = channel_replay::gen_interaction_trace(
        &channel_replay_trace,
        &relations,
        &recursion_relations,
    );
    let (mul_interaction, mul_claimed_sum) =
        qm31_mul::gen_interaction_trace(&qm31_mul_trace, &recursion_relations);
    let (inv_interaction, inv_claimed_sum) =
        qm31_inv::gen_interaction_trace(&qm31_inv_trace, &recursion_relations);
    let (linear_interaction, linear_claimed_sum) =
        linear_ops::gen_interaction_trace(&linear_ops_trace, &recursion_relations);
    let (poseidon2_interaction, poseidon2_claimed_sum) =
        air::poseidon2::component::witness::gen_interaction_trace(&poseidon2_trace, &relations);

    let sums = [
        claimed_sum,
        merkle_claimed_sum,
        channel_claimed_sum,
        poseidon2_claimed_sum,
        mul_claimed_sum,
        inv_claimed_sum,
        linear_claimed_sum,
    ];
    mix_claim(channel, &log_sizes, sums);

    // Tree 2: interaction traces (LogUp cumulative sums), in component order.
    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(
        mul_interaction
            .into_iter()
            .chain(inv_interaction)
            .chain(logup_interaction)
            .chain(merkle_interaction)
            .chain(channel_interaction)
            .chain(linear_interaction)
            .chain(poseidon2_interaction)
            .collect::<Vec<_>>(),
    );
    tree_builder.commit(channel);

    let mut location_allocator = TraceLocationAllocator::default();
    let (mul, inv, fold, double, sum, merkle, replay, linear, poseidon2) = components(
        &mut location_allocator,
        &log_sizes,
        sums,
        &relations,
        &recursion_relations,
    );

    let stark_proof = prove(
        &[
            &mul, &inv, &fold, &double, &sum, &merkle, &replay, &linear, &poseidon2,
        ],
        channel,
        commitment_scheme,
    )
    .expect("recursion proof generation failed");

    RecursionProof {
        log_sizes,
        claimed_sum,
        merkle_claimed_sum,
        channel_claimed_sum,
        poseidon2_claimed_sum,
        circuit_claimed_sums: [mul_claimed_sum, inv_claimed_sum, linear_claimed_sum],
        roots,
        leaves,
        channels,
        circuits,
        boundary,
        stark_proof,
    }
}

/// Verify a recursion AIR proof with any Merkle channel.
///
/// `circuit_arenas` are the canonical composition circuits, re-recorded by
/// the caller from the claims' public inputs with
/// `circuit::record_from_claim` over the inner components — the trusted
/// structure the lowered rows must match.
pub fn verify_recursion_with_channel<MC: MerkleChannel>(
    proof: RecursionProof<MC::H>,
    circuit_arenas: &[(std::rc::Rc<core::cell::RefCell<Arena>>, usize)],
    config: PcsConfig,
) -> Result<(), VerificationError> {
    assert_eq!(
        proof.circuits.len(),
        circuit_arenas.len(),
        "one re-recorded arena per circuit claim"
    );
    for (claim, (arena, output)) in proof.circuits.iter().zip(circuit_arenas) {
        // The claimed output must be what the canonical circuit computes
        // over the claimed inputs.
        if arena.borrow().nodes[*output].value != claim.output.1 {
            return Err(VerificationError::InvalidStructure(
                "claimed circuit output does not match the canonical circuit".to_string(),
            ));
        }
    }
    let channel = &mut MC::C::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);

    let commitments = &proof.stark_proof.commitments;
    commitment_scheme.commit(commitments[0], &[], channel);
    channel.mix_u32s(&proof.log_sizes);
    mix_roots(channel, &proof.roots);
    mix_leaves(channel, &proof.leaves);
    mix_channels(channel, &proof.channels);
    mix_circuits(channel, &proof.circuits);
    mix_boundary(channel, &proof.boundary);
    commitment_scheme.commit(commitments[1], &column_log_sizes(&proof.log_sizes), channel);

    let relations = Relations::draw(channel);
    let recursion_relations = RecursionRelations::draw(channel);

    // Every hash claim must be discharged by a permutation row, and every
    // path must anchor at a public root.
    let mut total = proof.merkle_claimed_sum
        + proof.channel_claimed_sum
        + proof.poseidon2_claimed_sum
        + proof.circuit_claimed_sums[0]
        + proof.circuit_claimed_sums[1]
        + proof.circuit_claimed_sums[2]
        + public_root_terms(&proof.roots, &recursion_relations)
        + public_leaf_terms(&proof.leaves, &recursion_relations)
        + public_channel_terms(&proof.channels, &recursion_relations);
    for (claim, (arena, output)) in proof.circuits.iter().zip(circuit_arenas) {
        total += public_circuit_terms(claim, &arena.borrow(), *output, &recursion_relations);
    }
    if !total.is_zero() {
        return Err(VerificationError::InvalidStructure(
            "merkle/channel/poseidon2/public logup sums do not cancel".to_string(),
        ));
    }
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
    // Interaction tree: one secure column (4 base) for logup_sum, two for
    // merkle_path (hash binding + node chaining), two for poseidon2.
    let interaction_log_sizes: Vec<u32> = std::iter::repeat_n(proof.log_sizes[0], 8)
        .chain(std::iter::repeat_n(proof.log_sizes[1], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[4], 4))
        .chain(std::iter::repeat_n(proof.log_sizes[5], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[6], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[7], 8))
        .chain(std::iter::repeat_n(proof.log_sizes[8], 8))
        .collect();
    commitment_scheme.commit(commitments[2], &interaction_log_sizes, channel);

    let mut location_allocator = TraceLocationAllocator::default();
    let (mul, inv, fold, double, sum, merkle, replay, linear, poseidon2) = components(
        &mut location_allocator,
        &proof.log_sizes,
        sums,
        &relations,
        &recursion_relations,
    );

    verify(
        &[
            &mul, &inv, &fold, &double, &sum, &merkle, &replay, &linear, &poseidon2,
        ],
        channel,
        &mut commitment_scheme,
        proof.stark_proof,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::circle::SECURE_FIELD_CIRCLE_GEN;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::fields::qm31::QM31;

    fn random_qm31(rng: &mut SmallRng) -> QM31 {
        QM31::from_u32_unchecked(
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
            rng.gen_range(0..(1 << 30)),
        )
    }

    fn random_traces(
        seed: u64,
        rows: usize,
    ) -> (
        RecursionTraces,
        Vec<QM31>,
        Vec<RootClaim>,
        Vec<ChannelClaim>,
    ) {
        let mut rng = SmallRng::seed_from_u64(seed);
        let mut traces = RecursionTraces::default();
        let mut terms = Vec::new();
        for _ in 0..rows {
            let a = random_qm31(&mut rng);
            let b = random_qm31(&mut rng);
            crate::qm31_mul::push_mul(&mut traces.qm31_mul, a, b);
            crate::qm31_inv::push_inv(&mut traces.qm31_inv, a);
            crate::fri_fold::push_fold_line(
                &mut traces.fri_fold_line,
                a,
                b,
                BaseField::from_u32_unchecked(rng.gen_range(1..(1 << 30))),
                random_qm31(&mut rng),
            );
            crate::circle_double::push_double(
                &mut traces.circle_double,
                SECURE_FIELD_CIRCLE_GEN.mul(rng.r#gen::<u128>()),
            );
            crate::logup_sum::push_term(&mut traces.logup_sum, b);
            terms.push(b);
        }

        // Two-level decommitment paths: leaf -> mid -> root, one per tree.
        let mut roots = Vec::new();
        for tree_id in 0..4u32 {
            let child: [u32; 8] = std::array::from_fn(|_| rng.gen_range(0..(1 << 30)));
            let steps = [
                crate::merkle_path::PathStep {
                    direction: rng.gen_range(0..2),
                    sibling: std::array::from_fn(|_| rng.gen_range(0..(1 << 30))),
                },
                crate::merkle_path::PathStep {
                    direction: rng.gen_range(0..2),
                    sibling: std::array::from_fn(|_| rng.gen_range(0..(1 << 30))),
                },
            ];
            // Bottom-up: hash the leaf-side step (depth 1), then the root
            // step (depth 0); indices follow the directions.
            let mid = crate::merkle_path::push_path_step(
                &mut traces.merkle_path,
                &mut traces.poseidon2,
                tree_id,
                1,
                steps[0].direction,
                child,
                steps[1],
                true,
            );
            let root = crate::merkle_path::push_path_step(
                &mut traces.merkle_path,
                &mut traces.poseidon2,
                tree_id,
                0,
                0,
                mid,
                steps[0],
                false,
            );
            roots.push(RootClaim {
                tree_id,
                root,
                n_paths: 1,
            });
        }

        // One replayed Fiat-Shamir transcript: three absorbed chunks.
        let mut channels = Vec::new();
        let chunks: Vec<[u32; 8]> = (0..3)
            .map(|_| std::array::from_fn(|_| rng.gen_range(0..(1 << 30))))
            .collect();
        let mut state = [0u32; 16];
        for (step, chunk) in chunks.iter().enumerate() {
            state = crate::channel_replay::push_sponge_step(
                &mut traces.channel_replay,
                &mut traces.poseidon2,
                0,
                step as u32,
                state,
                *chunk,
            );
        }
        assert_eq!(state, crate::channel_replay::replay_digest(&chunks));
        channels.push(ChannelClaim {
            channel_id: 0,
            chunks,
        });
        (traces, terms, roots, channels)
    }

    #[test]
    fn test_recursion_air_prove_verify_roundtrip() {
        let (traces, _, roots, channels) = random_traces(0, 50);
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        verify_recursion(proof, &[], PcsConfig::default()).expect("verification failed");
    }

    #[test]
    fn test_recursion_air_rejects_tampered_claim() {
        let (traces, _, roots, channels) = random_traces(1, 50);
        let mut proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        // Lying about a component size breaks the channel binding.
        proof.log_sizes[0] += 1;
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_claimed_sum_is_sum_of_inverses() {
        let (traces, terms, roots, channels) = random_traces(2, 50);
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert_eq!(proof.claimed_sum, crate::logup_sum::expected_sum(&terms));
    }

    #[test]
    fn test_recursion_air_prove_verify_roundtrip_poseidon2_channel() {
        use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
        let (traces, _, roots, channels) = random_traces(4, 50);
        let proof = prove_recursion_with_channel::<Poseidon2M31MerkleChannel>(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            None,
            PcsConfig::default(),
        );
        verify_recursion_with_channel::<Poseidon2M31MerkleChannel>(
            proof,
            &[],
            PcsConfig::default(),
        )
        .expect("poseidon2-channel verification failed");
    }

    #[test]
    fn test_recursion_air_merkle_and_poseidon2_sums_cancel() {
        let (traces, _, roots, channels) = random_traces(5, 20);
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        // Hash claims cancel between merkle_path and poseidon2; the node
        // claims cancel against the public root terms checked in verify.
        verify_recursion(proof, &[], PcsConfig::default()).expect("verification failed");
    }

    #[test]
    fn test_recursion_air_rejects_undischarged_hash_claim() {
        let (mut traces, _, roots, channels) = random_traces(6, 20);
        // Corrupt one parent limb: the merkle_path row now consumes a tuple
        // no permutation row emits, and its node claim no longer anchors.
        traces.merkle_path.parent_0[0] += 1;
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_rejects_permuted_merkle_hash_outputs() {
        use air::poseidon2::{T, poseidon2_traced_state};

        let mut traces = RecursionTraces::default();
        let left_a = [11, 12, 13, 14, 15, 16, 17, 18];
        let right_a = [21, 22, 23, 24, 25, 26, 27, 28];
        let left_b = [31, 32, 33, 34, 35, 36, 37, 38];
        let right_b = [41, 42, 43, 44, 45, 46, 47, 48];

        let mut input_a = [0; T];
        input_a[..8].copy_from_slice(&left_a);
        input_a[8..].copy_from_slice(&right_a);
        let output_a = poseidon2_traced_state(&mut traces.poseidon2, input_a, false, true);

        let mut input_b = [0; T];
        input_b[..8].copy_from_slice(&left_b);
        input_b[8..].copy_from_slice(&right_b);
        let output_b = poseidon2_traced_state(&mut traces.poseidon2, input_b, false, true);

        // Each path uses a valid permutation input and a valid permutation
        // output, but the outputs belong to the other path. Atomic hash-call
        // binding must reject this cross-call splice.
        traces.merkle_path.push(
            0,
            0,
            0,
            0,
            0,
            left_a[0],
            left_a[1],
            left_a[2],
            left_a[3],
            left_a[4],
            left_a[5],
            left_a[6],
            left_a[7],
            right_a[0],
            right_a[1],
            right_a[2],
            right_a[3],
            right_a[4],
            right_a[5],
            right_a[6],
            right_a[7],
            output_b[0],
            output_b[1],
            output_b[2],
            output_b[3],
            output_b[4],
            output_b[5],
            output_b[6],
            output_b[7],
            output_b[8],
            output_b[9],
            output_b[10],
            output_b[11],
            output_b[12],
            output_b[13],
            output_b[14],
            output_b[15],
            left_a[0],
            left_a[1],
            left_a[2],
            left_a[3],
            left_a[4],
            left_a[5],
            left_a[6],
            left_a[7],
        );
        traces.merkle_path.push(
            1,
            0,
            0,
            0,
            0,
            left_b[0],
            left_b[1],
            left_b[2],
            left_b[3],
            left_b[4],
            left_b[5],
            left_b[6],
            left_b[7],
            right_b[0],
            right_b[1],
            right_b[2],
            right_b[3],
            right_b[4],
            right_b[5],
            right_b[6],
            right_b[7],
            output_a[0],
            output_a[1],
            output_a[2],
            output_a[3],
            output_a[4],
            output_a[5],
            output_a[6],
            output_a[7],
            output_a[8],
            output_a[9],
            output_a[10],
            output_a[11],
            output_a[12],
            output_a[13],
            output_a[14],
            output_a[15],
            left_b[0],
            left_b[1],
            left_b[2],
            left_b[3],
            left_b[4],
            left_b[5],
            left_b[6],
            left_b[7],
        );

        let roots = vec![
            RootClaim {
                tree_id: 0,
                root: output_b[..8].try_into().expect("digest width"),
                n_paths: 1,
            },
            RootClaim {
                tree_id: 1,
                root: output_a[..8].try_into().expect("digest width"),
                n_paths: 1,
            },
        ];
        let leaves = vec![
            LeafClaim {
                tree_id: 0,
                depth: 1,
                index: 0,
                digest: left_a,
            },
            LeafClaim {
                tree_id: 1,
                depth: 1,
                index: 0,
                digest: left_b,
            },
        ];
        let proof = prove_recursion(traces, roots, leaves, vec![], vec![], PcsConfig::default());

        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_rejects_wrong_root_claim() {
        let (traces, _, mut roots, channels) = random_traces(7, 20);
        roots[0].root[0] += 1;
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_rejects_broken_path_chaining() {
        let (mut traces, _, roots, channels) = random_traces(8, 20);
        // Corrupt an index: the child claim emitted above no longer matches
        // the claim this row consumes.
        traces.merkle_path.index[0] += 1;
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_rejects_tampered_transcript_chunk() {
        let (traces, _, roots, mut channels) = random_traces(9, 20);
        // The public transcript no longer matches the absorbed witness data.
        channels[0].chunks[1][0] += 1;
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_rejects_broken_sponge_chaining() {
        let (mut traces, _, roots, channels) = random_traces(10, 20);
        // Corrupt a carried capacity word: the chained state claim breaks.
        traces.channel_replay.prev_15[1] += 1;
        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_recursion_air_proves_lui_composition_circuit() {
        use stwo_constraint_framework::{FrameworkEval, InfoEvaluator};

        let inner = prover::components::lui::air::Eval {
            log_size: 6,
            relations: prover::relations::Relations::dummy(),
        };
        let info = inner.evaluate(InfoEvaluator::empty());
        let mut rng = SmallRng::seed_from_u64(11);
        let mask_values: Vec<Vec<Vec<SecureField>>> = info
            .mask_offsets
            .iter()
            .map(|interaction| {
                interaction
                    .iter()
                    .map(|offsets| (0..offsets.len()).map(|_| random_qm31(&mut rng)).collect())
                    .collect()
            })
            .collect();
        let recorder = crate::recorder::Recorder::new(
            mask_values,
            random_qm31(&mut rng),
            random_qm31(&mut rng),
            6,
            random_qm31(&mut rng),
        );
        let recorder = inner.evaluate(recorder);
        let output = match &recorder.accumulation {
            crate::recorder::Rec::Node { id, .. } => *id,
            _ => panic!("constant accumulation"),
        };

        let (mut traces, _, roots, channels) = random_traces(12, 10);
        let claim = crate::circuit::lower_arena(
            &mut traces,
            7,
            &recorder.arena.borrow(),
            output,
            6,
            recorder.logup.cumsum_shift * SecureField::from(BaseField::from_u32_unchecked(1 << 6)),
        );

        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![claim.clone()],
            PcsConfig::default(),
        );

        // Verifier re-records the canonical circuit from the public inputs.
        let arena = crate::circuit::record_from_claim(&inner, &claim);
        verify_recursion(proof, &[arena], PcsConfig::default())
            .expect("composition-circuit verification failed");
    }

    #[test]
    fn test_recursion_air_rejects_wrong_circuit_output() {
        use stwo_constraint_framework::{FrameworkEval, InfoEvaluator};

        let inner = prover::components::lui::air::Eval {
            log_size: 6,
            relations: prover::relations::Relations::dummy(),
        };
        let info = inner.evaluate(InfoEvaluator::empty());
        let mut rng = SmallRng::seed_from_u64(13);
        let mask_values: Vec<Vec<Vec<SecureField>>> = info
            .mask_offsets
            .iter()
            .map(|interaction| {
                interaction
                    .iter()
                    .map(|offsets| (0..offsets.len()).map(|_| random_qm31(&mut rng)).collect())
                    .collect()
            })
            .collect();
        let recorder = crate::recorder::Recorder::new(
            mask_values,
            random_qm31(&mut rng),
            random_qm31(&mut rng),
            6,
            random_qm31(&mut rng),
        );
        let recorder = inner.evaluate(recorder);
        let output = match &recorder.accumulation {
            crate::recorder::Rec::Node { id, .. } => *id,
            _ => panic!("constant accumulation"),
        };

        let (mut traces, _, roots, channels) = random_traces(14, 10);
        let mut claim = crate::circuit::lower_arena(
            &mut traces,
            7,
            &recorder.arena.borrow(),
            output,
            6,
            recorder.logup.cumsum_shift * SecureField::from(BaseField::from_u32_unchecked(1 << 6)),
        );
        // Lie about the composition output.
        claim.output.1 += SecureField::from(BaseField::from_u32_unchecked(1));

        let proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![claim.clone()],
            PcsConfig::default(),
        );
        let arena = crate::circuit::record_from_claim(&inner, &claim);
        assert!(verify_recursion(proof, &[arena], PcsConfig::default()).is_err());
    }

    #[test]
    fn test_channel_session_replay_matches_real_channel_and_proves() {
        use prover::poseidon2_channel::{Poseidon2M31Channel, encode_u32s};
        use stwo::core::channel::Channel;

        // The real channel: mix, draw, mix, draw.
        let mut channel = Poseidon2M31Channel::default();
        channel.mix_u32s(&[7, 9]);
        let first = channel.draw_secure_felt();
        channel.mix_u64(42);
        let second = channel.draw_secure_felt();

        // The replayed session over the same operations.
        let mut traces = RecursionTraces::default();
        let ops = [
            crate::channel_replay::ChannelOp::Mix(encode_u32s(&[7, 9]).collect()),
            crate::channel_replay::ChannelOp::Draw,
            crate::channel_replay::ChannelOp::Mix(encode_u32s(&[42u32, 0]).collect()),
            crate::channel_replay::ChannelOp::Draw,
        ];
        let session = crate::channel_replay::replay_session(
            &mut traces.channel_replay,
            &mut traces.poseidon2,
            0,
            &ops,
        );
        session.check_links().expect("session chains");

        let drawn = |block: &[u32; 8]| {
            SecureField::from_m31_array(std::array::from_fn(|i| {
                BaseField::from_u32_unchecked(block[i])
            }))
        };
        assert_eq!(drawn(&session.draws[0]), first);
        assert_eq!(drawn(&session.draws[1]), second);

        // And the session is provable in the recursion AIR.
        let claims = session.claims.clone();
        let proof = prove_recursion(traces, vec![], vec![], claims, vec![], PcsConfig::default());
        verify_recursion(proof, &[], PcsConfig::default()).expect("session recursion proof failed");
    }

    #[test]
    fn test_recursion_air_rejects_tampered_claimed_sum() {
        let (traces, _, roots, channels) = random_traces(3, 50);
        let mut proof = prove_recursion(
            traces,
            roots,
            vec![],
            channels,
            vec![],
            PcsConfig::default(),
        );
        proof.claimed_sum += SecureField::from_u32_unchecked(1, 0, 0, 0);
        assert!(verify_recursion(proof, &[], PcsConfig::default()).is_err());
    }
}
