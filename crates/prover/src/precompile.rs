//! Cross-proof LogUp binding: proving a computation in a separate stwo
//! instance and binding it to its caller through a shared relation.
//!
//! This is the mechanism `docs/precompiles.md` builds on, reduced to its
//! essence and proven end to end. Two independent stwo proofs share one
//! LogUp relation: the *host* proof emits `value(x, y)` tuples it used (it
//! does not prove the relationship), and the *precompile* proof consumes
//! them while proving `y = x * x`. The shared relation is drawn from both
//! proofs' trace commitments (a two-phase handshake), so neither prover can
//! choose its trace after seeing the relation; the binder then checks the
//! two claimed LogUp sums cancel. Cancellation means every pair the host
//! used was discharged by a precompile row — the host never re-proves the
//! squaring, exactly as a real hash precompile would offload Poseidon2.
//!
//! The "square" here stands in for any pure function the precompile attests
//! (`y = poseidon2(x)`); the binding shape is identical.

use num_traits::Zero;
use stwo::core::ColumnVec;
use stwo::core::channel::{Blake2sChannel, Channel};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig};
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::StarkProof;
use stwo::core::proof_of_work::GrindOps;
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::{VerificationError, verify};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::pcs::CommitmentSchemeProver;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::prove;
use stwo_constraint_framework::{TraceLocationAllocator, relation};

use crate::relations::{INTERACTION_POW_BITS, Relations};

// The square exemplar shares one atomic `(x, y)` relation across its proofs.
relation!(ValueRelation, 2);

/// Relation instances embedded by the square binding component.
#[derive(Clone)]
pub struct BindingRelations {
    pub value: ValueRelation,
}

// Distinct AIR owners keep the square constraint out of prover-controlled data.
mod binding_emit_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::precompile::BindingRelations,

        relation value(2);

        fn binding(x, y) {
            emit(enabler) value(x, y);
            return (x, y);
        }
    }
}

mod binding_consume_square_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::precompile::BindingRelations,

        relation value(2);

        fn binding(x, y) {
            constrain y - x * x;
            consume(enabler) value(x, y);
            return (x, y);
        }
    }
}

type B = SimdBackend;
type MC = Blake2sMerkleChannel;
type H = Blake2sMerkleHasher;

/// Which side of the shared relation a proof sits on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Role {
    /// The caller: emits `+value(x, y)` for each pair it used, with no
    /// constraint tying `y` to `x` (the precompile owns that).
    Emit,
    /// The precompile: consumes `-value(x, y)` and proves `y = x * x`.
    ConsumeSquare,
}

/// Generate the interaction trace and claimed LogUp sum for one side.
///
/// The numerator is `±enabler`, so padding rows (enabler 0) contribute
/// `0 / value(0, 0)` and drop out cleanly.
fn gen_interaction_trace(
    trace: &[CircleEvaluation<B, BaseField, BitReversedOrder>],
    value: &ValueRelation,
    role: Role,
) -> (
    ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>>,
    SecureField,
) {
    let relations = BindingRelations {
        value: value.clone(),
    };
    match role {
        Role::Emit => {
            binding_emit_dsl::component::witness::gen_interaction_trace(trace, &relations)
        }
        Role::ConsumeSquare => {
            binding_consume_square_dsl::component::witness::gen_interaction_trace(trace, &relations)
        }
    }
}

/// One side's proof: its trace size, its claimed LogUp sum, and the stwo
/// proof. The trace-tree commitment inside `stark_proof` seeds the shared
/// relation.
pub struct SystemProof {
    pub log_size: u32,
    pub claimed_sum: SecureField,
    pub stark_proof: StarkProof<H>,
}

/// One proof of work over both committed main traces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JointInteractionProof {
    pub pow_nonce: u64,
}

/// A bound pair of proofs: the host that used the pairs and the precompile
/// that validated them.
pub struct PrecompileBindingProof {
    pub joint_interaction: JointInteractionProof,
    pub host: SystemProof,
    pub precompile: SystemProof,
}

/// Starts the ordered transcript shared by both proof instances.
fn joint_interaction_channel(seeds: [SecureField; 2]) -> Blake2sChannel {
    let mut channel = Blake2sChannel::default();
    channel.mix_felts(&seeds);
    channel
}

/// Grinds once over both post-commitment seeds and advances the joint transcript.
fn prove_joint_interaction(seeds: [SecureField; 2]) -> (JointInteractionProof, Blake2sChannel) {
    let mut channel = joint_interaction_channel(seeds);
    let pow_nonce = SimdBackend::grind(&channel, INTERACTION_POW_BITS);
    channel.mix_u64(pow_nonce);
    (JointInteractionProof { pow_nonce }, channel)
}

/// Checks the shared grind before any cross-proof relation challenge is drawn.
fn verify_joint_interaction(
    seeds: [SecureField; 2],
    proof: JointInteractionProof,
) -> Result<Blake2sChannel, VerificationError> {
    let mut channel = joint_interaction_channel(seeds);
    if !channel.verify_pow_nonce(INTERACTION_POW_BITS, proof.pow_nonce) {
        return Err(VerificationError::InvalidStructure(
            "precompile binding: invalid joint interaction proof of work".to_string(),
        ));
    }
    channel.mix_u64(proof.pow_nonce);
    Ok(channel)
}

/// Binds the ordered joint transcript prefix into one constituent proof.
fn bind_joint_interaction(
    channel: &mut Blake2sChannel,
    seeds: [SecureField; 2],
    proof: JointInteractionProof,
) {
    channel.mix_felts(&seeds);
    channel.mix_u64(proof.pow_nonce);
}

/// Commit one side's preprocessed (empty) and trace trees, leaving the
/// channel at the post-commit state from which the shared seed is drawn.
fn commit_system<'a>(
    trace: &[CircleEvaluation<B, BaseField, BitReversedOrder>],
    config: PcsConfig,
    twiddles: &'a TwiddleTree<B>,
) -> (CommitmentSchemeProver<'a, B, MC>, Blake2sChannel, u32) {
    let log_size = trace[0].domain.log_size();
    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme = CommitmentSchemeProver::<B, MC>::new(config, twiddles);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(vec![]);
    tree_builder.commit(&mut channel);

    channel.mix_u32s(&[log_size]);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(trace.to_vec());
    tree_builder.commit(&mut channel);

    (commitment_scheme, channel, log_size)
}

/// Finish one side: interaction trace, claimed sum, component, stwo proof.
/// The channel must already have the shared relation bound in.
fn finish_system(
    mut commitment_scheme: CommitmentSchemeProver<'_, B, MC>,
    channel: &mut Blake2sChannel,
    trace: &[CircleEvaluation<B, BaseField, BitReversedOrder>],
    value: &ValueRelation,
    role: Role,
) -> SystemProof {
    let log_size = trace[0].domain.log_size();
    let (interaction, claimed_sum) = gen_interaction_trace(trace, value, role);
    channel.mix_felts(&[claimed_sum]);

    let mut tree_builder = commitment_scheme.tree_builder();
    tree_builder.extend_evals(interaction);
    tree_builder.commit(channel);

    let relations = BindingRelations {
        value: value.clone(),
    };
    let stark_proof = match role {
        Role::Emit => {
            let mut location_allocator = TraceLocationAllocator::default();
            let component = binding_emit_dsl::component::air::Component::new(
                &mut location_allocator,
                binding_emit_dsl::component::air::Eval {
                    log_size,
                    relations,
                },
                claimed_sum,
            );
            prove(&[&component], channel, commitment_scheme)
        }
        Role::ConsumeSquare => {
            let mut location_allocator = TraceLocationAllocator::default();
            let component = binding_consume_square_dsl::component::air::Component::new(
                &mut location_allocator,
                binding_consume_square_dsl::component::air::Eval {
                    log_size,
                    relations,
                },
                claimed_sum,
            );
            prove(&[&component], channel, commitment_scheme)
        }
    }
    .expect("binding proof generation failed");

    SystemProof {
        log_size,
        claimed_sum,
        stark_proof,
    }
}

/// Prove the host and precompile sides as two independent stwo proofs bound
/// by the shared relation.
///
/// `pairs` are the `(x, y)` the host used; the precompile re-derives and
/// proves `y = x * x` for each. Both fill the same multiset, so the claimed
/// sums cancel.
pub fn prove_binding(pairs: &[(u32, u32)], config: PcsConfig) -> PrecompileBindingProof {
    prove_binding_sides(pairs, pairs, config)
}

/// Prove the two sides from independent pair lists — the faithful shape, in
/// which the host and the precompile build their tables separately. The
/// binding holds only when the two lists are the same multiset.
pub fn prove_binding_sides(
    host_pairs: &[(u32, u32)],
    precompile_pairs: &[(u32, u32)],
    config: PcsConfig,
) -> PrecompileBindingProof {
    let mut host_table = binding_emit_dsl::BindingTable::new();
    let mut precompile_table = binding_consume_square_dsl::BindingTable::new();
    for &(x, y) in host_pairs {
        host_table.push(x, y);
    }
    for &(x, y) in precompile_pairs {
        precompile_table.push(x, y);
    }
    let host_trace = host_table.into_witness();
    let precompile_trace = precompile_table.into_witness();

    let max_log_size = host_trace[0]
        .domain
        .log_size()
        .max(precompile_trace[0].domain.log_size());
    let twiddles = B::precompute_twiddles(
        CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let (host_scheme, mut host_channel, _) = commit_system(&host_trace, config, &twiddles);
    let (precompile_scheme, mut precompile_channel, _) =
        commit_system(&precompile_trace, config, &twiddles);

    // Two-phase draw: the relation depends on both committed traces.
    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let seeds = [seed_host, seed_precompile];
    let (joint_interaction, mut joint_channel) = prove_joint_interaction(seeds);
    let value = ValueRelation::draw(&mut joint_channel);

    bind_joint_interaction(&mut host_channel, seeds, joint_interaction);
    bind_joint_interaction(&mut precompile_channel, seeds, joint_interaction);

    let host = finish_system(
        host_scheme,
        &mut host_channel,
        &host_trace,
        &value,
        Role::Emit,
    );
    let precompile = finish_system(
        precompile_scheme,
        &mut precompile_channel,
        &precompile_trace,
        &value,
        Role::ConsumeSquare,
    );

    PrecompileBindingProof {
        joint_interaction,
        host,
        precompile,
    }
}

/// Replay one side's commitment phase, leaving the verifier channel at the
/// post-commit state. Mirrors [`commit_system`].
fn replay_system_commit(
    proof: &SystemProof,
    config: PcsConfig,
    trace_column_count: usize,
) -> (CommitmentSchemeVerifier<MC>, Blake2sChannel) {
    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);
    let commitments = &proof.stark_proof.commitments;

    commitment_scheme.commit(commitments[0], &[], &mut channel);
    channel.mix_u32s(&[proof.log_size]);
    let trace_log_sizes = vec![proof.log_size; trace_column_count];
    commitment_scheme.commit(commitments[1], &trace_log_sizes, &mut channel);

    (commitment_scheme, channel)
}

/// Finishes one side after the caller binds the joint transcript prefix.
fn verify_system(
    proof: SystemProof,
    mut commitment_scheme: CommitmentSchemeVerifier<MC>,
    channel: &mut Blake2sChannel,
    value: &ValueRelation,
    role: Role,
) -> Result<(), VerificationError> {
    channel.mix_felts(&[proof.claimed_sum]);

    // One secure column (4 base columns) of LogUp fractions.
    let interaction_log_sizes = vec![proof.log_size; 4];
    commitment_scheme.commit(
        proof.stark_proof.commitments[2],
        &interaction_log_sizes,
        channel,
    );

    let relations = BindingRelations {
        value: value.clone(),
    };
    match role {
        Role::Emit => {
            let mut location_allocator = TraceLocationAllocator::default();
            let component = binding_emit_dsl::component::air::Component::new(
                &mut location_allocator,
                binding_emit_dsl::component::air::Eval {
                    log_size: proof.log_size,
                    relations,
                },
                proof.claimed_sum,
            );
            verify(
                &[&component],
                channel,
                &mut commitment_scheme,
                proof.stark_proof,
            )
        }
        Role::ConsumeSquare => {
            let mut location_allocator = TraceLocationAllocator::default();
            let component = binding_consume_square_dsl::component::air::Component::new(
                &mut location_allocator,
                binding_consume_square_dsl::component::air::Eval {
                    log_size: proof.log_size,
                    relations,
                },
                proof.claimed_sum,
            );
            verify(
                &[&component],
                channel,
                &mut commitment_scheme,
                proof.stark_proof,
            )
        }
    }
}

/// Verify a bound pair: both stwo proofs hold, and their claimed LogUp sums
/// cancel under the shared relation.
///
/// Cancellation is the binding: every `value(x, y)` the host emitted was
/// consumed by a precompile row that proved `y = x * x`.
pub fn verify_binding(
    proof: PrecompileBindingProof,
    config: PcsConfig,
) -> Result<(), VerificationError> {
    let PrecompileBindingProof {
        joint_interaction,
        host,
        precompile,
    } = proof;

    let trace_column_count = binding_emit_dsl::prover_columns::BindingColumns::<()>::SIZE;
    let (host_scheme, mut host_channel) = replay_system_commit(&host, config, trace_column_count);
    let (precompile_scheme, mut precompile_channel) =
        replay_system_commit(&precompile, config, trace_column_count);

    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let seeds = [seed_host, seed_precompile];
    let mut joint_channel = verify_joint_interaction(seeds, joint_interaction)?;
    let value = ValueRelation::draw(&mut joint_channel);

    // The cross-proof binding check.
    if !(host.claimed_sum + precompile.claimed_sum).is_zero() {
        return Err(VerificationError::InvalidStructure(
            "precompile binding: host and precompile claimed sums do not cancel".to_string(),
        ));
    }

    bind_joint_interaction(&mut host_channel, seeds, joint_interaction);
    bind_joint_interaction(&mut precompile_channel, seeds, joint_interaction);
    verify_system(host, host_scheme, &mut host_channel, &value, Role::Emit)?;
    verify_system(
        precompile,
        precompile_scheme,
        &mut precompile_channel,
        &value,
        Role::ConsumeSquare,
    )
}

// =============================================================================
// The real precompile: Poseidon2 over the 32-word `poseidon2_io` relation
// =============================================================================

use air::poseidon2::poseidon2_traced_state;
use air::trace::Poseidon2Table;

// Outputs stay unconstrained here because the paired Poseidon proof discharges them.
mod hash_binding_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::relations::Relations,

        relation poseidon2_io(32);

        fn hash_binding(
            in_0, in_1, in_2, in_3, in_4, in_5, in_6, in_7,
            in_8, in_9, in_10, in_11, in_12, in_13, in_14, in_15,
            out_0, out_1, out_2, out_3, out_4, out_5, out_6, out_7,
            out_8, out_9, out_10, out_11, out_12, out_13, out_14, out_15,
        ) {
            consume(enabler) poseidon2_io(
                in_0, in_1, in_2, in_3, in_4, in_5, in_6, in_7,
                in_8, in_9, in_10, in_11, in_12, in_13, in_14, in_15,
                out_0, out_1, out_2, out_3, out_4, out_5, out_6, out_7,
                out_8, out_9, out_10, out_11, out_12, out_13, out_14, out_15,
            );
            return (
                out_0, out_1, out_2, out_3, out_4, out_5, out_6, out_7,
                out_8, out_9, out_10, out_11, out_12, out_13, out_14, out_15,
            );
        }
    }
}

use hash_binding_dsl::HashBindingTable;
use hash_binding_dsl::prover_columns::HashBindingColumns;

pub type HashHostEval = hash_binding_dsl::component::air::Eval;
pub type HashHostComponent = hash_binding_dsl::component::air::Component;

/// Generate the host side's interaction trace: `-enabler / poseidon2_io(t)`
/// per row, so padding rows drop out and every used tuple must be discharged
/// by a precompile permutation row.
fn gen_hash_host_interaction(
    trace: &[CircleEvaluation<B, BaseField, BitReversedOrder>],
    relations: &Relations,
) -> (
    ColumnVec<CircleEvaluation<B, BaseField, BitReversedOrder>>,
    SecureField,
) {
    hash_binding_dsl::component::witness::gen_interaction_trace(trace, relations)
}

/// A bound pair of proofs for the Poseidon2 precompile: the host that used
/// the permutations and the stark-v `poseidon2` component instance that
/// proved them (io rows, so only the atomic 32-word tuples are emitted).
pub struct HashPrecompileBindingProof {
    pub joint_interaction: JointInteractionProof,
    pub host: SystemProof,
    pub precompile: SystemProof,
}

/// Draws the full relation set from the post-grind joint transcript.
/// The `poseidon2_io` member is the shared relation; drawing the whole set
/// keeps the precompile side's component byte-identical to the zkVM's.
fn draw_shared_relations(channel: &mut Blake2sChannel) -> Relations {
    Relations::draw(channel)
}

/// Prove the host and the Poseidon2 precompile as two independent stwo
/// proofs bound by the shared `poseidon2_io` relation.
///
/// `states` are the permutation inputs the host used; the host table carries
/// `(state, permute(state))` with no constraint, and the precompile proves
/// every permutation with the reused stark-v `poseidon2` component.
pub fn prove_hash_binding(states: &[[u32; 16]], config: PcsConfig) -> HashPrecompileBindingProof {
    let outputs: Vec<[u32; 16]> = states
        .iter()
        .map(|state| {
            let mut out = *state;
            air::poseidon2::poseidon2_permutation(&mut out);
            out
        })
        .collect();
    let host_pairs: Vec<([u32; 16], [u32; 16])> =
        states.iter().zip(&outputs).map(|(i, o)| (*i, *o)).collect();
    prove_hash_binding_sides(&host_pairs, states, config)
}

/// Prove the two sides from independent lists — the faithful shape. The
/// binding holds only when the host's `(in, out)` multiset is exactly the
/// set of permutations the precompile proved.
pub fn prove_hash_binding_sides(
    host_pairs: &[([u32; 16], [u32; 16])],
    precompile_states: &[[u32; 16]],
    config: PcsConfig,
) -> HashPrecompileBindingProof {
    let mut host_table = HashBindingTable::new();
    for (input, output) in host_pairs {
        host_table.push(
            input[0], input[1], input[2], input[3], input[4], input[5], input[6], input[7],
            input[8], input[9], input[10], input[11], input[12], input[13], input[14], input[15],
            output[0], output[1], output[2], output[3], output[4], output[5], output[6], output[7],
            output[8], output[9], output[10], output[11], output[12], output[13], output[14],
            output[15],
        );
    }
    let mut precompile_table = Poseidon2Table::default();
    for state in precompile_states {
        poseidon2_traced_state(&mut precompile_table, *state, false, true);
    }

    let host_trace = host_table.into_witness();
    let precompile_trace = precompile_table.into_witness();

    let max_log_size = host_trace[0]
        .domain
        .log_size()
        .max(precompile_trace[0].domain.log_size());
    let twiddles = B::precompute_twiddles(
        CanonicCoset::new(max_log_size + 2 + config.fri_config.log_blowup_factor)
            .circle_domain()
            .half_coset,
    );

    let (host_scheme, mut host_channel, host_log_size) =
        commit_system(&host_trace, config, &twiddles);
    let (precompile_scheme, mut precompile_channel, precompile_log_size) =
        commit_system(&precompile_trace, config, &twiddles);

    // Two-phase draw: the relations depend on both committed traces.
    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let seeds = [seed_host, seed_precompile];
    let (joint_interaction, mut joint_channel) = prove_joint_interaction(seeds);
    let relations = draw_shared_relations(&mut joint_channel);
    bind_joint_interaction(&mut host_channel, seeds, joint_interaction);
    bind_joint_interaction(&mut precompile_channel, seeds, joint_interaction);

    // Host side: interaction, claim, proof.
    let (host_interaction, host_claimed_sum) = gen_hash_host_interaction(&host_trace, &relations);
    host_channel.mix_felts(&[host_claimed_sum]);
    let mut host_scheme = host_scheme;
    let mut tree_builder = host_scheme.tree_builder();
    tree_builder.extend_evals(host_interaction);
    tree_builder.commit(&mut host_channel);
    let mut location_allocator = TraceLocationAllocator::default();
    let host_component = HashHostComponent::new(
        &mut location_allocator,
        HashHostEval {
            log_size: host_log_size,
            relations: relations.clone(),
        },
        host_claimed_sum,
    );
    let host_proof = prove(&[&host_component], &mut host_channel, host_scheme)
        .expect("hash host proof generation failed");

    // Precompile side: the reused stark-v poseidon2 component.
    let (precompile_interaction, precompile_claimed_sum) =
        air::poseidon2::component::witness::gen_interaction_trace(&precompile_trace, &relations);
    precompile_channel.mix_felts(&[precompile_claimed_sum]);
    let mut precompile_scheme = precompile_scheme;
    let mut tree_builder = precompile_scheme.tree_builder();
    tree_builder.extend_evals(precompile_interaction);
    tree_builder.commit(&mut precompile_channel);
    let mut location_allocator = TraceLocationAllocator::default();
    let precompile_component = air::poseidon2::component::air::Component::new(
        &mut location_allocator,
        air::poseidon2::component::air::Eval {
            log_size: precompile_log_size,
            relations: relations.clone(),
        },
        precompile_claimed_sum,
    );
    let precompile_proof = prove(
        &[&precompile_component],
        &mut precompile_channel,
        precompile_scheme,
    )
    .expect("hash precompile proof generation failed");

    HashPrecompileBindingProof {
        joint_interaction,
        host: SystemProof {
            log_size: host_log_size,
            claimed_sum: host_claimed_sum,
            stark_proof: host_proof,
        },
        precompile: SystemProof {
            log_size: precompile_log_size,
            claimed_sum: precompile_claimed_sum,
            stark_proof: precompile_proof,
        },
    }
}

/// Verify a bound Poseidon2 pair: both stwo proofs hold, and their claimed
/// LogUp sums cancel under the shared `poseidon2_io` relation — every tuple
/// the host used was discharged by a proven permutation row.
pub fn verify_hash_binding(
    proof: HashPrecompileBindingProof,
    config: PcsConfig,
) -> Result<(), VerificationError> {
    let HashPrecompileBindingProof {
        joint_interaction,
        host,
        precompile,
    } = proof;

    let (mut host_scheme, mut host_channel) =
        replay_system_commit(&host, config, HashBindingColumns::<()>::SIZE);
    let (mut precompile_scheme, mut precompile_channel) = replay_system_commit(
        &precompile,
        config,
        air::trace::prover_columns::Poseidon2Columns::<()>::SIZE,
    );

    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let seeds = [seed_host, seed_precompile];
    let mut joint_channel = verify_joint_interaction(seeds, joint_interaction)?;
    let relations = draw_shared_relations(&mut joint_channel);

    // The cross-proof binding check.
    if !(host.claimed_sum + precompile.claimed_sum).is_zero() {
        return Err(VerificationError::InvalidStructure(
            "hash precompile binding: claimed sums do not cancel".to_string(),
        ));
    }

    // Host side: one secure LogUp column (4 base columns).
    bind_joint_interaction(&mut host_channel, seeds, joint_interaction);
    host_channel.mix_felts(&[host.claimed_sum]);
    host_scheme.commit(
        host.stark_proof.commitments[2],
        &[host.log_size; 4],
        &mut host_channel,
    );
    let mut location_allocator = TraceLocationAllocator::default();
    let host_component = HashHostComponent::new(
        &mut location_allocator,
        HashHostEval {
            log_size: host.log_size,
            relations: relations.clone(),
        },
        host.claimed_sum,
    );
    verify(
        &[&host_component],
        &mut host_channel,
        &mut host_scheme,
        host.stark_proof,
    )?;

    // Precompile side: two secure LogUp columns (8 base columns, the
    // poseidon2 component pairs its entries).
    bind_joint_interaction(&mut precompile_channel, seeds, joint_interaction);
    precompile_channel.mix_felts(&[precompile.claimed_sum]);
    precompile_scheme.commit(
        precompile.stark_proof.commitments[2],
        &[precompile.log_size; 8],
        &mut precompile_channel,
    );
    let mut location_allocator = TraceLocationAllocator::default();
    let precompile_component = air::poseidon2::component::air::Component::new(
        &mut location_allocator,
        air::poseidon2::component::air::Eval {
            log_size: precompile.log_size,
            relations: relations.clone(),
        },
        precompile.claimed_sum,
    );
    verify(
        &[&precompile_component],
        &mut precompile_channel,
        &mut precompile_scheme,
        precompile.stark_proof,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config() -> PcsConfig {
        PcsConfig::default()
    }

    /// Squares of 0..6 — the honest host/precompile multiset.
    fn square_pairs() -> Vec<(u32, u32)> {
        (0u32..6).map(|x| (x, x * x)).collect()
    }

    #[test]
    fn test_binding_roundtrip_verifies() {
        let proof = prove_binding(&square_pairs(), config());
        assert!(verify_binding(proof, config()).is_ok());
    }

    #[test]
    fn test_binding_rejects_invalid_joint_interaction_pow() {
        let mut proof = prove_binding(&square_pairs(), config());
        let columns = binding_emit_dsl::prover_columns::BindingColumns::<()>::SIZE;
        proof.joint_interaction.pow_nonce =
            invalid_joint_pow_nonce(&proof.host, columns, &proof.precompile, columns);
        assert!(verify_binding(proof, config()).is_err());
    }

    #[test]
    fn test_binding_sums_cancel() {
        let proof = prove_binding(&square_pairs(), config());
        assert!((proof.host.claimed_sum + proof.precompile.claimed_sum).is_zero());
    }

    #[test]
    fn test_host_sum_alone_is_nonzero() {
        // The host's emissions do not balance on their own — the precompile
        // proof is what discharges them.
        let proof = prove_binding(&square_pairs(), config());
        assert!(!proof.host.claimed_sum.is_zero());
    }

    #[test]
    fn test_host_uses_pair_precompile_never_validated_is_rejected() {
        // The host emits a pair the precompile never proved: the multiset
        // does not close, the sums do not cancel, the binding is rejected.
        let mut host_pairs = square_pairs();
        host_pairs.push((7, 49));
        let proof = prove_binding_sides(&host_pairs, &square_pairs(), config());
        assert!(verify_binding(proof, config()).is_err());
    }

    #[test]
    fn test_precompile_validates_pair_host_never_used_is_rejected() {
        // Symmetric: an extra validated pair the host did not emit also
        // fails to cancel.
        let mut precompile_pairs = square_pairs();
        precompile_pairs.push((7, 49));
        let proof = prove_binding_sides(&square_pairs(), &precompile_pairs, config());
        assert!(verify_binding(proof, config()).is_err());
    }

    /// Distinct 16-word permutation inputs.
    fn hash_states(n: u32) -> Vec<[u32; 16]> {
        (0..n)
            .map(|i| std::array::from_fn(|j| i * 31 + j as u32 + 1))
            .collect()
    }

    fn permute(state: &[u32; 16]) -> [u32; 16] {
        let mut out = *state;
        air::poseidon2::poseidon2_permutation(&mut out);
        out
    }

    #[test]
    fn test_hash_binding_roundtrip_verifies() {
        let proof = prove_hash_binding(&hash_states(5), config());
        assert!(verify_hash_binding(proof, config()).is_ok());
    }

    #[test]
    fn test_hash_binding_rejects_invalid_joint_interaction_pow() {
        let mut proof = prove_hash_binding(&hash_states(5), config());
        proof.joint_interaction.pow_nonce = invalid_joint_pow_nonce(
            &proof.host,
            HashBindingColumns::<()>::SIZE,
            &proof.precompile,
            air::trace::prover_columns::Poseidon2Columns::<()>::SIZE,
        );
        assert!(verify_hash_binding(proof, config()).is_err());
    }

    #[test]
    fn test_hash_binding_sums_cancel() {
        let proof = prove_hash_binding(&hash_states(5), config());
        assert!((proof.host.claimed_sum + proof.precompile.claimed_sum).is_zero());
    }

    #[test]
    fn test_hash_host_forged_output_is_rejected() {
        // The host claims an io pair whose output is not the permutation of
        // its input: no precompile row discharges it, the sums do not cancel.
        let states = hash_states(3);
        let mut pairs: Vec<_> = states.iter().map(|s| (*s, permute(s))).collect();
        pairs[0].1[0] ^= 1;
        let proof = prove_hash_binding_sides(&pairs, &states, config());
        assert!(verify_hash_binding(proof, config()).is_err());
    }

    #[test]
    fn test_hash_host_unproven_tuple_is_rejected() {
        // The host uses a permutation the precompile never proved.
        let states = hash_states(3);
        let mut pairs: Vec<_> = states.iter().map(|s| (*s, permute(s))).collect();
        let extra: [u32; 16] = std::array::from_fn(|j| 1000 + j as u32);
        pairs.push((extra, permute(&extra)));
        let proof = prove_hash_binding_sides(&pairs, &states, config());
        assert!(verify_hash_binding(proof, config()).is_err());
    }

    #[test]
    fn test_hash_precompile_extra_permutation_is_rejected() {
        // Symmetric: a proven permutation the host never used fails to cancel.
        let states = hash_states(3);
        let pairs: Vec<_> = states.iter().map(|s| (*s, permute(s))).collect();
        let mut precompile_states = states.clone();
        precompile_states.push(std::array::from_fn(|j| 2000 + j as u32));
        let proof = prove_hash_binding_sides(&pairs, &precompile_states, config());
        assert!(verify_hash_binding(proof, config()).is_err());
    }

    #[test]
    fn test_forged_claimed_sum_fails_stwo_verification() {
        // Forging the host's claimed sum to force the binder's cancellation
        // check to pass cannot help: the sum is bound to the committed
        // interaction trace, so stwo verification rejects it.
        let mut proof = prove_binding(&square_pairs(), config());
        let one = SecureField::from(BaseField::from(1));
        proof.host.claimed_sum = -proof.precompile.claimed_sum + one;
        proof.precompile.claimed_sum = -proof.host.claimed_sum;
        assert!(verify_binding(proof, config()).is_err());
    }

    fn invalid_joint_pow_nonce(
        host: &SystemProof,
        host_columns: usize,
        precompile: &SystemProof,
        precompile_columns: usize,
    ) -> u64 {
        let (_, mut host_channel) = replay_system_commit(host, config(), host_columns);
        let (_, mut precompile_channel) =
            replay_system_commit(precompile, config(), precompile_columns);
        let seeds = [
            host_channel.draw_secure_felt(),
            precompile_channel.draw_secure_felt(),
        ];
        let channel = joint_interaction_channel(seeds);
        (0_u64..)
            .find(|nonce| !channel.verify_pow_nonce(INTERACTION_POW_BITS, *nonce))
            .expect("the PoW predicate rejects at least one nonce")
    }
}
