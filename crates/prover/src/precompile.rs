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
use stwo::core::vcs_lifted::blake2_merkle::{Blake2sMerkleChannel, Blake2sMerkleHasher};
use stwo::core::verifier::{VerificationError, verify};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::pcs::CommitmentSchemeProver;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::{CircleEvaluation, PolyOps};
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::prove;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
    TraceLocationAllocator, relation,
};
use stwo_macros::{combine, define_component_tables};

// The binding tables. `binding` is one row per `(x, y)` pair of the square
// exemplar, on either side of the shared relation: the host fills it with
// the pairs it used, the precompile with the pairs it validated.
// `hash_binding` is the widened host side of the Poseidon2 precompile: one
// row per permutation the host used, carrying the full 32-word io tuple; the
// precompile side is the stark-v `poseidon2` component itself (io rows).
define_component_tables! {
    binding: {
        committed: { x, y },
    },
    hash_binding: {
        committed: {
            in_0, in_1, in_2, in_3, in_4, in_5, in_6, in_7,
            in_8, in_9, in_10, in_11, in_12, in_13, in_14, in_15,
            out_0, out_1, out_2, out_3, out_4, out_5, out_6, out_7,
            out_8, out_9, out_10, out_11, out_12, out_13, out_14, out_15,
        },
    },
}

use prover_columns::{BindingColumns, HashBindingColumns};

// The shared relation, arity 2: `(x, y)`. A real precompile widens this to
// the hash io tuple, e.g. `poseidon2_io(in_0..15, out_0..15)`.
relation!(ValueRelation, 2);

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

/// AIR of one binding side.
#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub value: ValueRelation,
    pub role: Role,
}

pub type Component = FrameworkComponent<Eval>;

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = BindingColumns::from_eval(&mut eval);
        // Enabler booleanity (generated) for every row.
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        // The precompile is the only side that proves the relationship.
        if self.role == Role::ConsumeSquare {
            eval.add_constraint(cols.y.clone() - cols.x.clone() * cols.x.clone());
        }
        let numerator = match self.role {
            Role::Emit => E::EF::from(cols.enabler.clone()),
            Role::ConsumeSquare => -E::EF::from(cols.enabler.clone()),
        };
        eval.add_to_relation(RelationEntry::new(
            &self.value,
            numerator,
            &[cols.x.clone(), cols.y.clone()],
        ));
        eval.finalize_logup();
        eval
    }
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
    let cols = BindingColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let denom = combine!(value, [cols.x, cols.y]);

    debug_assert_eq!(denom.len(), simd_size);
    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();
    for (vec_row, &denominator) in denom.iter().enumerate() {
        let enabler = PackedQM31::from(cols.enabler[vec_row]);
        let numerator = match role {
            Role::Emit => enabler,
            Role::ConsumeSquare => -enabler,
        };
        col_gen.write_frac(vec_row, numerator, denominator);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

/// One side's proof: its trace size, its claimed LogUp sum, and the stwo
/// proof. The trace-tree commitment inside `stark_proof` seeds the shared
/// relation.
pub struct SystemProof {
    pub log_size: u32,
    pub claimed_sum: SecureField,
    pub stark_proof: StarkProof<H>,
}

/// A bound pair of proofs: the host that used the pairs and the precompile
/// that validated them.
pub struct PrecompileBindingProof {
    pub host: SystemProof,
    pub precompile: SystemProof,
}

/// Draw the shared relation from both trace commitments' channel seeds.
///
/// Deterministic in both prover and verifier: the relation is a public
/// function of both proofs' trace roots, so neither prover commits its trace
/// after learning the relation.
fn draw_shared_relation(seed_host: SecureField, seed_precompile: SecureField) -> ValueRelation {
    let mut channel = Blake2sChannel::default();
    channel.mix_felts(&[seed_host, seed_precompile]);
    ValueRelation::draw(&mut channel)
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

    let mut location_allocator = TraceLocationAllocator::default();
    let component = Component::new(
        &mut location_allocator,
        Eval {
            log_size,
            value: value.clone(),
            role,
        },
        claimed_sum,
    );
    let stark_proof =
        prove(&[&component], channel, commitment_scheme).expect("binding proof generation failed");

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
    let mut host_table = BindingTable::new();
    let mut precompile_table = BindingTable::new();
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
    let value = draw_shared_relation(seed_host, seed_precompile);

    // Bind the shared relation into each transcript.
    host_channel.mix_felts(&[seed_host, seed_precompile]);
    precompile_channel.mix_felts(&[seed_host, seed_precompile]);

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

    PrecompileBindingProof { host, precompile }
}

/// Replay one side's commitment phase, leaving the verifier channel at the
/// post-commit state. Mirrors [`commit_system`].
fn replay_commit(
    proof: &SystemProof,
    config: PcsConfig,
) -> (CommitmentSchemeVerifier<MC>, Blake2sChannel) {
    let mut channel = Blake2sChannel::default();
    let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);
    let commitments = &proof.stark_proof.commitments;

    commitment_scheme.commit(commitments[0], &[], &mut channel);
    channel.mix_u32s(&[proof.log_size]);
    let trace_log_sizes = vec![proof.log_size; BindingColumns::<()>::SIZE];
    commitment_scheme.commit(commitments[1], &trace_log_sizes, &mut channel);

    (commitment_scheme, channel)
}

/// Finish verifying one side: bind the shared relation, commit the
/// interaction tree, and run stwo verification against the matching role.
fn verify_system(
    proof: SystemProof,
    mut commitment_scheme: CommitmentSchemeVerifier<MC>,
    channel: &mut Blake2sChannel,
    value: &ValueRelation,
    role: Role,
    seeds: [SecureField; 2],
) -> Result<(), VerificationError> {
    channel.mix_felts(&seeds);
    channel.mix_felts(&[proof.claimed_sum]);

    // One secure column (4 base columns) of LogUp fractions.
    let interaction_log_sizes = vec![proof.log_size; 4];
    commitment_scheme.commit(
        proof.stark_proof.commitments[2],
        &interaction_log_sizes,
        channel,
    );

    let mut location_allocator = TraceLocationAllocator::default();
    let component = Component::new(
        &mut location_allocator,
        Eval {
            log_size: proof.log_size,
            value: value.clone(),
            role,
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

/// Verify a bound pair: both stwo proofs hold, and their claimed LogUp sums
/// cancel under the shared relation.
///
/// Cancellation is the binding: every `value(x, y)` the host emitted was
/// consumed by a precompile row that proved `y = x * x`.
pub fn verify_binding(
    proof: PrecompileBindingProof,
    config: PcsConfig,
) -> Result<(), VerificationError> {
    let PrecompileBindingProof { host, precompile } = proof;

    let (host_scheme, mut host_channel) = replay_commit(&host, config);
    let (precompile_scheme, mut precompile_channel) = replay_commit(&precompile, config);

    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let value = draw_shared_relation(seed_host, seed_precompile);

    // The cross-proof binding check.
    if !(host.claimed_sum + precompile.claimed_sum).is_zero() {
        return Err(VerificationError::InvalidStructure(
            "precompile binding: host and precompile claimed sums do not cancel".to_string(),
        ));
    }

    let seeds = [seed_host, seed_precompile];
    verify_system(
        host,
        host_scheme,
        &mut host_channel,
        &value,
        Role::Emit,
        seeds,
    )?;
    verify_system(
        precompile,
        precompile_scheme,
        &mut precompile_channel,
        &value,
        Role::ConsumeSquare,
        seeds,
    )
}

// =============================================================================
// The real precompile: Poseidon2 over the 32-word `poseidon2_io` relation
// =============================================================================

use crate::relations::Relations;
use air::poseidon2::poseidon2_traced_state;
use air::trace::Poseidon2Table;

/// AIR of the host side of the Poseidon2 binding: each row consumes one
/// `poseidon2_io(in_0..15, out_0..15)` tuple the host used. No constraint
/// ties the output to the input — the precompile proof owns the permutation.
#[derive(Clone)]
pub struct HashHostEval {
    pub log_size: u32,
    pub relations: Relations,
}

pub type HashHostComponent = FrameworkComponent<HashHostEval>;

impl FrameworkEval for HashHostEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = HashBindingColumns::from_eval(&mut eval);
        for constraint in cols.constraints() {
            eval.add_constraint(constraint);
        }
        let tuple = [
            cols.in_0.clone(),
            cols.in_1.clone(),
            cols.in_2.clone(),
            cols.in_3.clone(),
            cols.in_4.clone(),
            cols.in_5.clone(),
            cols.in_6.clone(),
            cols.in_7.clone(),
            cols.in_8.clone(),
            cols.in_9.clone(),
            cols.in_10.clone(),
            cols.in_11.clone(),
            cols.in_12.clone(),
            cols.in_13.clone(),
            cols.in_14.clone(),
            cols.in_15.clone(),
            cols.out_0.clone(),
            cols.out_1.clone(),
            cols.out_2.clone(),
            cols.out_3.clone(),
            cols.out_4.clone(),
            cols.out_5.clone(),
            cols.out_6.clone(),
            cols.out_7.clone(),
            cols.out_8.clone(),
            cols.out_9.clone(),
            cols.out_10.clone(),
            cols.out_11.clone(),
            cols.out_12.clone(),
            cols.out_13.clone(),
            cols.out_14.clone(),
            cols.out_15.clone(),
        ];
        eval.add_to_relation(RelationEntry::new(
            &self.relations.poseidon2_io,
            -E::EF::from(cols.enabler.clone()),
            &tuple,
        ));
        eval.finalize_logup();
        eval
    }
}

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
    let cols = HashBindingColumns::from_iter(trace.iter().map(|eval| &eval.values.data));
    let log_size = trace[0].domain.log_size();
    let denom = combine!(
        relations.poseidon2_io,
        [
            cols.in_0,
            cols.in_1,
            cols.in_2,
            cols.in_3,
            cols.in_4,
            cols.in_5,
            cols.in_6,
            cols.in_7,
            cols.in_8,
            cols.in_9,
            cols.in_10,
            cols.in_11,
            cols.in_12,
            cols.in_13,
            cols.in_14,
            cols.in_15,
            cols.out_0,
            cols.out_1,
            cols.out_2,
            cols.out_3,
            cols.out_4,
            cols.out_5,
            cols.out_6,
            cols.out_7,
            cols.out_8,
            cols.out_9,
            cols.out_10,
            cols.out_11,
            cols.out_12,
            cols.out_13,
            cols.out_14,
            cols.out_15
        ]
    );

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    let mut col_gen = logup_gen.new_col();
    for (vec_row, &denominator) in denom.iter().enumerate() {
        let numerator = -PackedQM31::from(cols.enabler[vec_row]);
        col_gen.write_frac(vec_row, numerator, denominator);
    }
    col_gen.finalize_col();
    logup_gen.finalize_last()
}

/// A bound pair of proofs for the Poseidon2 precompile: the host that used
/// the permutations and the stark-v `poseidon2` component instance that
/// proved them (io rows, so only the atomic 32-word tuples are emitted).
pub struct HashPrecompileBindingProof {
    pub host: SystemProof,
    pub precompile: SystemProof,
}

/// Draw the full relation set from both trace commitments' channel seeds.
/// The `poseidon2_io` member is the shared relation; drawing the whole set
/// keeps the precompile side's component byte-identical to the zkVM's.
fn draw_shared_relations(seed_host: SecureField, seed_precompile: SecureField) -> Relations {
    let mut channel = Blake2sChannel::default();
    channel.mix_felts(&[seed_host, seed_precompile]);
    Relations::draw(&mut channel)
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
    let relations = draw_shared_relations(seed_host, seed_precompile);
    host_channel.mix_felts(&[seed_host, seed_precompile]);
    precompile_channel.mix_felts(&[seed_host, seed_precompile]);

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
    let HashPrecompileBindingProof { host, precompile } = proof;

    let replay = |proof: &SystemProof, n_columns: usize| {
        let mut channel = Blake2sChannel::default();
        let mut commitment_scheme = CommitmentSchemeVerifier::<MC>::new(config);
        let commitments = &proof.stark_proof.commitments;
        commitment_scheme.commit(commitments[0], &[], &mut channel);
        channel.mix_u32s(&[proof.log_size]);
        commitment_scheme.commit(
            commitments[1],
            &vec![proof.log_size; n_columns],
            &mut channel,
        );
        (commitment_scheme, channel)
    };
    let (mut host_scheme, mut host_channel) = replay(&host, HashBindingColumns::<()>::SIZE);
    let (mut precompile_scheme, mut precompile_channel) = replay(
        &precompile,
        air::trace::prover_columns::Poseidon2Columns::<()>::SIZE,
    );

    let seed_host = host_channel.draw_secure_felt();
    let seed_precompile = precompile_channel.draw_secure_felt();
    let relations = draw_shared_relations(seed_host, seed_precompile);
    let seeds = [seed_host, seed_precompile];

    // The cross-proof binding check.
    if !(host.claimed_sum + precompile.claimed_sum).is_zero() {
        return Err(VerificationError::InvalidStructure(
            "hash precompile binding: claimed sums do not cancel".to_string(),
        ));
    }

    // Host side: one secure LogUp column (4 base columns).
    host_channel.mix_felts(&seeds);
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
    precompile_channel.mix_felts(&seeds);
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
}
