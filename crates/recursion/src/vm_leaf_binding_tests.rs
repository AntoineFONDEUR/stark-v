//! End-to-end relation closure for the current protocol VM leaf public boundary.
//!
//! The test composes the fixed claim source, both Poseidon hash lanes, the
//! claim-to-statement circuit, transcript-owned VM relation challenges, public
//! LogUp arithmetic and control, shared arithmetic tables, and the standard
//! byte-range table under one independently drawn relation set. Only external
//! statement, transcript-draw, AIR-challenge, and proof-input terms remain
//! explicit verifier anchors.

use air::digest::M31Word;
use air::trace::Poseidon2Table;
use num_traits::Zero;
use prover::poseidon2_channel::Poseidon2M31Channel;
use stwo::core::channel::Channel;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use crate::circuit::CircuitTraces;
use crate::relations::RecursionRelations;
use crate::{linear_ops, qm31_inv, qm31_mul};

use super::control_air::{ControlRelations, SEGMENT_VERIFIER_ID};
use super::kernel::{VerifierSchema, VerifierStep};
use super::relation_challenge_air::{
    AIR_EVALUATION_CHALLENGE_SCOPE, RelationChallengePreprocessed, RelationChallengeRelations,
    RelationChallengeTable, gen_interaction_trace as gen_relation_challenge_interaction,
    push_relation_challenges,
};
use super::statement::SPAN_STATEMENT_CANONICAL_WORDS;
use super::statement_input_air::{StatementInputRelations, VM_CLAIM_STATEMENT_SCOPE};
use super::transcript::RecordingTranscriptBackend;
use super::transcript_binding_air::UniversalTranscriptWitness;
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::transcript_program::VerifierTranscriptExecution;
use super::transcript_program::tests::{
    plan_for_schema_with_counts, recording_execution_for_with_claimed_sum,
};
use super::transcript_state_air::TranscriptStateRelations;
use super::vm_public_claim::tests::{public_data, shape};
use super::vm_public_claim::{
    VmPublicClaimShape, canonical_vm_public_claim_words, vm_public_claim_digest,
};
use super::vm_public_claim_hash_air::{
    VmPublicClaimHashPreprocessed, VmPublicClaimHashRelations, VmPublicClaimHashTable,
    gen_interaction_trace as gen_claim_hash_interaction, push_vm_public_claim_hash,
};
use super::vm_public_claim_input_air::{
    VmPublicClaimInputPreprocessed, VmPublicClaimInputRelations, VmPublicClaimInputTable,
    gen_interaction_trace as gen_claim_input_interaction, push_vm_public_claim_inputs,
    register_range_check_multiplicities,
};
use super::vm_public_claim_semantics_circuit::tests::{valid_digests, valid_words};
use super::vm_public_claim_semantics_circuit::{
    VmPublicClaimSemanticsCircuit, VmPublicClaimSemanticsWitness,
    build_vm_public_claim_semantics_circuit,
};
use super::vm_public_claim_semantics_input_air::{
    VmPublicClaimSemanticsInputPreprocessed, VmPublicClaimSemanticsInputTable,
    gen_interaction_trace as gen_semantic_input_interaction, push_vm_public_claim_semantics_inputs,
};
use super::vm_public_claim_semantics_lowering::{
    lower_vm_public_claim_semantics_circuit, public_vm_public_claim_semantics_terms,
};
use super::vm_public_io_hash_air::{
    VmPublicIoHashPreprocessed, VmPublicIoHashRelations, VmPublicIoHashTable,
    gen_interaction_trace as gen_io_hash_interaction, push_vm_public_io_hashes,
};
use super::vm_public_logup_circuit::{
    VmPublicLogupChallengeWords, VmPublicLogupWitness, build_vm_public_logup_circuit,
    build_vm_public_logup_reference,
};
use super::vm_public_logup_control_air::{
    VmPublicLogupControlPreprocessed, gen_interaction_trace as gen_public_logup_control_interaction,
};
use super::vm_public_logup_input_air::{
    VmPublicLogupInputPreprocessed, VmPublicLogupInputTable,
    gen_interaction_trace as gen_public_logup_input_interaction, push_vm_public_logup_inputs,
};
use super::vm_public_logup_lowering::{
    lower_vm_public_logup_circuit, public_vm_public_logup_terms,
};
use super::wire::ProofKind;

const SEMANTIC_CIRCUIT_ID: u32 = 23;
const PUBLIC_LOGUP_CIRCUIT_ID: u32 = 24;
const VM_RELATION_CHALLENGE_COUNT: u32 = 12;

fn semantic_circuits() -> (
    VmPublicClaimSemanticsCircuit,
    VmPublicClaimSemanticsCircuit,
    Vec<M31Word>,
    [M31Word; SPAN_STATEMENT_CANONICAL_WORDS],
) {
    let shape = shape();
    let (claim, statement) = valid_words();
    let zero_claim = vec![M31Word::ZERO; claim.len()];
    let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
    let zero_digest = [M31Word::ZERO; 8];
    let (input_digest, output_digest) = valid_digests();
    let reference = build_vm_public_claim_semantics_circuit(
        shape,
        VmPublicClaimSemanticsWitness {
            segment_selector: false,
            claim_words: &zero_claim,
            statement_words: &zero_statement,
            input_digest: &zero_digest,
            output_digest: &zero_digest,
        },
    )
    .expect("reference leaf circuit has fixed widths");
    let witness = build_vm_public_claim_semantics_circuit(
        shape,
        VmPublicClaimSemanticsWitness {
            segment_selector: true,
            claim_words: &claim,
            statement_words: &statement,
            input_digest: &input_digest,
            output_digest: &output_digest,
        },
    )
    .expect("fixture leaf circuit has fixed widths");
    (reference, witness, claim, statement)
}

fn leaf_binding_relation_sum(mut channel: Poseidon2M31Channel) -> SecureField {
    let shape = shape();
    let public_data = public_data();
    let (reference, witness, _claim_words, statement_words) = semantic_circuits();
    let public_logup_reference = build_vm_public_logup_reference(shape, 1)
        .expect("fixture public LogUp reference is representable");
    let vm_plan = plan_for_schema_with_counts(
        VerifierSchema::Vm,
        1,
        VM_RELATION_CHALLENGE_COUNT,
        public_logup_reference.public_term_count(),
    );
    let recursion_plan = plan_for_schema_with_counts(VerifierSchema::Recursion, 1, 1, 0);
    let provisional_execution =
        recording_execution_for_with_claimed_sum(&vm_plan, 1, SecureField::zero());
    let challenge_words = public_logup_challenge_words(&provisional_execution);
    let public_claim_words = canonical_vm_public_claim_words(&public_data, shape)
        .expect("fixture public claim is canonical");
    let provisional_public_logup = build_vm_public_logup_circuit(
        shape,
        1,
        VmPublicLogupWitness {
            segment_selector: true,
            claim_words: &public_claim_words,
            relation_challenges: challenge_words,
            claimed_sums: &[SecureField::zero()],
        },
    )
    .expect("fixture public relation denominators are nonzero");
    let interaction_claimed_sum = -provisional_public_logup.constrained_sum();
    let transcript_execution =
        recording_execution_for_with_claimed_sum(&vm_plan, 1, interaction_claimed_sum);
    let challenge_words = public_logup_challenge_words(&transcript_execution);
    let public_logup_witness = build_vm_public_logup_circuit(
        shape,
        1,
        VmPublicLogupWitness {
            segment_selector: true,
            claim_words: &public_claim_words,
            relation_challenges: challenge_words,
            claimed_sums: &[interaction_claimed_sum],
        },
    )
    .expect("fixture public LogUp equation closes");

    let recursion_relations = RecursionRelations::draw(&mut channel);
    let vm_relations = prover::relations::Relations::draw(&mut channel);
    let claim_relations = VmPublicClaimInputRelations::draw(&mut channel);
    let claim_hash_relations = VmPublicClaimHashRelations::draw(&mut channel);
    let io_hash_relations = VmPublicIoHashRelations::draw(&mut channel);
    let statement_relations = StatementInputRelations::draw(&mut channel);
    let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
    let transcript_state_relations = TranscriptStateRelations::draw(&mut channel);
    let relation_challenge_relations = RelationChallengeRelations::draw(&mut channel);
    let control_relations = ControlRelations::draw(&mut channel);

    let claim_preprocessing =
        VmPublicClaimInputPreprocessed::new(shape).expect("fixture claim shape is supported");
    let mut claim_table = VmPublicClaimInputTable::new();
    push_vm_public_claim_inputs(
        &mut claim_table,
        &claim_preprocessing,
        ProofKind::SegmentLeaf,
        Some(&public_data),
    )
    .expect("fixture public claim materializes");
    let claim_trace = claim_table.into_witness();
    let claim_preprocessed = claim_preprocessing.gen_columns();
    let mut counters = prover::relations::Counters::new();
    register_range_check_multiplicities(
        &claim_trace,
        &claim_preprocessed,
        ProofKind::SegmentLeaf,
        &mut counters,
    );
    let range_trace = counters.range_check_8_8.into_trace();
    let (_, range_sum) =
        prover::components::lookups::range_check_8_8::witness::gen_interaction_trace(
            &range_trace,
            &vm_relations,
        );
    let (_, claim_input_sum) = gen_claim_input_interaction(
        &claim_trace,
        &claim_preprocessed,
        ProofKind::SegmentLeaf,
        &claim_relations,
        &vm_relations,
    );

    let challenge_preprocessing = RelationChallengePreprocessed::new(&vm_plan, &recursion_plan)
        .expect("fixture plans have canonical relation draws");
    let mut challenge_table = RelationChallengeTable::new();
    push_relation_challenges(
        &mut challenge_table,
        &challenge_preprocessing,
        UniversalTranscriptWitness::Segment(&transcript_execution),
    )
    .expect("fixture transcript challenges materialize");
    let (_, relation_challenge_sum) = gen_relation_challenge_interaction(
        &challenge_table.into_witness(),
        &challenge_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &transcript_state_relations,
        &relation_challenge_relations,
    );

    let public_control_preprocessing =
        VmPublicLogupControlPreprocessed::new(&vm_plan, public_logup_reference.public_term_count())
            .expect("fixture VM public control slice is exact");
    let (_, public_control_sum) = gen_public_logup_control_interaction(
        &public_control_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &control_relations,
    );

    let mut poseidon = Poseidon2Table::new();
    let claim_hash_preprocessing =
        VmPublicClaimHashPreprocessed::new(shape).expect("fixture claim shape is supported");
    let mut claim_hash_table = VmPublicClaimHashTable::new();
    push_vm_public_claim_hash(
        &mut claim_hash_table,
        &mut poseidon,
        &claim_hash_preprocessing,
        ProofKind::SegmentLeaf,
        Some(&public_data),
    )
    .expect("fixture claim hash materializes");
    let (_, claim_hash_sum) = gen_claim_hash_interaction(
        &claim_hash_table.into_witness(),
        &claim_hash_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &vm_relations,
        &claim_relations,
        &claim_hash_relations,
        &verifier_input_relations,
    );

    let io_hash_preprocessing =
        VmPublicIoHashPreprocessed::new(shape).expect("fixture IO shape is supported");
    let mut io_hash_table = VmPublicIoHashTable::new();
    push_vm_public_io_hashes(
        &mut io_hash_table,
        &mut poseidon,
        &io_hash_preprocessing,
        ProofKind::SegmentLeaf,
        Some(&public_data),
    )
    .expect("fixture IO hashes materialize");
    let (_, io_hash_sum) = gen_io_hash_interaction(
        &io_hash_table.into_witness(),
        &io_hash_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &vm_relations,
        &claim_relations,
        &io_hash_relations,
    );
    let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
        &poseidon.into_witness(),
        &vm_relations,
    );

    let semantic_preprocessing =
        VmPublicClaimSemanticsInputPreprocessed::new(&reference, SEMANTIC_CIRCUIT_ID)
            .expect("reference semantic inputs are canonical");
    let mut semantic_table = VmPublicClaimSemanticsInputTable::new();
    push_vm_public_claim_semantics_inputs(
        &mut semantic_table,
        &semantic_preprocessing,
        &reference,
        &witness,
        ProofKind::SegmentLeaf,
    )
    .expect("fixture semantic inputs materialize");
    let (_, semantic_input_sum) = gen_semantic_input_interaction(
        &semantic_table.into_witness(),
        &semantic_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &claim_relations,
        &statement_relations,
        &recursion_relations,
        &io_hash_relations,
    );

    let public_logup_input_preprocessing =
        VmPublicLogupInputPreprocessed::new(&public_logup_reference, PUBLIC_LOGUP_CIRCUIT_ID)
            .expect("reference public LogUp inputs are canonical");
    let mut public_logup_input_table = VmPublicLogupInputTable::new();
    push_vm_public_logup_inputs(
        &mut public_logup_input_table,
        &public_logup_input_preprocessing,
        &public_logup_reference,
        &public_logup_witness,
        ProofKind::SegmentLeaf,
    )
    .expect("fixture public LogUp inputs materialize");
    let (_, public_logup_input_sum) = gen_public_logup_input_interaction(
        &public_logup_input_table.into_witness(),
        &public_logup_input_preprocessing.gen_columns(),
        ProofKind::SegmentLeaf,
        &claim_relations,
        &relation_challenge_relations,
        &verifier_input_relations,
        &recursion_relations,
    );

    let mut recursion_traces = CircuitTraces::default();
    lower_vm_public_claim_semantics_circuit(
        &mut recursion_traces,
        SEMANTIC_CIRCUIT_ID,
        &reference,
        &witness,
    )
    .expect("fixture semantic circuit lowers");
    lower_vm_public_logup_circuit(
        &mut recursion_traces,
        PUBLIC_LOGUP_CIRCUIT_ID,
        &public_logup_reference,
        &public_logup_witness,
    )
    .expect("fixture public LogUp circuit lowers");
    let (_, mul_sum) = qm31_mul::gen_interaction_trace(
        &recursion_traces.qm31_mul.into_witness(),
        &recursion_relations,
    );
    let (_, linear_sum) = linear_ops::gen_interaction_trace(
        &recursion_traces.linear_ops.into_witness(),
        &recursion_relations,
    );
    let (_, inverse_sum) = qm31_inv::gen_interaction_trace(
        &recursion_traces.qm31_inv.into_witness(),
        &recursion_relations,
    );
    let semantic_public_sum = public_vm_public_claim_semantics_terms(
        SEMANTIC_CIRCUIT_ID,
        &reference,
        &recursion_relations,
    )
    .expect("reference semantic circuit has zero outputs");
    let public_logup_public_sum = public_vm_public_logup_terms(
        PUBLIC_LOGUP_CIRCUIT_ID,
        &public_logup_reference,
        &recursion_relations,
    )
    .expect("reference public LogUp circuit has a zero output");

    claim_input_sum
        + relation_challenge_sum
        + public_control_sum
        + claim_hash_sum
        + io_hash_sum
        + poseidon_sum
        + semantic_input_sum
        + public_logup_input_sum
        + mul_sum
        + linear_sum
        + inverse_sum
        + semantic_public_sum
        + public_logup_public_sum
        + range_sum
        + statement_source_terms(&statement_words, &statement_relations)
        + claim_digest_source_terms(&public_data, shape, &verifier_input_relations)
        + claimed_sum_source_terms(interaction_claimed_sum, &verifier_input_relations)
        + transcript_draw_source_terms(&transcript_execution, &transcript_state_relations)
        + air_challenge_sink_terms(&transcript_execution, &relation_challenge_relations)
        + public_control_source_terms(&vm_plan, &control_relations)
}

fn public_logup_challenge_words(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
) -> VmPublicLogupChallengeWords {
    VmPublicLogupChallengeWords::new(
        relation_challenge_draw(execution, 0),
        relation_challenge_draw(execution, 1),
        relation_challenge_draw(execution, 3),
    )
}

fn relation_challenge_draw(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    challenge: u32,
) -> [M31Word; 8] {
    execution
        .operations()
        .iter()
        .find(|operation| operation.step() == VerifierStep::DrawRelationChallenge { challenge })
        .and_then(|operation| operation.draw())
        .expect("fixture transcript contains every requested VM relation challenge")
}

fn claimed_sum_source_terms(
    claimed_sum: SecureField,
    relations: &VerifierInputRelations,
) -> SecureField {
    claimed_sum.to_m31_array().into_iter().enumerate().fold(
        SecureField::zero(),
        |sum, (limb, value)| {
            let denominator: SecureField = relations.input_word.combine(&[
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(VerifierInputKind::ClaimedSum.as_u32()),
                M31::from(0),
                M31::from(u32::try_from(limb).expect("claimed-sum limb fits u32")),
                value,
            ]);
            sum + denominator.inverse()
        },
    )
}

fn transcript_draw_source_terms(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    relations: &TranscriptStateRelations,
) -> SecureField {
    execution
        .operations()
        .iter()
        .filter_map(|operation| {
            let VerifierStep::DrawRelationChallenge { .. } = operation.step() else {
                return None;
            };
            let encoded = operation.step().encode();
            let mut tuple = vec![
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(operation.sequence()),
                M31::from(encoded.tag()),
                M31::from(encoded.args()[0]),
                M31::from(encoded.args()[1]),
                M31::from(encoded.args()[2]),
                M31::from(encoded.args()[3]),
            ];
            tuple.extend(
                operation
                    .draw()
                    .expect("relation challenge operation has a draw")
                    .map(|word| M31::from(word.as_u32())),
            );
            let denominator: SecureField = relations.draw_output.combine(&tuple);
            Some(denominator.inverse())
        })
        .fold(SecureField::zero(), |sum, term| sum + term)
}

fn air_challenge_sink_terms(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    relations: &RelationChallengeRelations,
) -> SecureField {
    execution
        .operations()
        .iter()
        .filter_map(|operation| {
            let VerifierStep::DrawRelationChallenge { challenge } = operation.step() else {
                return None;
            };
            Some((
                challenge,
                operation
                    .draw()
                    .expect("relation challenge operation has a draw"),
            ))
        })
        .flat_map(|(challenge, words)| {
            words
                .into_iter()
                .enumerate()
                .map(move |(word_index, word)| {
                    let denominator: SecureField = relations.word.combine(&[
                        M31::from(SEGMENT_VERIFIER_ID),
                        M31::from(AIR_EVALUATION_CHALLENGE_SCOPE),
                        M31::from(challenge),
                        M31::from(
                            u32::try_from(word_index).expect("relation challenge word fits u32"),
                        ),
                        M31::from(word.as_u32()),
                    ]);
                    -denominator.inverse()
                })
        })
        .fold(SecureField::zero(), |sum, term| sum + term)
}

fn public_control_source_terms(
    plan: &super::kernel::VerifierControlPlan,
    relations: &ControlRelations,
) -> SecureField {
    plan.steps()
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, step)| {
            matches!(
                step,
                VerifierStep::AccumulatePublicLogupTerm { .. }
                    | VerifierStep::AssertGlobalLogupZero
            )
        })
        .fold(SecureField::zero(), |sum, (sequence, step)| {
            let encoded = step.encode();
            let denominator: SecureField = relations.step.combine(&[
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(u32::try_from(sequence).expect("control sequence fits u32")),
                M31::from(encoded.tag()),
                M31::from(encoded.args()[0]),
                M31::from(encoded.args()[1]),
                M31::from(encoded.args()[2]),
                M31::from(encoded.args()[3]),
            ]);
            sum + denominator.inverse()
        })
}

fn statement_source_terms(
    words: &[M31Word; SPAN_STATEMENT_CANONICAL_WORDS],
    relations: &StatementInputRelations,
) -> SecureField {
    words
        .iter()
        .copied()
        .enumerate()
        .fold(SecureField::zero(), |sum, (index, word)| {
            let denominator: SecureField = relations.statement_word.combine(&[
                M31::from(VM_CLAIM_STATEMENT_SCOPE),
                M31::from(u32::try_from(index).expect("statement word index fits u32")),
                M31::from(word.as_u32()),
            ]);
            sum + denominator.inverse()
        })
}

fn claim_digest_source_terms(
    public_data: &prover::public_data::PublicData,
    shape: VmPublicClaimShape,
    relations: &VerifierInputRelations,
) -> SecureField {
    vm_public_claim_digest(public_data, shape)
        .expect("fixture public claim digest is canonical")
        .digest()
        .words()
        .iter()
        .copied()
        .enumerate()
        .fold(SecureField::zero(), |sum, (limb, word)| {
            let denominator: SecureField = relations.input_word.combine(&[
                M31::from(SEGMENT_VERIFIER_ID),
                M31::from(VerifierInputKind::VmPublicClaimDigest.as_u32()),
                M31::from(0),
                M31::from(u32::try_from(limb).expect("digest limb fits u32")),
                M31::from(word.as_u32()),
            ]);
            sum + denominator.inverse()
        })
}

#[test]
fn complete_vm_leaf_public_boundary_relations_cancel() {
    assert_eq!(
        leaf_binding_relation_sum(Poseidon2M31Channel::default()),
        SecureField::zero()
    );
}

#[test]
fn vm_leaf_public_boundary_closure_is_challenge_independent() {
    let mut channel = Poseidon2M31Channel::default();
    channel.mix_u32s(&[1]);
    assert_eq!(leaf_binding_relation_sum(channel), SecureField::zero());
}
