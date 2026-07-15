//! End-to-end relation closure for the V2 VM leaf public boundary.
//!
//! The test composes the fixed claim source, both Poseidon hash lanes, the
//! claim-to-statement circuit, shared arithmetic tables, and standard byte
//! range table under one independently drawn relation set. Only the external
//! statement and transcript inputs remain as explicit verifier terms.

use air::digest::M31Word;
use air::trace::Poseidon2Table;
use num_traits::Zero;
use prover::poseidon2_channel::Poseidon2M31Channel;
use stwo::core::channel::Channel;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use crate::prover::RecursionTraces;
use crate::relations::RecursionRelations;
use crate::{linear_ops, qm31_mul};

use super::control_air::SEGMENT_VERIFIER_ID;
use super::statement::SPAN_STATEMENT_CANONICAL_WORDS;
use super::statement_input_air::{StatementInputRelations, VM_CLAIM_STATEMENT_SCOPE};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::vm_public_claim::tests::{public_data, shape};
use super::vm_public_claim::{VmPublicClaimShape, vm_public_claim_digest};
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
use super::wire::ProofKind;

const CIRCUIT_ID: u32 = 23;

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

    let recursion_relations = RecursionRelations::draw(&mut channel);
    let vm_relations = prover::relations::Relations::draw(&mut channel);
    let claim_relations = VmPublicClaimInputRelations::draw(&mut channel);
    let claim_hash_relations = VmPublicClaimHashRelations::draw(&mut channel);
    let io_hash_relations = VmPublicIoHashRelations::draw(&mut channel);
    let statement_relations = StatementInputRelations::draw(&mut channel);
    let verifier_input_relations = VerifierInputRelations::draw(&mut channel);

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
        VmPublicClaimSemanticsInputPreprocessed::new(&reference, CIRCUIT_ID)
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

    let mut recursion_traces = RecursionTraces::default();
    lower_vm_public_claim_semantics_circuit(
        &mut recursion_traces,
        CIRCUIT_ID,
        &reference,
        &witness,
    )
    .expect("fixture semantic circuit lowers");
    let (_, mul_sum) = qm31_mul::gen_interaction_trace(
        &recursion_traces.qm31_mul.into_witness(),
        &recursion_relations,
    );
    let (_, linear_sum) = linear_ops::gen_interaction_trace(
        &recursion_traces.linear_ops.into_witness(),
        &recursion_relations,
    );
    let semantic_public_sum =
        public_vm_public_claim_semantics_terms(CIRCUIT_ID, &reference, &recursion_relations)
            .expect("reference semantic circuit has zero outputs");

    claim_input_sum
        + claim_hash_sum
        + io_hash_sum
        + poseidon_sum
        + semantic_input_sum
        + mul_sum
        + linear_sum
        + semantic_public_sum
        + range_sum
        + statement_source_terms(&statement_words, &statement_relations)
        + claim_digest_source_terms(&public_data, shape, &verifier_input_relations)
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
