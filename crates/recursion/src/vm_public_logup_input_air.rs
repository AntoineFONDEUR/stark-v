//! AIR ownership for VM public-LogUp arithmetic circuit inputs.
//!
//! Verifier preprocessing assigns every circuit input to one transcript-bound
//! claim word, range-checked claim byte, relation-challenge word, claimed-sum
//! limb, or the public segment selector. Each source is consumed once and each
//! circuit wire is emitted with its exact static use count.

use core::fmt;
use std::collections::HashSet;

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::circuit::use_counts_for_outputs;
use crate::recorder::Op;
use crate::relations::RecursionRelations;

use super::control_air::SEGMENT_VERIFIER_ID;
use super::relation_challenge_air::{RelationChallengeRelations, VM_PUBLIC_LOGUP_CHALLENGE_SCOPE};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::vm_public_claim::{VmPublicClaimWordKind, canonical_vm_public_claim_word_kinds};
use super::vm_public_claim_input_air::{VM_PUBLIC_LOGUP_SCOPE, VmPublicClaimInputRelations};
use super::vm_public_logup_circuit::{VmPublicLogupCircuit, VmPublicLogupInputSource};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;
const QM31_LIMBS: u32 = 4;
const CHALLENGE_WORDS: u32 = 8;

const ROW_MASK_COLUMN: usize = 0;
const CLAIM_WORD_MASK_COLUMN: usize = 1;
const CLAIM_BYTE_MASK_COLUMN: usize = 2;
const CHALLENGE_MASK_COLUMN: usize = 3;
const CLAIMED_SUM_MASK_COLUMN: usize = 4;
const SELECTOR_MASK_COLUMN: usize = 5;
const CIRCUIT_ID_COLUMN: usize = 6;
const NODE_ID_COLUMN: usize = 7;
const USE_COUNT_COLUMN: usize = 8;
const SOURCE_INDEX_0_COLUMN: usize = 9;
const SOURCE_INDEX_1_COLUMN: usize = 10;
const PREPROCESSED_COLUMN_COUNT: usize = 11;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: VmPublicLogupInputSource,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    source_index_0: u32,
    source_index_1: u32,
}

/// Verifier-owned input-node layout for one fixed public-LogUp circuit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicLogupInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmPublicLogupInputPreprocessed {
    pub fn new(
        reference: &VmPublicLogupCircuit,
        circuit_id: u32,
    ) -> Result<Self, VmPublicLogupInputError> {
        M31Word::try_from(circuit_id)
            .map_err(|_| VmPublicLogupInputError::CircuitIdNotCanonical { circuit_id })?;
        let arena = reference.circuit().arena();
        let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
        let claim_kinds = canonical_vm_public_claim_word_kinds(reference.shape());
        let mut sources = HashSet::with_capacity(reference.input_bindings().len());
        let mut selector_count = 0_usize;
        let mut rows = Vec::with_capacity(reference.input_bindings().len());
        for binding in reference.input_bindings() {
            if !sources.insert(binding.source) {
                return Err(VmPublicLogupInputError::DuplicateInputSource {
                    source: binding.source,
                });
            }
            let node_id = usize::try_from(binding.node_id).map_err(|_| {
                VmPublicLogupInputError::NodeIdDoesNotFitUsize {
                    node_id: binding.node_id,
                }
            })?;
            let node = arena
                .nodes
                .get(node_id)
                .ok_or(VmPublicLogupInputError::NodeMissing {
                    node_id: binding.node_id,
                })?;
            if node.op != Op::Input {
                return Err(VmPublicLogupInputError::BindingTargetsNonInput {
                    node_id: binding.node_id,
                });
            }
            let use_count = uses[node_id];
            M31Word::try_from(use_count).map_err(|_| {
                VmPublicLogupInputError::UseCountNotCanonical {
                    node_id: binding.node_id,
                    use_count,
                }
            })?;
            let (source_index_0, source_index_1) = validate_source(
                binding.source,
                &claim_kinds,
                reference.claimed_sum_count(),
                &mut selector_count,
            )?;
            rows.push(PreprocessedRow {
                source: binding.source,
                circuit_id,
                node_id: binding.node_id,
                use_count,
                source_index_0,
                source_index_1,
            });
        }
        if selector_count != 1 {
            return Err(VmPublicLogupInputError::SelectorCountMismatch {
                actual: selector_count,
            });
        }
        let expected_inputs = expected_input_count(&claim_kinds, reference.claimed_sum_count())?;
        if rows.len() != expected_inputs {
            return Err(VmPublicLogupInputError::InputCountMismatch {
                expected: expected_inputs,
                actual: rows.len(),
            });
        }
        drop(arena);
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmPublicLogupInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicLogupInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn input_count(&self) -> usize {
        self.rows.len()
    }

    pub fn column_ids() -> Vec<PreProcessedColumnId> {
        preprocessed_column_ids()
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = (0..PREPROCESSED_COLUMN_COUNT)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][index] = 1;
            columns[CLAIM_WORD_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmPublicLogupInputSource::ClaimWord { .. }
            ));
            columns[CLAIM_BYTE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmPublicLogupInputSource::ClaimByte { .. }
            ));
            columns[CHALLENGE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmPublicLogupInputSource::RelationChallengeWord { .. }
            ));
            columns[CLAIMED_SUM_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                VmPublicLogupInputSource::ClaimedSumWord { .. }
            ));
            columns[SELECTOR_MASK_COLUMN][index] =
                u32::from(row.source == VmPublicLogupInputSource::SegmentSelector);
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[SOURCE_INDEX_0_COLUMN][index] = row.source_index_0;
            columns[SOURCE_INDEX_1_COLUMN][index] = row.source_index_1;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validate_source(
    source: VmPublicLogupInputSource,
    claim_kinds: &[VmPublicClaimWordKind],
    claimed_sum_count: u32,
    selector_count: &mut usize,
) -> Result<(u32, u32), VmPublicLogupInputError> {
    match source {
        VmPublicLogupInputSource::ClaimWord { index } => {
            require_claim_index(claim_kinds, index)?;
            Ok((index, 0))
        }
        VmPublicLogupInputSource::ClaimByte {
            word_index,
            byte_index,
        } => {
            let index = require_claim_index(claim_kinds, word_index)?;
            if claim_kinds[index] != VmPublicClaimWordKind::U16 {
                return Err(VmPublicLogupInputError::ByteSourceIsNotU16 { word_index });
            }
            if byte_index >= 2 {
                return Err(VmPublicLogupInputError::ByteIndexOutOfRange { byte_index });
            }
            Ok((word_index, byte_index))
        }
        VmPublicLogupInputSource::RelationChallengeWord {
            challenge,
            word_index,
        } => {
            if !matches!(challenge, 0 | 1 | 3) {
                return Err(VmPublicLogupInputError::UnexpectedChallenge { challenge });
            }
            if word_index >= CHALLENGE_WORDS {
                return Err(VmPublicLogupInputError::ChallengeWordOutOfRange { word_index });
            }
            Ok((challenge, word_index))
        }
        VmPublicLogupInputSource::ClaimedSumWord {
            item_index,
            limb_index,
        } => {
            if item_index >= claimed_sum_count {
                return Err(VmPublicLogupInputError::ClaimedSumIndexOutOfRange { item_index });
            }
            if limb_index >= QM31_LIMBS {
                return Err(VmPublicLogupInputError::ClaimedSumLimbOutOfRange { limb_index });
            }
            Ok((item_index, limb_index))
        }
        VmPublicLogupInputSource::SegmentSelector => {
            *selector_count = selector_count
                .checked_add(1)
                .ok_or(VmPublicLogupInputError::RowCountOverflow)?;
            Ok((0, 0))
        }
    }
}

fn require_claim_index(
    claim_kinds: &[VmPublicClaimWordKind],
    index: u32,
) -> Result<usize, VmPublicLogupInputError> {
    let index = usize::try_from(index)
        .map_err(|_| VmPublicLogupInputError::ClaimIndexDoesNotFitUsize { index })?;
    if index >= claim_kinds.len() {
        return Err(VmPublicLogupInputError::ClaimIndexOutOfRange {
            index,
            claim_word_count: claim_kinds.len(),
        });
    }
    Ok(index)
}

fn expected_input_count(
    claim_kinds: &[VmPublicClaimWordKind],
    claimed_sum_count: u32,
) -> Result<usize, VmPublicLogupInputError> {
    let byte_inputs = claim_kinds
        .iter()
        .filter(|kind| **kind == VmPublicClaimWordKind::U16)
        .count()
        .checked_mul(2)
        .ok_or(VmPublicLogupInputError::RowCountOverflow)?;
    let claimed_sum_inputs = usize::try_from(claimed_sum_count)
        .ok()
        .and_then(|count| count.checked_mul(QM31_LIMBS as usize))
        .ok_or(VmPublicLogupInputError::RowCountOverflow)?;
    claim_kinds
        .len()
        .checked_add(byte_inputs)
        .and_then(|count| count.checked_add(3 * CHALLENGE_WORDS as usize))
        .and_then(|count| count.checked_add(claimed_sum_inputs))
        .and_then(|count| count.checked_add(1))
        .ok_or(VmPublicLogupInputError::RowCountOverflow)
}

/// Relations used by the macro-generated public-LogUp input component.
#[derive(Clone)]
pub struct VmPublicLogupInputComponentRelations {
    pub claim_word: super::vm_public_claim_input_air::VmPublicClaimWordRelation,
    pub claim_byte: super::vm_public_claim_input_air::VmPublicClaimByteRelation,
    pub challenge_word: super::relation_challenge_air::RelationChallengeWordRelation,
    pub verifier_input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub wire: crate::relations::WireRelation,
}

impl VmPublicLogupInputComponentRelations {
    /// Combine every source owner with the shared arithmetic wire relation.
    pub fn new(
        claim_relations: &VmPublicClaimInputRelations,
        challenge_relations: &RelationChallengeRelations,
        verifier_input_relations: &VerifierInputRelations,
        circuit_relations: &RecursionRelations,
    ) -> Self {
        Self {
            claim_word: claim_relations.claim_word.clone(),
            claim_byte: claim_relations.claim_byte.clone(),
            challenge_word: challenge_relations.word.clone(),
            verifier_input_word: verifier_input_relations.input_word.clone(),
            wire: circuit_relations.wire.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations:
        crate::vm_public_logup_input_air::VmPublicLogupInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_public_logup_input_row_mask",
        claim_word_mask: "recursion_vm_public_logup_input_claim_word_mask",
        claim_byte_mask: "recursion_vm_public_logup_input_claim_byte_mask",
        challenge_mask: "recursion_vm_public_logup_input_challenge_mask",
        claimed_sum_mask: "recursion_vm_public_logup_input_claimed_sum_mask",
        selector_mask: "recursion_vm_public_logup_input_selector_mask",
        circuit_id: "recursion_vm_public_logup_input_circuit_id",
        node_id: "recursion_vm_public_logup_input_node_id",
        use_count: "recursion_vm_public_logup_input_use_count",
        source_index_0: "recursion_vm_public_logup_input_source_index_0",
        source_index_1: "recursion_vm_public_logup_input_source_index_1",
    },
    embedded_params: [
        segment_active, claim_scope, verifier_id, challenge_scope, claimed_sum_kind,
    ],

    relation claim_word(3);
    relation claim_byte(3);
    relation challenge_word(5);
    relation verifier_input_word(5);
    relation wire(6);

    fn vm_public_logup_input(
        value,
        row_mask, claim_word_mask, claim_byte_mask, challenge_mask,
        claimed_sum_mask, selector_mask, circuit_id, node_id, use_count,
        source_index_0, source_index_1,
        segment_active, claim_scope, verifier_id, challenge_scope, claimed_sum_kind,
    ) {
        let witness_mask = row_mask - selector_mask;

        constrain enabler - row_mask;
        constrain witness_mask * (1 - segment_active) * value;
        constrain selector_mask * (value - segment_active);

        consume(segment_active * claim_word_mask) claim_word(
            claim_scope, source_index_0, value,
        );
        consume(segment_active * claim_byte_mask) claim_byte(
            source_index_0, source_index_1, value,
        );
        consume(segment_active * challenge_mask) challenge_word(
            verifier_id, challenge_scope, source_index_0, source_index_1, value,
        );
        consume(segment_active * claimed_sum_mask) verifier_input_word(
            verifier_id, claimed_sum_kind, source_index_0, source_index_1, value,
        );
        emit(row_mask * use_count) wire(circuit_id, node_id, value, 0, 0, 0);

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for the selected universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    claim_relations: &VmPublicClaimInputRelations,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    circuit_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        claim_scope: BaseField::from(VM_PUBLIC_LOGUP_SCOPE),
        verifier_id: BaseField::from(SEGMENT_VERIFIER_ID),
        challenge_scope: BaseField::from(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
        claimed_sum_kind: BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        relations: VmPublicLogupInputComponentRelations::new(
            claim_relations,
            challenge_relations,
            verifier_input_relations,
            circuit_relations,
        ),
    }
}

/// Generate source consumers and exact circuit-wire producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    claim_relations: &VmPublicClaimInputRelations,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    circuit_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(VM_PUBLIC_LOGUP_SCOPE),
        BaseField::from(SEGMENT_VERIFIER_ID),
        BaseField::from(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
        BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        &VmPublicLogupInputComponentRelations::new(
            claim_relations,
            challenge_relations,
            verifier_input_relations,
            circuit_relations,
        ),
    )
}

/// Materializes input values after proving that witness structure is canonical.
pub fn push_vm_public_logup_inputs(
    table: &mut VmPublicLogupInputTable,
    preprocessed: &VmPublicLogupInputPreprocessed,
    reference: &VmPublicLogupCircuit,
    witness: &VmPublicLogupCircuit,
    proof_kind: ProofKind,
) -> Result<(), VmPublicLogupInputError> {
    if reference.shape() != witness.shape()
        || reference.claimed_sum_count() != witness.claimed_sum_count()
        || reference.input_bindings() != witness.input_bindings()
    {
        return Err(VmPublicLogupInputError::InputLayoutMismatch);
    }
    if witness.input_bindings().len() != preprocessed.rows.len() {
        return Err(VmPublicLogupInputError::InputCountMismatch {
            expected: preprocessed.rows.len(),
            actual: witness.input_bindings().len(),
        });
    }
    let arena = witness.circuit().arena();
    let active = proof_kind == ProofKind::SegmentLeaf;
    for (row, binding) in preprocessed.rows.iter().zip(witness.input_bindings()) {
        if row.node_id != binding.node_id || row.source != binding.source {
            return Err(VmPublicLogupInputError::InputCoordinateMismatch {
                node_id: binding.node_id,
            });
        }
        let node_id = usize::try_from(binding.node_id).map_err(|_| {
            VmPublicLogupInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?;
        let node = arena
            .nodes
            .get(node_id)
            .ok_or(VmPublicLogupInputError::NodeMissing {
                node_id: binding.node_id,
            })?;
        if node.op != Op::Input {
            return Err(VmPublicLogupInputError::BindingTargetsNonInput {
                node_id: binding.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(VmPublicLogupInputError::InputIsNotBaseField {
                node_id: binding.node_id,
            });
        }
        let expected = if binding.source == VmPublicLogupInputSource::SegmentSelector {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(VmPublicLogupInputError::InactiveInputIsNonZero {
                node_id: binding.node_id,
            });
        }
        table.push(expected);
    }
    Ok(())
}

/// Invalid public-LogUp input layout or witness value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicLogupInputError {
    CircuitIdNotCanonical {
        circuit_id: u32,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    NodeIdDoesNotFitUsize {
        node_id: u32,
    },
    NodeMissing {
        node_id: u32,
    },
    BindingTargetsNonInput {
        node_id: u32,
    },
    UseCountNotCanonical {
        node_id: u32,
        use_count: u32,
    },
    DuplicateInputSource {
        source: VmPublicLogupInputSource,
    },
    ClaimIndexDoesNotFitUsize {
        index: u32,
    },
    ClaimIndexOutOfRange {
        index: usize,
        claim_word_count: usize,
    },
    ByteSourceIsNotU16 {
        word_index: u32,
    },
    ByteIndexOutOfRange {
        byte_index: u32,
    },
    UnexpectedChallenge {
        challenge: u32,
    },
    ChallengeWordOutOfRange {
        word_index: u32,
    },
    ClaimedSumIndexOutOfRange {
        item_index: u32,
    },
    ClaimedSumLimbOutOfRange {
        limb_index: u32,
    },
    SelectorCountMismatch {
        actual: usize,
    },
    InputCountMismatch {
        expected: usize,
        actual: usize,
    },
    InputLayoutMismatch,
    InputCoordinateMismatch {
        node_id: u32,
    },
    InputIsNotBaseField {
        node_id: u32,
    },
    InactiveInputIsNonZero {
        node_id: u32,
    },
}

impl fmt::Display for VmPublicLogupInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicLogupInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use prover::relations::Relations;
    use rstest::rstest;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::vm_public_claim::{canonical_vm_public_claim_words, tests as claim_tests};
    use crate::vm_public_logup_circuit::{
        VmPublicLogupChallengeWords, VmPublicLogupWitness, build_vm_public_logup_circuit,
        build_vm_public_logup_reference,
    };

    const CIRCUIT_ID: u32 = 37;

    fn circuits(kind: ProofKind) -> (VmPublicLogupCircuit, VmPublicLogupCircuit) {
        let shape = claim_tests::shape();
        let reference =
            build_vm_public_logup_reference(shape, 1).expect("fixture reference is representable");
        let active = kind == ProofKind::SegmentLeaf;
        let claim = if active {
            canonical_vm_public_claim_words(&claim_tests::public_data(), shape)
                .expect("fixture claim is canonical")
        } else {
            vec![M31Word::ZERO; shape.claim_word_count()]
        };
        let mut channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut channel);
        let challenges = if active {
            VmPublicLogupChallengeWords::from_relations(&relations)
        } else {
            VmPublicLogupChallengeWords::new(
                [M31Word::ZERO; CHALLENGE_WORDS as usize],
                [M31Word::ZERO; CHALLENGE_WORDS as usize],
                [M31Word::ZERO; CHALLENGE_WORDS as usize],
            )
        };
        let claimed_sums = if active {
            vec![-claim_tests::public_data().logup_sum(&relations)]
        } else {
            vec![SecureField::zero()]
        };
        let witness = build_vm_public_logup_circuit(
            shape,
            1,
            VmPublicLogupWitness {
                segment_selector: active,
                claim_words: &claim,
                relation_challenges: challenges,
                claimed_sums: &claimed_sums,
            },
        )
        .expect("fixture circuit has safe selected denominators");
        (reference, witness)
    }

    fn assert_constraints(kind: ProofKind) {
        let (reference, witness) = circuits(kind);
        let preprocessing = VmPublicLogupInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("fixture input layout is canonical");
        let mut table = VmPublicLogupInputTable::new();
        push_vm_public_logup_inputs(&mut table, &preprocessing, &reference, &witness, kind)
            .expect("fixture input values match their mode");
        let claim_relations = VmPublicClaimInputRelations::dummy();
        let challenge_relations = RelationChallengeRelations::dummy();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &claim_relations,
            &challenge_relations,
            &verifier_input_relations,
            &circuit_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &claim_relations,
            &challenge_relations,
            &verifier_input_relations,
            &circuit_relations,
        );
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_public_logup_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[rstest]
    fn preprocessing_covers_every_circuit_input_exactly_once() {
        let (reference, _) = circuits(ProofKind::SegmentLeaf);
        let preprocessing = VmPublicLogupInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("fixture input layout is canonical");
        assert_eq!(
            preprocessing.input_count(),
            reference.input_bindings().len()
        );
    }
}
