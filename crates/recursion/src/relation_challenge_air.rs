//! Scoped ownership for relation challenges drawn by current protocol verifier transcripts.
//!
//! Each trusted relation-challenge operation consumes its complete eight-word
//! transcript draw atomically. The same words are then copied into distinct
//! verifier-owned scopes for public LogUp arithmetic and AIR evaluation, so a
//! downstream circuit cannot reuse one scope twice or exchange child lanes.

use core::fmt;

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::relation;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::transcript::RecordingTranscriptBackend;
use super::transcript_binding_air::UniversalTranscriptWitness;
use super::transcript_program::VerifierTranscriptExecution;
use super::transcript_state_air::TranscriptStateRelations;
use super::wire::ProofKind;

/// Relation-challenge words reserved for VM public LogUp arithmetic.
pub const VM_PUBLIC_LOGUP_CHALLENGE_SCOPE: u32 = 0;
/// Relation-challenge words reserved for inner AIR evaluation.
pub const AIR_EVALUATION_CHALLENGE_SCOPE: u32 = 1;

const RATE: usize = 8;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const PUBLIC_LOGUP_MASK_COLUMN: usize = 3;
const VERIFIER_ID_COLUMN: usize = 4;
const SEQUENCE_COLUMN: usize = 5;
const TAG_COLUMN: usize = 6;
const ARG_0_COLUMN: usize = 7;
const ARG_1_COLUMN: usize = 8;
const ARG_2_COLUMN: usize = 9;
const ARG_3_COLUMN: usize = 10;
const CHALLENGE_COLUMN: usize = 11;
const PREPROCESSED_COLUMN_COUNT: usize = 12;

// Scoped word: verifier, consumer scope, challenge, word index, and value.
relation!(RelationChallengeWordRelation, 5);

/// Downstream ownership relation for every relation-challenge word.
#[derive(Clone)]
pub struct RelationChallengeRelations {
    pub word: RelationChallengeWordRelation,
}

impl RelationChallengeRelations {
    pub fn dummy() -> Self {
        Self {
            word: RelationChallengeWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            word: RelationChallengeWordRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    public_logup_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
    challenge: u32,
}

/// Trusted relation-challenge operations for all three verifier lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationChallengePreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_challenge_count: u32,
    recursion_challenge_count: u32,
}

impl RelationChallengePreprocessed {
    pub fn new(
        vm: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> Result<Self, RelationChallengeError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(RelationChallengeError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm.schema(),
            });
        }
        if recursion.schema() != VerifierSchema::Recursion {
            return Err(RelationChallengeError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion.schema(),
            });
        }

        let mut rows = Vec::new();
        let vm_challenge_count = append_plan_rows(&mut rows, vm, SEGMENT_VERIFIER_ID, 1, 0)?;
        let recursion_challenge_count =
            append_plan_rows(&mut rows, recursion, LEFT_RECURSION_VERIFIER_ID, 0, 1)?;
        append_plan_rows(&mut rows, recursion, RIGHT_RECURSION_VERIFIER_ID, 0, 1)?;

        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(RelationChallengeError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(RelationChallengeError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            vm_challenge_count,
            recursion_challenge_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn vm_challenge_count(&self) -> u32 {
        self.vm_challenge_count
    }

    pub const fn recursion_challenge_count(&self) -> u32 {
        self.recursion_challenge_count
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
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[PUBLIC_LOGUP_MASK_COLUMN][index] = row.public_logup_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
            columns[CHALLENGE_COLUMN][index] = row.challenge;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_plan_rows(
    rows: &mut Vec<PreprocessedRow>,
    plan: &VerifierControlPlan,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<u32, RelationChallengeError> {
    let mut expected_challenge = 0_u32;
    for (sequence, step) in plan.steps().iter().copied().enumerate() {
        let VerifierStep::DrawRelationChallenge { challenge } = step else {
            continue;
        };
        if challenge != expected_challenge {
            return Err(RelationChallengeError::NonCanonicalChallengeIndex {
                expected: expected_challenge,
                actual: challenge,
            });
        }
        let sequence = u32::try_from(sequence)
            .map_err(|_| RelationChallengeError::SequenceOutOfRange { sequence })?;
        let encoded = step.encode();
        rows.push(PreprocessedRow {
            segment_mask,
            binary_mask,
            public_logup_mask: u32::from(
                plan.schema() == VerifierSchema::Vm && matches!(challenge, 0 | 1 | 3),
            ),
            verifier_id,
            sequence,
            tag: encoded.tag(),
            args: encoded.args(),
            challenge,
        });
        expected_challenge = expected_challenge
            .checked_add(1)
            .ok_or(RelationChallengeError::ChallengeCountOverflow)?;
    }
    if expected_challenge == 0 {
        return Err(RelationChallengeError::RelationChallengesMissing {
            schema: plan.schema(),
        });
    }
    Ok(expected_challenge)
}

/// Relation instances used by the macro-generated challenge component.
#[derive(Clone)]
pub struct RelationChallengeComponentRelations {
    pub draw_output: super::transcript_state_air::TranscriptDrawOutputRelation,
    pub word: RelationChallengeWordRelation,
}

impl RelationChallengeComponentRelations {
    /// Combine transcript-draw and scoped challenge relation instances.
    pub fn new(
        transcript_relations: &TranscriptStateRelations,
        challenge_relations: &RelationChallengeRelations,
    ) -> Self {
        Self {
            draw_output: transcript_relations.draw_output.clone(),
            word: challenge_relations.word.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations:
        crate::relation_challenge_air::RelationChallengeComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_relation_challenge_row_mask",
        segment_mask: "recursion_relation_challenge_segment_mask",
        binary_mask: "recursion_relation_challenge_binary_mask",
        public_logup_mask: "recursion_relation_challenge_public_logup_mask",
        verifier_id: "recursion_relation_challenge_verifier_id",
        sequence: "recursion_relation_challenge_sequence",
        tag: "recursion_relation_challenge_tag",
        arg_0: "recursion_relation_challenge_arg_0",
        arg_1: "recursion_relation_challenge_arg_1",
        arg_2: "recursion_relation_challenge_arg_2",
        arg_3: "recursion_relation_challenge_arg_3",
        challenge: "recursion_relation_challenge_index",
    },
    embedded_params: [segment_active, binary_active, air_scope, public_scope],

    relation draw_output(15);
    relation word(5);

    fn relation_challenge(
        output_0, output_1, output_2, output_3,
        output_4, output_5, output_6, output_7,
        row_mask, segment_mask, binary_mask, public_logup_mask,
        verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3, challenge,
        segment_active, binary_active, air_scope, public_scope,
    ) {
        let mode_active =
            row_mask * (segment_mask * segment_active + binary_mask * binary_active);
        let inactive = 1 - enabler;

        constrain enabler - mode_active;
        constrain inactive * output_0;
        constrain inactive * output_1;
        constrain inactive * output_2;
        constrain inactive * output_3;
        constrain inactive * output_4;
        constrain inactive * output_5;
        constrain inactive * output_6;
        constrain inactive * output_7;

        consume(enabler) draw_output(
            verifier_id, sequence, tag, arg_0, arg_1, arg_2, arg_3,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 0, output_0);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 0, output_0,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 1, output_1);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 1, output_1,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 2, output_2);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 2, output_2,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 3, output_3);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 3, output_3,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 4, output_4);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 4, output_4,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 5, output_5);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 5, output_5,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 6, output_6);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 6, output_6,
        );
        emit(enabler) word(verifier_id, air_scope, challenge, 7, output_7);
        emit(enabler * public_logup_mask) word(
            verifier_id, public_scope, challenge, 7, output_7,
        );

        return output_0;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator with verifier-owned mode and scope values.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    transcript_relations: &TranscriptStateRelations,
    challenge_relations: &RelationChallengeRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        air_scope: BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        public_scope: BaseField::from(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
        relations: RelationChallengeComponentRelations::new(
            transcript_relations,
            challenge_relations,
        ),
    }
}

/// Generate transcript-draw consumers and scoped word producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    transcript_relations: &TranscriptStateRelations,
    challenge_relations: &RelationChallengeRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        BaseField::from(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
        &RelationChallengeComponentRelations::new(transcript_relations, challenge_relations),
    )
}

/// Materializes the trusted relation-challenge draws for the selected lanes.
pub fn push_relation_challenges(
    table: &mut RelationChallengeTable,
    preprocessed: &RelationChallengePreprocessed,
    witness: UniversalTranscriptWitness<'_>,
) -> Result<(), RelationChallengeError> {
    let (segment, left, right) = match witness {
        UniversalTranscriptWitness::Segment(execution) => (Some(execution), None, None),
        UniversalTranscriptWitness::Binary { left, right } => (None, Some(left), Some(right)),
        UniversalTranscriptWitness::Empty => (None, None, None),
    };
    for row in &preprocessed.rows {
        let execution = match row.verifier_id {
            SEGMENT_VERIFIER_ID => segment,
            LEFT_RECURSION_VERIFIER_ID => left,
            RIGHT_RECURSION_VERIFIER_ID => right,
            verifier_id => return Err(RelationChallengeError::UnknownVerifierId { verifier_id }),
        };
        let values = if let Some(execution) = execution {
            challenge_draw(execution, row)?.map(M31Word::as_u32)
        } else {
            [0; RATE]
        };
        table.push_row_values(execution.is_some(), values);
    }
    Ok(())
}

fn challenge_draw(
    execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
    row: &PreprocessedRow,
) -> Result<[M31Word; RATE], RelationChallengeError> {
    let operation = execution
        .operations()
        .iter()
        .find(|operation| operation.sequence() == row.sequence)
        .ok_or(RelationChallengeError::OperationMissing {
            verifier_id: row.verifier_id,
            sequence: row.sequence,
        })?;
    let expected = VerifierStep::DrawRelationChallenge {
        challenge: row.challenge,
    };
    if operation.step() != expected {
        return Err(RelationChallengeError::OperationMismatch {
            verifier_id: row.verifier_id,
            sequence: row.sequence,
            expected,
            actual: operation.step(),
        });
    }
    operation.draw().ok_or(RelationChallengeError::DrawMissing {
        verifier_id: row.verifier_id,
        sequence: row.sequence,
    })
}

impl RelationChallengeTable {
    fn push_row_values(&mut self, active: bool, values: [u32; RATE]) {
        self.push_row(&[
            u32::from(active),
            values[0],
            values[1],
            values[2],
            values[3],
            values[4],
            values[5],
            values[6],
            values[7],
        ]);
    }
}

/// Invalid trusted challenge layout or transcript witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RelationChallengeError {
    SchemaMismatch {
        lane: &'static str,
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    SequenceOutOfRange {
        sequence: usize,
    },
    NonCanonicalChallengeIndex {
        expected: u32,
        actual: u32,
    },
    ChallengeCountOverflow,
    RelationChallengesMissing {
        schema: VerifierSchema,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    OperationMissing {
        verifier_id: u32,
        sequence: u32,
    },
    OperationMismatch {
        verifier_id: u32,
        sequence: u32,
        expected: VerifierStep,
        actual: VerifierStep,
    },
    DrawMissing {
        verifier_id: u32,
        sequence: u32,
    },
}

impl fmt::Display for RelationChallengeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for RelationChallengeError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::transcript_program::tests::{plan_for_schema, recording_execution_for};

    fn plans() -> (VerifierControlPlan, VerifierControlPlan) {
        (
            plan_for_schema(VerifierSchema::Vm, 1),
            plan_for_schema(VerifierSchema::Recursion, 1),
        )
    }

    fn assert_constraints(kind: ProofKind, tamper_inactive: bool) {
        let (vm, recursion) = plans();
        let preprocessing = RelationChallengePreprocessed::new(&vm, &recursion)
            .expect("fixture plans have canonical relation draws");
        let segment = recording_execution_for(&vm, 1);
        let left = recording_execution_for(&recursion, 1);
        let right = recording_execution_for(&recursion, 2);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTranscriptWitness::Segment(&segment),
            ProofKind::BinaryNode => UniversalTranscriptWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalTranscriptWitness::Empty,
        };
        let mut table = RelationChallengeTable::new();
        push_relation_challenges(&mut table, &preprocessing, witness)
            .expect("fixture challenge draws materialize");
        if tamper_inactive {
            table.output_0[0] = 1;
        }
        let transcript_relations = TranscriptStateRelations::dummy();
        let challenge_relations = RelationChallengeRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &transcript_relations,
            &challenge_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &transcript_relations,
            &challenge_relations,
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

    fn bridge_sum(swap_verifier: bool) -> QM31 {
        let (vm, recursion) = plans();
        let preprocessing = RelationChallengePreprocessed::new(&vm, &recursion)
            .expect("fixture plans have canonical relation draws");
        let execution = recording_execution_for(&vm, 1);
        let mut table = RelationChallengeTable::new();
        push_relation_challenges(
            &mut table,
            &preprocessing,
            UniversalTranscriptWitness::Segment(&execution),
        )
        .expect("fixture challenge draws materialize");

        let mut channel = Poseidon2M31Channel::default();
        let transcript_relations = TranscriptStateRelations::draw(&mut channel);
        let challenge_relations = RelationChallengeRelations::draw(&mut channel);
        let (_, component_sum) = gen_interaction_trace(
            &table.into_witness(),
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &transcript_relations,
            &challenge_relations,
        );
        component_sum
            + transcript_source_terms(&preprocessing, &execution, &transcript_relations)
            + challenge_consumer_terms(
                &preprocessing,
                &execution,
                &challenge_relations,
                swap_verifier,
            )
    }

    fn transcript_source_terms(
        preprocessing: &RelationChallengePreprocessed,
        execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
        relations: &TranscriptStateRelations,
    ) -> QM31 {
        preprocessing
            .rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let draw =
                    challenge_draw(execution, row).expect("fixture operation has a relation draw");
                let mut tuple = vec![
                    M31::from(row.verifier_id),
                    M31::from(row.sequence),
                    M31::from(row.tag),
                    M31::from(row.args[0]),
                    M31::from(row.args[1]),
                    M31::from(row.args[2]),
                    M31::from(row.args[3]),
                ];
                tuple.extend(draw.map(|word| M31::from(word.as_u32())));
                let denominator: QM31 = relations.draw_output.combine(&tuple);
                sum + denominator.inverse()
            })
    }

    fn challenge_consumer_terms(
        preprocessing: &RelationChallengePreprocessed,
        execution: &VerifierTranscriptExecution<RecordingTranscriptBackend>,
        relations: &RelationChallengeRelations,
        swap_verifier: bool,
    ) -> QM31 {
        preprocessing
            .rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let draw =
                    challenge_draw(execution, row).expect("fixture operation has a relation draw");
                let verifier_id = if swap_verifier {
                    LEFT_RECURSION_VERIFIER_ID
                } else {
                    row.verifier_id
                };
                let scopes = if row.public_logup_mask == 1 {
                    [
                        Some(AIR_EVALUATION_CHALLENGE_SCOPE),
                        Some(VM_PUBLIC_LOGUP_CHALLENGE_SCOPE),
                    ]
                } else {
                    [Some(AIR_EVALUATION_CHALLENGE_SCOPE), None]
                };
                scopes
                    .into_iter()
                    .flatten()
                    .flat_map(|scope| {
                        draw.into_iter().enumerate().map(move |(word_index, word)| {
                            let denominator: QM31 = relations.word.combine(&[
                                M31::from(verifier_id),
                                M31::from(scope),
                                M31::from(row.challenge),
                                M31::from(
                                    u32::try_from(word_index)
                                        .expect("challenge word index fits u32"),
                                ),
                                M31::from(word.as_u32()),
                            ]);
                            -denominator.inverse()
                        })
                    })
                    .fold(sum, |sum, term| sum + term)
            })
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_relation_challenge_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, false);
    }

    #[rstest]
    #[should_panic]
    fn inactive_relation_challenge_words_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, true);
    }

    #[rstest]
    fn transcript_draws_close_into_both_challenge_scopes() {
        assert!(bridge_sum(false).is_zero());
    }

    #[rstest]
    fn segment_challenges_cannot_move_to_a_recursion_lane() {
        assert!(!bridge_sum(true).is_zero());
    }
}
