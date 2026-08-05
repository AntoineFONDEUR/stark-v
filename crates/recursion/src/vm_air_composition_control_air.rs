//! Control-step consumer for universal AIR composition verification.
//!
//! Verifier preprocessing extracts the contiguous AIR-evaluation slice and its
//! immediately following composition assertion from the trusted VM and
//! recursion plans. Fixed circuit profiles supply both trusted counts, so proof
//! values cannot shorten either AIR program or change a sampled-value boundary.
//! Segment mode activates the VM lane, binary mode activates both recursion
//! lanes, and empty mode activates none.

use core::fmt;

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

use super::control_air::ControlRelations;
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::vm_air_composition_circuit::VmAirCompositionProfile;
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const VERIFIER_ID_COLUMN: usize = 2;
const SEQUENCE_COLUMN: usize = 3;
const TAG_COLUMN: usize = 4;
const ARG_0_COLUMN: usize = 5;
const ARG_1_COLUMN: usize = 6;
const ARG_2_COLUMN: usize = 7;
const ARG_3_COLUMN: usize = 8;
const PREPROCESSED_COLUMN_COUNT: usize = 9;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    verifier_id: u32,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
}

/// Trusted universal AIR-composition control rows for fixed circuit profiles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmAirCompositionControlPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_air_instruction_count: u32,
    vm_sampled_value_count: u32,
    recursion_air_instruction_count: u32,
    recursion_sampled_value_count: u32,
}

impl VmAirCompositionControlPreprocessed {
    pub fn new(
        vm_plan: &VerifierControlPlan,
        vm_profile: VmAirCompositionProfile,
        recursion_plan: &VerifierControlPlan,
        recursion_air_instruction_count: u32,
        recursion_sampled_value_count: u32,
    ) -> Result<Self, VmAirCompositionControlError> {
        if vm_plan.schema() != VerifierSchema::Vm {
            return Err(VmAirCompositionControlError::SchemaMismatch {
                lane: "segment",
                expected: VerifierSchema::Vm,
                actual: vm_plan.schema(),
            });
        }
        if recursion_plan.schema() != VerifierSchema::Recursion {
            return Err(VmAirCompositionControlError::SchemaMismatch {
                lane: "binary",
                expected: VerifierSchema::Recursion,
                actual: recursion_plan.schema(),
            });
        }
        let mut rows = validated_rows(
            vm_plan.steps(),
            vm_profile.air_instruction_count(),
            vm_profile.sampled_value_count(),
            super::control_air::SEGMENT_VERIFIER_ID,
        )?;
        rows.extend(validated_rows(
            recursion_plan.steps(),
            recursion_air_instruction_count,
            recursion_sampled_value_count,
            super::control_air::LEFT_RECURSION_VERIFIER_ID,
        )?);
        rows.extend(validated_rows(
            recursion_plan.steps(),
            recursion_air_instruction_count,
            recursion_sampled_value_count,
            super::control_air::RIGHT_RECURSION_VERIFIER_ID,
        )?);
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmAirCompositionControlError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmAirCompositionControlError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            vm_air_instruction_count: vm_profile.air_instruction_count(),
            vm_sampled_value_count: vm_profile.sampled_value_count(),
            recursion_air_instruction_count,
            recursion_sampled_value_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub const fn vm_air_instruction_count(&self) -> u32 {
        self.vm_air_instruction_count
    }

    pub const fn vm_sampled_value_count(&self) -> u32 {
        self.vm_sampled_value_count
    }

    pub const fn recursion_air_instruction_count(&self) -> u32 {
        self.recursion_air_instruction_count
    }

    pub const fn recursion_sampled_value_count(&self) -> u32 {
        self.recursion_sampled_value_count
    }

    pub fn row_count(&self) -> usize {
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
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validated_rows(
    steps: &[VerifierStep],
    air_instruction_count: u32,
    sampled_value_count: u32,
    verifier_id: u32,
) -> Result<Vec<PreprocessedRow>, VmAirCompositionControlError> {
    let mut rows = Vec::new();
    let mut expected_instruction = 0_u32;
    let mut previous_instruction_sequence = None;
    let mut assertion_sequence = None;
    for (sequence, step) in steps.iter().copied().enumerate() {
        match step {
            VerifierStep::EvaluateAirInstruction { instruction } => {
                if assertion_sequence.is_some() {
                    return Err(
                        VmAirCompositionControlError::InstructionAfterCompositionAssertion {
                            instruction,
                        },
                    );
                }
                if instruction != expected_instruction {
                    return Err(VmAirCompositionControlError::NonCanonicalInstructionIndex {
                        expected: expected_instruction,
                        actual: instruction,
                    });
                }
                if let Some(previous) = previous_instruction_sequence {
                    if sequence != previous + 1 {
                        return Err(VmAirCompositionControlError::NonContiguousInstruction {
                            previous,
                            actual: sequence,
                        });
                    }
                }
                rows.push(encoded_row(sequence, step, verifier_id)?);
                previous_instruction_sequence = Some(sequence);
                expected_instruction = expected_instruction
                    .checked_add(1)
                    .ok_or(VmAirCompositionControlError::InstructionCountOverflow)?;
            }
            VerifierStep::AssertComposition {
                sampled_value_count: actual_sampled_value_count,
            } => {
                if assertion_sequence.is_some() {
                    return Err(VmAirCompositionControlError::DuplicateCompositionAssertion);
                }
                if expected_instruction != air_instruction_count {
                    return Err(VmAirCompositionControlError::InstructionCountMismatch {
                        expected: air_instruction_count,
                        actual: expected_instruction,
                    });
                }
                if actual_sampled_value_count != sampled_value_count {
                    return Err(VmAirCompositionControlError::SampledValueCountMismatch {
                        expected: sampled_value_count,
                        actual: actual_sampled_value_count,
                    });
                }
                if let Some(previous) = previous_instruction_sequence {
                    if sequence != previous + 1 {
                        return Err(
                            VmAirCompositionControlError::CompositionAssertionNotAdjacent {
                                previous,
                                actual: sequence,
                            },
                        );
                    }
                }
                rows.push(encoded_row(sequence, step, verifier_id)?);
                assertion_sequence = Some(sequence);
            }
            _ => {}
        }
    }
    if expected_instruction != air_instruction_count {
        return Err(VmAirCompositionControlError::InstructionCountMismatch {
            expected: air_instruction_count,
            actual: expected_instruction,
        });
    }
    if assertion_sequence.is_none() {
        return Err(VmAirCompositionControlError::CompositionAssertionMissing);
    }
    Ok(rows)
}

fn encoded_row(
    sequence: usize,
    step: VerifierStep,
    verifier_id: u32,
) -> Result<PreprocessedRow, VmAirCompositionControlError> {
    let sequence = u32::try_from(sequence)
        .map_err(|_| VmAirCompositionControlError::SequenceOutOfRange { sequence })?;
    let encoded = step.encode();
    Ok(PreprocessedRow {
        segment_mask: u32::from(verifier_id == super::control_air::SEGMENT_VERIFIER_ID),
        verifier_id,
        sequence,
        tag: encoded.tag(),
        args: encoded.args(),
    })
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_relations: crate::control_air::ControlRelations,
    embedded_preprocessed: {
        row_mask: "recursion_vm_air_composition_control_row_mask",
        segment_mask: "recursion_vm_air_composition_control_segment_mask",
        verifier_id: "recursion_vm_air_composition_control_verifier_id",
        sequence: "recursion_vm_air_composition_control_sequence",
        tag: "recursion_vm_air_composition_control_tag",
        arg_0: "recursion_vm_air_composition_control_arg_0",
        arg_1: "recursion_vm_air_composition_control_arg_1",
        arg_2: "recursion_vm_air_composition_control_arg_2",
        arg_3: "recursion_vm_air_composition_control_arg_3",
    },
    embedded_params: [segment_active, binary_active],

    relation step(7);

    fn vm_air_composition_control(
        row_mask,
        segment_mask,
        verifier_id,
        sequence,
        tag,
        arg_0,
        arg_1,
        arg_2,
        arg_3,
        segment_active,
        binary_active,
    ) {
        let binary_mask = 1 - segment_mask;
        let active = row_mask
            * (segment_mask * segment_active + binary_mask * binary_active);
        consume(active) step(
            verifier_id,
            sequence,
            tag,
            arg_0,
            arg_1,
            arg_2,
            arg_3,
        );
        return sequence;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated consumer with verifier-owned proof-kind selectors.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    control_relations: ControlRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: control_relations,
    }
}

/// Generates the negative control-step fractions for the active verifier lanes.
pub fn gen_interaction_trace(
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        control_relations,
    )
}

/// Invalid VM AIR-composition control slice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmAirCompositionControlError {
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
    NonCanonicalInstructionIndex {
        expected: u32,
        actual: u32,
    },
    NonContiguousInstruction {
        previous: usize,
        actual: usize,
    },
    InstructionCountOverflow,
    InstructionCountMismatch {
        expected: u32,
        actual: u32,
    },
    InstructionAfterCompositionAssertion {
        instruction: u32,
    },
    DuplicateCompositionAssertion,
    CompositionAssertionNotAdjacent {
        previous: usize,
        actual: usize,
    },
    CompositionAssertionMissing,
    SampledValueCountMismatch {
        expected: u32,
        actual: u32,
    },
}

impl fmt::Display for VmAirCompositionControlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirCompositionControlError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::components::COMPONENT_NAMES;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::control_air::SEGMENT_VERIFIER_ID;
    use crate::kernel::VerifierProgramSpec;
    use crate::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};
    use crate::vm_air_composition_circuit::build_vm_air_composition_reference;
    use crate::vm_air_program::VM_AIR_COMPONENT_COUNT;

    fn word(value: u32) -> air::digest::M31Word {
        air::digest::M31Word::try_from(value).expect("fixture value is canonical")
    }

    fn component_log_sizes() -> [u32; VM_AIR_COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    fn profile() -> VmAirCompositionProfile {
        build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture composition profile is valid")
            .profile()
    }

    fn plan(schema: VerifierSchema, profile: VmAirCompositionProfile) -> VerifierControlPlan {
        let pcs = PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(9),
            fri_log_last_layer_degree_bound: air::digest::M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        };
        let shape = FixedProofShape {
            claimed_sum_count: word(profile.claimed_sum_count()),
            sampled_value_count: word(profile.sampled_value_count()),
            queried_value_count: word(36),
            trace_path_count: word(36),
            raw_query_count: word(9),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8); 4],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        };
        let spec = VerifierProgramSpec::new(
            schema,
            profile.relation_challenge_count(),
            5,
            profile.air_instruction_count(),
            3,
        )
        .expect("fixture verifier program has every phase");
        VerifierControlPlan::new(spec, pcs, &shape).expect("fixture shape matches its PCS profile")
    }

    fn preprocessing() -> VmAirCompositionControlPreprocessed {
        let profile = profile();
        VmAirCompositionControlPreprocessed::new(
            &plan(VerifierSchema::Vm, profile),
            profile,
            &plan(VerifierSchema::Recursion, profile),
            profile.air_instruction_count(),
            profile.sampled_value_count(),
        )
        .expect("fixture composition control slices are exact")
    }

    fn assert_constraints(kind: ProofKind) {
        let preprocessing = preprocessing();
        let control_relations = ControlRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let (interaction, claimed_sum) =
            gen_interaction_trace(&preprocessed, kind, &control_relations);
        let traces = TreeVec::new(vec![preprocessed, vec![], interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(preprocessing.log_size(), kind, control_relations);
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn bridge_sum(kind: ProofKind) -> QM31 {
        let preprocessing = preprocessing();
        let mut channel = Poseidon2M31Channel::default();
        let relations = ControlRelations::draw(&mut channel);
        let (_, consumer_sum) =
            gen_interaction_trace(&preprocessing.gen_columns(), kind, &relations);
        preprocessing
            .rows
            .iter()
            .filter(|row| match kind {
                ProofKind::SegmentLeaf => row.verifier_id == SEGMENT_VERIFIER_ID,
                ProofKind::BinaryNode => row.verifier_id != SEGMENT_VERIFIER_ID,
                ProofKind::EmptyLeaf => false,
            })
            .fold(consumer_sum, |sum, row| {
                let denominator: QM31 = relations.step.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(row.sequence),
                    M31::from(row.tag),
                    M31::from(row.args[0]),
                    M31::from(row.args[1]),
                    M31::from(row.args[2]),
                    M31::from(row.args[3]),
                ]);
                sum + denominator.inverse()
            })
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_air_control_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn air_control_steps_close_exactly(#[case] kind: ProofKind) {
        assert!(bridge_sum(kind).is_zero());
    }

    #[test]
    fn sampled_value_count_drift_is_rejected() {
        let profile = profile();
        assert_eq!(
            validated_rows(
                &[
                    VerifierStep::EvaluateAirInstruction { instruction: 0 },
                    VerifierStep::AssertComposition {
                        sampled_value_count: profile.sampled_value_count() + 1,
                    },
                ],
                1,
                profile.sampled_value_count(),
                0,
            ),
            Err(VmAirCompositionControlError::SampledValueCountMismatch {
                expected: profile.sampled_value_count(),
                actual: profile.sampled_value_count() + 1,
            })
        );
    }

    #[test]
    fn noncontiguous_air_instructions_are_rejected() {
        assert_eq!(
            validated_rows(
                &[
                    VerifierStep::EvaluateAirInstruction { instruction: 0 },
                    VerifierStep::BindStatement,
                    VerifierStep::EvaluateAirInstruction { instruction: 1 },
                    VerifierStep::AssertComposition {
                        sampled_value_count: 3,
                    },
                ],
                2,
                3,
                0,
            ),
            Err(VmAirCompositionControlError::NonContiguousInstruction {
                previous: 0,
                actual: 2,
            })
        );
    }

    #[test]
    fn missing_composition_assertion_is_rejected() {
        assert_eq!(
            validated_rows(
                &[VerifierStep::EvaluateAirInstruction { instruction: 0 }],
                1,
                3,
                0,
            ),
            Err(VmAirCompositionControlError::CompositionAssertionMissing)
        );
    }
}
