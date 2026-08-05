//! AIR ownership for universal arithmetic-circuit inputs and fixed anchors.
//!
//! Verifier preprocessing assigns segment-mode VM inputs and binary-mode
//! recursion inputs to their sampled values, claimed sums, relation challenges,
//! typed randomness, statement words, and selectors. The same DSL table anchors
//! fixed constants and zero outputs, consuming every source and emitting every
//! circuit wire with its exact verifier-owned use count.

use core::fmt;
use std::collections::{HashMap, HashSet};

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::{CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use super::control_air::SEGMENT_VERIFIER_ID;
use super::recursion_air_composition_circuit::{
    RecursionAirCompositionCircuit, RecursionAirCompositionInputSource,
};
use super::relation_challenge_air::{AIR_EVALUATION_CHALLENGE_SCOPE, RelationChallengeRelations};
use super::statement_input_air::{StatementInputRelations, StatementWordRelation};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
use super::vm_air_composition_circuit::{
    SECURE_VALUE_WORD_COUNT, VmAirCompositionCircuit, VmAirCompositionInputSource,
};
use super::wire::ProofKind;
use crate::circuit::{limbs, use_counts_for_outputs};
use crate::recorder::{ConstraintCircuit, Op};
use crate::relations::RecursionRelations;

const MIN_LOG_SIZE: u32 = 4;
const RELATION_CHALLENGE_WORD_COUNT_U32: u32 = 8;
const SECURE_VALUE_WORD_COUNT_U32: u32 = 4;

const ROW_MASK_COLUMN: usize = 0;
const SAMPLED_VALUE_MASK_COLUMN: usize = 1;
const CLAIMED_SUM_MASK_COLUMN: usize = 2;
const CHALLENGE_MASK_COLUMN: usize = 3;
const COMPOSITION_RANDOMNESS_MASK_COLUMN: usize = 4;
const OODS_POINT_MASK_COLUMN: usize = 5;
const SELECTOR_MASK_COLUMN: usize = 6;
const CIRCUIT_ID_COLUMN: usize = 7;
const NODE_ID_COLUMN: usize = 8;
const USE_COUNT_COLUMN: usize = 9;
const SOURCE_INDEX_0_COLUMN: usize = 10;
const SOURCE_INDEX_1_COLUMN: usize = 11;
const ANCHOR_ROW_MASK_COLUMN: usize = 12;
const CONSTANT_SEGMENT_USES_COLUMN: usize = 13;
const CONSTANT_BINARY_USES_COLUMN: usize = 14;
const CONSTANT_EMPTY_USES_COLUMN: usize = 15;
const OUTPUT_SEGMENT_MASK_COLUMN: usize = 16;
const OUTPUT_BINARY_MASK_COLUMN: usize = 17;
const OUTPUT_EMPTY_MASK_COLUMN: usize = 18;
const FIXED_VALUE_0_COLUMN: usize = 19;
const FIXED_VALUE_1_COLUMN: usize = 20;
const FIXED_VALUE_2_COLUMN: usize = 21;
const FIXED_VALUE_3_COLUMN: usize = 22;
const INPUT_SEGMENT_MASK_COLUMN: usize = 23;
const INPUT_BINARY_MASK_COLUMN: usize = 24;
const PARENT_BINARY_SELECTOR_MASK_COLUMN: usize = 25;
const CHILD_KIND_SELECTOR_MASK_COLUMN: usize = 26;
const STATEMENT_WORD_MASK_COLUMN: usize = 27;
const VERIFIER_ID_COLUMN: usize = 28;
const STATEMENT_SCOPE_COLUMN: usize = 29;
const RECURSION_CLAIMED_SUM_MASK_COLUMN: usize = 30;
const PREPROCESSED_COLUMN_COUNT: usize = 31;

/// Universal modes in which one fixed arithmetic-circuit anchor is active.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CircuitAnchorMode {
    segment: bool,
    binary: bool,
    empty: bool,
}

impl CircuitAnchorMode {
    pub const ALL: Self = Self {
        segment: true,
        binary: true,
        empty: true,
    };
    pub const SEGMENT: Self = Self {
        segment: true,
        binary: false,
        empty: false,
    };
    pub const BINARY: Self = Self {
        segment: false,
        binary: true,
        empty: false,
    };

    const fn selectors(self) -> [bool; 3] {
        [self.segment, self.binary, self.empty]
    }
}

/// One fixed circuit whose constants and zero outputs are closed inside the
/// universal AIR instead of supplied as verifier terms.
#[derive(Clone, Copy)]
pub struct CircuitAnchorLane<'a> {
    pub circuit_id: u32,
    pub circuit: &'a ConstraintCircuit,
    pub active_in: CircuitAnchorMode,
}

/// One recursion-child composition graph and the transcript/statement scopes
/// that own its inputs in a binary parent.
#[derive(Clone, Copy)]
pub struct RecursionCompositionInputLane<'a> {
    pub verifier_id: u32,
    pub circuit_id: u32,
    pub statement_scope: u32,
    pub circuit: &'a RecursionAirCompositionCircuit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AnchorKind {
    None,
    Constant,
    Output,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum CompositionInputSource {
    Vm(VmAirCompositionInputSource),
    Recursion {
        verifier_id: u32,
        statement_scope: u32,
        source: RecursionAirCompositionInputSource,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: Option<CompositionInputSource>,
    anchor: AnchorKind,
    anchor_mode: CircuitAnchorMode,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    source_index_0: u32,
    source_index_1: u32,
    fixed_value: [u32; 4],
}

/// Verifier-owned input-node layout for one fixed VM composition circuit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmAirCompositionInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    input_count: usize,
    vm_input_count: usize,
}

impl VmAirCompositionInputPreprocessed {
    pub fn new(
        reference: &VmAirCompositionCircuit,
        circuit_id: u32,
    ) -> Result<Self, VmAirCompositionInputError> {
        Self::new_with_anchors(reference, circuit_id, &[])
    }

    /// Owns the VM composition inputs plus every fixed circuit anchor in one
    /// existing DSL component. The VM circuit is always included as a segment
    /// anchor; callers provide the remaining universal circuits.
    pub fn new_with_anchors(
        reference: &VmAirCompositionCircuit,
        circuit_id: u32,
        additional_anchors: &[CircuitAnchorLane<'_>],
    ) -> Result<Self, VmAirCompositionInputError> {
        Self::new_with_anchors_and_recursion_inputs(reference, circuit_id, &[], additional_anchors)
    }

    /// Adds the two child-composition input lanes to the same fixed DSL table
    /// that owns VM composition inputs and all circuit anchors.
    pub fn new_with_anchors_and_recursion_inputs(
        reference: &VmAirCompositionCircuit,
        circuit_id: u32,
        recursion_lanes: &[RecursionCompositionInputLane<'_>],
        additional_anchors: &[CircuitAnchorLane<'_>],
    ) -> Result<Self, VmAirCompositionInputError> {
        M31Word::try_from(circuit_id)
            .map_err(|_| VmAirCompositionInputError::CircuitIdNotCanonical { circuit_id })?;
        let arena = reference.circuit().arena();
        let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
        let mut sources = HashSet::with_capacity(reference.input_bindings().len());
        let mut selector_count = 0_usize;
        let mut rows = Vec::with_capacity(reference.input_bindings().len());
        for binding in reference.input_bindings() {
            if !sources.insert(binding.source) {
                return Err(VmAirCompositionInputError::DuplicateInputSource {
                    source: binding.source,
                });
            }
            M31Word::try_from(binding.node_id).map_err(|_| {
                VmAirCompositionInputError::NodeIdNotCanonical {
                    node_id: binding.node_id,
                }
            })?;
            let node_id = usize::try_from(binding.node_id).map_err(|_| {
                VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                    node_id: binding.node_id,
                }
            })?;
            let node = arena
                .nodes
                .get(node_id)
                .ok_or(VmAirCompositionInputError::NodeMissing {
                    node_id: binding.node_id,
                })?;
            if node.op != Op::Input {
                return Err(VmAirCompositionInputError::BindingTargetsNonInput {
                    node_id: binding.node_id,
                });
            }
            let use_count = uses[node_id];
            M31Word::try_from(use_count).map_err(|_| {
                VmAirCompositionInputError::UseCountNotCanonical {
                    node_id: binding.node_id,
                    use_count,
                }
            })?;
            let (source_index_0, source_index_1) =
                validate_source(binding.source, reference, &mut selector_count)?;
            rows.push(PreprocessedRow {
                source: Some(CompositionInputSource::Vm(binding.source)),
                anchor: AnchorKind::None,
                anchor_mode: CircuitAnchorMode::SEGMENT,
                circuit_id,
                node_id: binding.node_id,
                use_count,
                source_index_0,
                source_index_1,
                fixed_value: [0; 4],
            });
        }
        if selector_count != 1 {
            return Err(VmAirCompositionInputError::SelectorCountMismatch {
                actual: selector_count,
            });
        }
        let expected_inputs = expected_input_count(reference)?;
        if rows.len() != expected_inputs {
            return Err(VmAirCompositionInputError::InputCountMismatch {
                expected: expected_inputs,
                actual: rows.len(),
            });
        }
        let vm_input_count = rows.len();
        drop(arena);

        for lane in recursion_lanes.iter().copied() {
            append_recursion_input_rows(&mut rows, lane)?;
        }
        let input_count = rows.len();

        let primary_anchor = CircuitAnchorLane {
            circuit_id,
            circuit: reference.circuit(),
            active_in: CircuitAnchorMode::SEGMENT,
        };
        let mut circuit_ids = HashSet::with_capacity(additional_anchors.len() + 1);
        append_anchor_rows(&mut rows, primary_anchor, &mut circuit_ids)?;
        for anchor in additional_anchors.iter().copied() {
            append_anchor_rows(&mut rows, anchor, &mut circuit_ids)?;
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmAirCompositionInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
            return Err(VmAirCompositionInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            input_count,
            vm_input_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn input_count(&self) -> usize {
        self.input_count
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
            columns[SAMPLED_VALUE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::SampledValueWord { .. }
                )) | Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::SampledValueWord { .. },
                    ..
                })
            ));
            columns[CLAIMED_SUM_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::ClaimedSumWord { .. }
                )) | Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::ClaimedSumWord { .. },
                    ..
                })
            ));
            columns[CHALLENGE_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::RelationChallengeWord { .. }
                )) | Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::RelationChallengeWord { .. },
                    ..
                })
            ));
            columns[COMPOSITION_RANDOMNESS_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::CompositionRandomnessWord { .. }
                )) | Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::CompositionRandomnessWord { .. },
                    ..
                })
            ));
            columns[OODS_POINT_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::OodsPointWord { .. }
                )) | Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::OodsPointWord { .. },
                    ..
                })
            ));
            columns[SELECTOR_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Vm(
                    VmAirCompositionInputSource::SegmentSelector
                ))
            ));
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[SOURCE_INDEX_0_COLUMN][index] = row.source_index_0;
            columns[SOURCE_INDEX_1_COLUMN][index] = row.source_index_1;
            let [segment, binary, empty] = row.anchor_mode.selectors();
            columns[ANCHOR_ROW_MASK_COLUMN][index] = u32::from(row.anchor != AnchorKind::None);
            columns[CONSTANT_SEGMENT_USES_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Constant && segment) * row.use_count;
            columns[CONSTANT_BINARY_USES_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Constant && binary) * row.use_count;
            columns[CONSTANT_EMPTY_USES_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Constant && empty) * row.use_count;
            columns[OUTPUT_SEGMENT_MASK_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Output && segment);
            columns[OUTPUT_BINARY_MASK_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Output && binary);
            columns[OUTPUT_EMPTY_MASK_COLUMN][index] =
                u32::from(row.anchor == AnchorKind::Output && empty);
            columns[FIXED_VALUE_0_COLUMN][index] = row.fixed_value[0];
            columns[FIXED_VALUE_1_COLUMN][index] = row.fixed_value[1];
            columns[FIXED_VALUE_2_COLUMN][index] = row.fixed_value[2];
            columns[FIXED_VALUE_3_COLUMN][index] = row.fixed_value[3];
            columns[INPUT_SEGMENT_MASK_COLUMN][index] =
                u32::from(matches!(row.source, Some(CompositionInputSource::Vm(_))));
            columns[INPUT_BINARY_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Recursion { .. })
            ));
            columns[PARENT_BINARY_SELECTOR_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::ParentBinarySelector,
                    ..
                })
            ));
            columns[CHILD_KIND_SELECTOR_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::ChildKindSelector { .. },
                    ..
                })
            ));
            columns[STATEMENT_WORD_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::StatementWord { .. },
                    ..
                })
            ));
            if let Some(CompositionInputSource::Recursion {
                verifier_id,
                statement_scope,
                ..
            }) = row.source
            {
                columns[VERIFIER_ID_COLUMN][index] = verifier_id;
                columns[STATEMENT_SCOPE_COLUMN][index] = statement_scope;
            } else if matches!(row.source, Some(CompositionInputSource::Vm(_))) {
                columns[VERIFIER_ID_COLUMN][index] = SEGMENT_VERIFIER_ID;
            }
            columns[RECURSION_CLAIMED_SUM_MASK_COLUMN][index] = u32::from(matches!(
                row.source,
                Some(CompositionInputSource::Recursion {
                    source: RecursionAirCompositionInputSource::ClaimedSumWord { .. },
                    ..
                })
            ));
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn append_anchor_rows(
    rows: &mut Vec<PreprocessedRow>,
    anchor: CircuitAnchorLane<'_>,
    circuit_ids: &mut HashSet<u32>,
) -> Result<(), VmAirCompositionInputError> {
    M31Word::try_from(anchor.circuit_id).map_err(|_| {
        VmAirCompositionInputError::CircuitIdNotCanonical {
            circuit_id: anchor.circuit_id,
        }
    })?;
    if !circuit_ids.insert(anchor.circuit_id) {
        return Err(VmAirCompositionInputError::DuplicateCircuitId {
            circuit_id: anchor.circuit_id,
        });
    }
    let arena = anchor.circuit.arena();
    let uses = use_counts_for_outputs(&arena, anchor.circuit.outputs());
    for (node_index, node) in arena.nodes.iter().enumerate() {
        let node_id = checked_node_id(node_index)?;
        match node.op {
            Op::Input => {}
            Op::Const => rows.push(anchor_row(
                anchor,
                AnchorKind::Constant,
                node_id,
                uses[node_index],
                limbs(node.value),
            )),
            Op::Add(_, _) | Op::Sub(_, _) | Op::Mul(_, _) | Op::Neg(_) | Op::Inverse(_) => {}
        }
    }
    for output in anchor.circuit.outputs() {
        rows.push(anchor_row(
            anchor,
            AnchorKind::Output,
            checked_node_id(*output)?,
            0,
            [0; 4],
        ));
    }
    Ok(())
}

fn append_recursion_input_rows(
    rows: &mut Vec<PreprocessedRow>,
    lane: RecursionCompositionInputLane<'_>,
) -> Result<(), VmAirCompositionInputError> {
    M31Word::try_from(lane.verifier_id).map_err(|_| {
        VmAirCompositionInputError::VerifierIdNotCanonical {
            verifier_id: lane.verifier_id,
        }
    })?;
    M31Word::try_from(lane.statement_scope).map_err(|_| {
        VmAirCompositionInputError::StatementScopeNotCanonical {
            statement_scope: lane.statement_scope,
        }
    })?;
    M31Word::try_from(lane.circuit_id).map_err(|_| {
        VmAirCompositionInputError::CircuitIdNotCanonical {
            circuit_id: lane.circuit_id,
        }
    })?;
    let arena = lane.circuit.circuit().arena();
    let uses = use_counts_for_outputs(&arena, lane.circuit.circuit().outputs());
    let mut sources = HashSet::with_capacity(lane.circuit.input_bindings().len());
    let mut parent_selector_count = 0_usize;
    let mut child_selector_count = 0_usize;
    for binding in lane.circuit.input_bindings() {
        if !sources.insert(binding.source) {
            return Err(VmAirCompositionInputError::DuplicateRecursionInputSource {
                circuit_id: lane.circuit_id,
                source: binding.source,
            });
        }
        let node_id = checked_node_id(usize::try_from(binding.node_id).map_err(|_| {
            VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?)?;
        let node_index = usize::try_from(node_id)
            .map_err(|_| VmAirCompositionInputError::NodeIdDoesNotFitUsize { node_id })?;
        let node = arena
            .nodes
            .get(node_index)
            .ok_or(VmAirCompositionInputError::NodeMissing { node_id })?;
        if node.op != Op::Input {
            return Err(VmAirCompositionInputError::BindingTargetsNonInput { node_id });
        }
        let (source_index_0, source_index_1) = validate_recursion_source(
            binding.source,
            &mut parent_selector_count,
            &mut child_selector_count,
        )?;
        let use_count = uses[node_index];
        M31Word::try_from(use_count)
            .map_err(|_| VmAirCompositionInputError::UseCountNotCanonical { node_id, use_count })?;
        rows.push(PreprocessedRow {
            source: Some(CompositionInputSource::Recursion {
                verifier_id: lane.verifier_id,
                statement_scope: lane.statement_scope,
                source: binding.source,
            }),
            anchor: AnchorKind::None,
            anchor_mode: CircuitAnchorMode::BINARY,
            circuit_id: lane.circuit_id,
            node_id,
            use_count,
            source_index_0,
            source_index_1,
            fixed_value: [0; 4],
        });
    }
    if parent_selector_count != 1 || child_selector_count != 3 {
        return Err(VmAirCompositionInputError::RecursionSelectorCountMismatch {
            parent: parent_selector_count,
            child: child_selector_count,
        });
    }
    Ok(())
}

fn validate_recursion_source(
    source: RecursionAirCompositionInputSource,
    parent_selector_count: &mut usize,
    child_selector_count: &mut usize,
) -> Result<(u32, u32), VmAirCompositionInputError> {
    match source {
        RecursionAirCompositionInputSource::ParentBinarySelector => {
            *parent_selector_count = parent_selector_count
                .checked_add(1)
                .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
            Ok((0, 0))
        }
        RecursionAirCompositionInputSource::ChildKindSelector { kind } => {
            *child_selector_count = child_selector_count
                .checked_add(1)
                .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
            Ok((
                match kind {
                    ProofKind::SegmentLeaf => 0,
                    ProofKind::BinaryNode => 1,
                    ProofKind::EmptyLeaf => 2,
                },
                0,
            ))
        }
        RecursionAirCompositionInputSource::StatementWord { word_index } => {
            if usize::try_from(word_index)
                .ok()
                .filter(|index| *index < crate::statement::SPAN_STATEMENT_CANONICAL_WORDS)
                .is_none()
            {
                return Err(VmAirCompositionInputError::StatementWordIndexOutOfRange {
                    word_index,
                });
            }
            Ok((word_index, 0))
        }
        RecursionAirCompositionInputSource::SampledValueWord {
            item_index,
            word_index,
        }
        | RecursionAirCompositionInputSource::ClaimedSumWord {
            item_index,
            word_index,
        } => {
            if word_index >= SECURE_VALUE_WORD_COUNT_U32 {
                return Err(
                    VmAirCompositionInputError::RecursionSecureWordIndexOutOfRange { word_index },
                );
            }
            Ok((item_index, word_index))
        }
        RecursionAirCompositionInputSource::RelationChallengeWord {
            challenge,
            word_index,
        } => {
            if challenge >= crate::universal_relations::UNIVERSAL_RELATION_COUNT as u32 {
                return Err(VmAirCompositionInputError::ChallengeIndexOutOfRange { challenge });
            }
            if word_index >= RELATION_CHALLENGE_WORD_COUNT_U32 {
                return Err(VmAirCompositionInputError::ChallengeWordOutOfRange { word_index });
            }
            Ok((challenge, word_index))
        }
        RecursionAirCompositionInputSource::CompositionRandomnessWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::CompositionRandomness, word_index)?;
            Ok((0, word_index))
        }
        RecursionAirCompositionInputSource::OodsPointWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::OodsPoint, word_index)?;
            Ok((0, word_index))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn anchor_row(
    anchor: CircuitAnchorLane<'_>,
    kind: AnchorKind,
    node_id: u32,
    use_count: u32,
    fixed_value: [u32; 4],
) -> PreprocessedRow {
    PreprocessedRow {
        source: None,
        anchor: kind,
        anchor_mode: anchor.active_in,
        circuit_id: anchor.circuit_id,
        node_id,
        use_count,
        source_index_0: 0,
        source_index_1: 0,
        fixed_value,
    }
}

fn checked_node_id(node_id: usize) -> Result<u32, VmAirCompositionInputError> {
    let node_id = u32::try_from(node_id)
        .map_err(|_| VmAirCompositionInputError::NodeIndexOutOfRange { node_id })?;
    M31Word::try_from(node_id)
        .map(M31Word::as_u32)
        .map_err(|_| VmAirCompositionInputError::NodeIdNotCanonical { node_id })
}

fn validate_source(
    source: VmAirCompositionInputSource,
    reference: &VmAirCompositionCircuit,
    selector_count: &mut usize,
) -> Result<(u32, u32), VmAirCompositionInputError> {
    let profile = reference.profile();
    match source {
        VmAirCompositionInputSource::SampledValueWord {
            item_index,
            word_index,
        } => {
            validate_secure_coordinate(
                VmAirCompositionInputKind::SampledValue,
                item_index,
                word_index,
                profile.sampled_value_count(),
            )?;
            Ok((item_index, word_index))
        }
        VmAirCompositionInputSource::ClaimedSumWord {
            item_index,
            word_index,
        } => {
            validate_secure_coordinate(
                VmAirCompositionInputKind::ClaimedSum,
                item_index,
                word_index,
                profile.claimed_sum_count(),
            )?;
            Ok((item_index, word_index))
        }
        VmAirCompositionInputSource::RelationChallengeWord {
            challenge,
            word_index,
        } => {
            if challenge >= profile.relation_challenge_count() {
                return Err(VmAirCompositionInputError::ChallengeIndexOutOfRange { challenge });
            }
            if word_index >= RELATION_CHALLENGE_WORD_COUNT_U32 {
                return Err(VmAirCompositionInputError::ChallengeWordOutOfRange { word_index });
            }
            Ok((challenge, word_index))
        }
        VmAirCompositionInputSource::CompositionRandomnessWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::CompositionRandomness, word_index)?;
            Ok((0, word_index))
        }
        VmAirCompositionInputSource::OodsPointWord { word_index } => {
            validate_randomness_word(VerifierRandomnessKind::OodsPoint, word_index)?;
            Ok((0, word_index))
        }
        VmAirCompositionInputSource::SegmentSelector => {
            *selector_count = selector_count
                .checked_add(1)
                .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
            Ok((0, 0))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmAirCompositionInputKind {
    SampledValue,
    ClaimedSum,
}

fn validate_secure_coordinate(
    kind: VmAirCompositionInputKind,
    item_index: u32,
    word_index: u32,
    item_count: u32,
) -> Result<(), VmAirCompositionInputError> {
    if item_index >= item_count {
        return Err(VmAirCompositionInputError::SecureItemIndexOutOfRange {
            kind,
            item_index,
            item_count,
        });
    }
    if word_index >= SECURE_VALUE_WORD_COUNT_U32 {
        return Err(VmAirCompositionInputError::SecureWordIndexOutOfRange { kind, word_index });
    }
    Ok(())
}

fn validate_randomness_word(
    kind: VerifierRandomnessKind,
    word_index: u32,
) -> Result<(), VmAirCompositionInputError> {
    if word_index >= SECURE_VALUE_WORD_COUNT_U32 {
        return Err(VmAirCompositionInputError::RandomnessWordOutOfRange { kind, word_index });
    }
    Ok(())
}

fn expected_input_count(
    reference: &VmAirCompositionCircuit,
) -> Result<usize, VmAirCompositionInputError> {
    let profile = reference.profile();
    let sampled = usize::try_from(profile.sampled_value_count())
        .ok()
        .and_then(|count| count.checked_mul(SECURE_VALUE_WORD_COUNT))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    let claimed = usize::try_from(profile.claimed_sum_count())
        .ok()
        .and_then(|count| count.checked_mul(SECURE_VALUE_WORD_COUNT))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    let challenges = usize::try_from(profile.relation_challenge_count())
        .ok()
        .and_then(|count| count.checked_mul(RELATION_CHALLENGE_WORD_COUNT_U32 as usize))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)?;
    sampled
        .checked_add(claimed)
        .and_then(|count| count.checked_add(challenges))
        .and_then(|count| count.checked_add(2 * SECURE_VALUE_WORD_COUNT))
        .and_then(|count| count.checked_add(1))
        .ok_or(VmAirCompositionInputError::RowCountOverflow)
}

/// Relations used by the macro-generated VM composition input component.
#[derive(Clone)]
pub struct VmAirCompositionInputComponentRelations {
    pub verifier_input_word: super::transcript_payload_air::VerifierInputWordRelation,
    pub challenge_word: super::relation_challenge_air::RelationChallengeWordRelation,
    pub randomness_word: super::verifier_randomness_air::VerifierRandomnessWordRelation,
    pub statement_word: StatementWordRelation,
    pub wire: crate::relations::WireRelation,
}

impl VmAirCompositionInputComponentRelations {
    /// Combine every transcript source with the shared arithmetic wire relation.
    pub fn new(
        challenge_relations: &RelationChallengeRelations,
        verifier_input_relations: &VerifierInputRelations,
        randomness_relations: &VerifierRandomnessRelations,
        statement_relations: &StatementInputRelations,
        circuit_relations: &RecursionRelations,
    ) -> Self {
        Self {
            verifier_input_word: verifier_input_relations.input_word.clone(),
            challenge_word: challenge_relations.word.clone(),
            randomness_word: randomness_relations.word.clone(),
            statement_word: statement_relations.statement_word.clone(),
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
        crate::vm_air_composition_input_air::VmAirCompositionInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_air_composition_input_row_mask",
        sampled_value_mask: "recursion_vm_air_composition_input_sampled_value_mask",
        claimed_sum_mask: "recursion_vm_air_composition_input_claimed_sum_mask",
        challenge_mask: "recursion_vm_air_composition_input_challenge_mask",
        composition_randomness_mask:
            "recursion_vm_air_composition_input_composition_randomness_mask",
        oods_point_mask: "recursion_vm_air_composition_input_oods_point_mask",
        selector_mask: "recursion_vm_air_composition_input_selector_mask",
        circuit_id: "recursion_vm_air_composition_input_circuit_id",
        node_id: "recursion_vm_air_composition_input_node_id",
        use_count: "recursion_vm_air_composition_input_use_count",
        source_index_0: "recursion_vm_air_composition_input_source_index_0",
        source_index_1: "recursion_vm_air_composition_input_source_index_1",
        anchor_row_mask: "recursion_circuit_anchor_row_mask",
        constant_segment_uses: "recursion_circuit_anchor_constant_segment_uses",
        constant_binary_uses: "recursion_circuit_anchor_constant_binary_uses",
        constant_empty_uses: "recursion_circuit_anchor_constant_empty_uses",
        output_segment_mask: "recursion_circuit_anchor_output_segment_mask",
        output_binary_mask: "recursion_circuit_anchor_output_binary_mask",
        output_empty_mask: "recursion_circuit_anchor_output_empty_mask",
        fixed_value_0: "recursion_circuit_anchor_fixed_value_0",
        fixed_value_1: "recursion_circuit_anchor_fixed_value_1",
        fixed_value_2: "recursion_circuit_anchor_fixed_value_2",
        fixed_value_3: "recursion_circuit_anchor_fixed_value_3",
        input_segment_mask: "recursion_circuit_input_segment_mask",
        input_binary_mask: "recursion_circuit_input_binary_mask",
        parent_binary_selector_mask: "recursion_circuit_parent_binary_selector_mask",
        child_kind_selector_mask: "recursion_circuit_child_kind_selector_mask",
        statement_word_mask: "recursion_circuit_statement_word_mask",
        verifier_id: "recursion_circuit_input_verifier_id",
        statement_scope: "recursion_circuit_input_statement_scope",
        recursion_claimed_sum_mask: "recursion_circuit_input_recursion_claimed_sum_mask",
    },
    embedded_params: [
        segment_active, binary_active, empty_active,
        sampled_value_kind, vm_claimed_sum_kind, recursion_claimed_sum_kind,
        challenge_scope, composition_randomness_kind, oods_point_kind,
    ],

    relation verifier_input_word(5);
    relation challenge_word(5);
    relation randomness_word(5);
    relation statement_word(3);
    relation wire(6);

    fn vm_air_composition_input(
        value,
        row_mask, sampled_value_mask, claimed_sum_mask, challenge_mask,
        composition_randomness_mask, oods_point_mask, selector_mask,
        circuit_id, node_id, use_count, source_index_0, source_index_1,
        anchor_row_mask,
        constant_segment_uses, constant_binary_uses, constant_empty_uses,
        output_segment_mask, output_binary_mask, output_empty_mask,
        fixed_value_0, fixed_value_1, fixed_value_2, fixed_value_3,
        input_segment_mask, input_binary_mask,
        parent_binary_selector_mask, child_kind_selector_mask,
        statement_word_mask, verifier_id, statement_scope,
        recursion_claimed_sum_mask,
        segment_active, binary_active, empty_active,
        sampled_value_kind, vm_claimed_sum_kind, recursion_claimed_sum_kind,
        challenge_scope, composition_randomness_kind, oods_point_kind,
    ) {
        let input_mask = sampled_value_mask + claimed_sum_mask + challenge_mask
            + composition_randomness_mask + oods_point_mask + selector_mask
            + parent_binary_selector_mask + child_kind_selector_mask
            + statement_word_mask;
        let input_active = input_segment_mask * segment_active
            + input_binary_mask * binary_active;
        let constant_uses = constant_segment_uses * segment_active
            + constant_binary_uses * binary_active
            + constant_empty_uses * empty_active;
        let output_active = output_segment_mask * segment_active
            + output_binary_mask * binary_active
            + output_empty_mask * empty_active;

        constrain enabler - row_mask;
        constrain row_mask - input_mask - anchor_row_mask;
        constrain input_segment_mask * (1 - segment_active) * value;
        constrain input_binary_mask * (1 - binary_active) * value;
        constrain selector_mask * (value - segment_active);
        constrain parent_binary_selector_mask * (value - binary_active);
        constrain anchor_row_mask * value;

        consume(input_active * sampled_value_mask) verifier_input_word(
            verifier_id, sampled_value_kind, source_index_0, source_index_1, value,
        );
        consume(input_active * (claimed_sum_mask - recursion_claimed_sum_mask)) verifier_input_word(
            verifier_id, vm_claimed_sum_kind, source_index_0, source_index_1, value,
        );
        consume(input_active * recursion_claimed_sum_mask) verifier_input_word(
            verifier_id, recursion_claimed_sum_kind, source_index_0, source_index_1, value,
        );
        consume(input_active * challenge_mask) challenge_word(
            verifier_id, challenge_scope, source_index_0, source_index_1, value,
        );
        consume(input_active * composition_randomness_mask) randomness_word(
            verifier_id, composition_randomness_kind, source_index_0, source_index_1, value,
        );
        consume(input_active * oods_point_mask) randomness_word(
            verifier_id, oods_point_kind, source_index_0, source_index_1, value,
        );
        consume(input_active * statement_word_mask) statement_word(
            statement_scope, source_index_0, value,
        );
        emit(input_active * use_count) wire(
            circuit_id, node_id, value, 0, 0, 0,
        );
        emit(constant_uses) wire(
            circuit_id, node_id,
            fixed_value_0, fixed_value_1, fixed_value_2, fixed_value_3,
        );
        consume(output_active) wire(
            circuit_id, node_id,
            fixed_value_0, fixed_value_1, fixed_value_2, fixed_value_3,
        );

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for the selected universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    statement_relations: &StatementInputRelations,
    circuit_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        empty_active: BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf)),
        sampled_value_kind: BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        vm_claimed_sum_kind: BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32()),
        recursion_claimed_sum_kind: BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        challenge_scope: BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        composition_randomness_kind: BaseField::from(
            VerifierRandomnessKind::CompositionRandomness.as_u32(),
        ),
        oods_point_kind: BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        relations: VmAirCompositionInputComponentRelations::new(
            challenge_relations,
            verifier_input_relations,
            randomness_relations,
            statement_relations,
            circuit_relations,
        ),
    }
}

/// Generate source consumers and exact circuit-wire producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    challenge_relations: &RelationChallengeRelations,
    verifier_input_relations: &VerifierInputRelations,
    randomness_relations: &VerifierRandomnessRelations,
    statement_relations: &StatementInputRelations,
    circuit_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(u32::from(proof_kind == ProofKind::EmptyLeaf)),
        BaseField::from(VerifierInputKind::SampledValue.as_u32()),
        BaseField::from(VerifierInputKind::VmAirClaimedSum.as_u32()),
        BaseField::from(VerifierInputKind::ClaimedSum.as_u32()),
        BaseField::from(AIR_EVALUATION_CHALLENGE_SCOPE),
        BaseField::from(VerifierRandomnessKind::CompositionRandomness.as_u32()),
        BaseField::from(VerifierRandomnessKind::OodsPoint.as_u32()),
        &VmAirCompositionInputComponentRelations::new(
            challenge_relations,
            verifier_input_relations,
            randomness_relations,
            statement_relations,
            circuit_relations,
        ),
    )
}

/// Materializes input values after checking the fixed circuit layout.
pub fn push_vm_air_composition_inputs(
    table: &mut VmAirCompositionInputTable,
    preprocessed: &VmAirCompositionInputPreprocessed,
    reference: &VmAirCompositionCircuit,
    witness: &VmAirCompositionCircuit,
    proof_kind: ProofKind,
) -> Result<(), VmAirCompositionInputError> {
    push_air_composition_inputs(
        table,
        preprocessed,
        reference,
        witness,
        &[],
        &[],
        proof_kind,
    )
}

/// Materializes VM and recursion-child inputs under the selected universal mode.
#[allow(clippy::too_many_arguments)]
pub fn push_air_composition_inputs(
    table: &mut VmAirCompositionInputTable,
    preprocessed: &VmAirCompositionInputPreprocessed,
    vm_reference: &VmAirCompositionCircuit,
    vm_witness: &VmAirCompositionCircuit,
    recursion_references: &[RecursionCompositionInputLane<'_>],
    recursion_witnesses: &[RecursionCompositionInputLane<'_>],
    proof_kind: ProofKind,
) -> Result<(), VmAirCompositionInputError> {
    let mut values = HashMap::with_capacity(preprocessed.input_count);
    append_vm_input_values(
        &mut values,
        vm_reference,
        vm_witness,
        proof_kind == ProofKind::SegmentLeaf,
        preprocessed
            .rows
            .iter()
            .find_map(|row| {
                matches!(row.source, Some(CompositionInputSource::Vm(_))).then_some(row.circuit_id)
            })
            .ok_or(VmAirCompositionInputError::VmInputLaneMissing)?,
        preprocessed.vm_input_count,
    )?;
    if recursion_references.len() != recursion_witnesses.len() {
        return Err(VmAirCompositionInputError::RecursionLaneCountMismatch {
            expected: recursion_references.len(),
            actual: recursion_witnesses.len(),
        });
    }
    for (reference, witness) in recursion_references
        .iter()
        .copied()
        .zip(recursion_witnesses.iter().copied())
    {
        append_recursion_input_values(
            &mut values,
            reference,
            witness,
            proof_kind == ProofKind::BinaryNode,
        )?;
    }
    if values.len() != preprocessed.input_count {
        return Err(VmAirCompositionInputError::InputCountMismatch {
            expected: preprocessed.input_count,
            actual: values.len(),
        });
    }
    for row in &preprocessed.rows {
        let Some(source) = row.source else {
            table.push(0);
            continue;
        };
        let value = values
            .remove(&(row.circuit_id, row.node_id, source))
            .ok_or(VmAirCompositionInputError::InputCoordinateMismatch {
                node_id: row.node_id,
            })?;
        table.push(value);
    }
    if !values.is_empty() {
        return Err(VmAirCompositionInputError::InputCountMismatch {
            expected: preprocessed.input_count,
            actual: preprocessed.input_count + values.len(),
        });
    }
    Ok(())
}

fn append_vm_input_values(
    values: &mut HashMap<(u32, u32, CompositionInputSource), u32>,
    reference: &VmAirCompositionCircuit,
    witness: &VmAirCompositionCircuit,
    active: bool,
    circuit_id: u32,
    expected_input_count: usize,
) -> Result<(), VmAirCompositionInputError> {
    if reference.profile() != witness.profile()
        || reference.input_bindings() != witness.input_bindings()
        || reference.circuit().outputs() != witness.circuit().outputs()
    {
        return Err(VmAirCompositionInputError::InputLayoutMismatch);
    }
    if witness.input_bindings().len() != expected_input_count {
        return Err(VmAirCompositionInputError::InputCountMismatch {
            expected: expected_input_count,
            actual: witness.input_bindings().len(),
        });
    }
    let arena = witness.circuit().arena();
    for binding in witness.input_bindings() {
        let node_id = usize::try_from(binding.node_id).map_err(|_| {
            VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?;
        let node = arena
            .nodes
            .get(node_id)
            .ok_or(VmAirCompositionInputError::NodeMissing {
                node_id: binding.node_id,
            })?;
        if node.op != Op::Input {
            return Err(VmAirCompositionInputError::BindingTargetsNonInput {
                node_id: binding.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(VmAirCompositionInputError::InputIsNotBaseField {
                node_id: binding.node_id,
            });
        }
        let expected = if binding.source == VmAirCompositionInputSource::SegmentSelector {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(VmAirCompositionInputError::InactiveInputIsNonZero {
                node_id: binding.node_id,
            });
        }
        if values
            .insert(
                (
                    circuit_id,
                    binding.node_id,
                    CompositionInputSource::Vm(binding.source),
                ),
                expected,
            )
            .is_some()
        {
            return Err(VmAirCompositionInputError::InputCoordinateMismatch {
                node_id: binding.node_id,
            });
        }
    }
    Ok(())
}

fn append_recursion_input_values(
    values: &mut HashMap<(u32, u32, CompositionInputSource), u32>,
    reference: RecursionCompositionInputLane<'_>,
    witness: RecursionCompositionInputLane<'_>,
    active: bool,
) -> Result<(), VmAirCompositionInputError> {
    if reference.verifier_id != witness.verifier_id
        || reference.circuit_id != witness.circuit_id
        || reference.statement_scope != witness.statement_scope
        || reference.circuit.input_bindings() != witness.circuit.input_bindings()
        || reference.circuit.circuit().outputs() != witness.circuit.circuit().outputs()
    {
        return Err(VmAirCompositionInputError::InputLayoutMismatch);
    }
    let arena = witness.circuit.circuit().arena();
    for binding in witness.circuit.input_bindings() {
        let node_id = usize::try_from(binding.node_id).map_err(|_| {
            VmAirCompositionInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?;
        let node = arena
            .nodes
            .get(node_id)
            .ok_or(VmAirCompositionInputError::NodeMissing {
                node_id: binding.node_id,
            })?;
        if node.op != Op::Input {
            return Err(VmAirCompositionInputError::BindingTargetsNonInput {
                node_id: binding.node_id,
            });
        }
        let limbs = node.value.to_m31_array();
        if limbs[1..].iter().any(|limb| limb.0 != 0) {
            return Err(VmAirCompositionInputError::InputIsNotBaseField {
                node_id: binding.node_id,
            });
        }
        let expected = if binding.source == RecursionAirCompositionInputSource::ParentBinarySelector
        {
            u32::from(active)
        } else if active {
            limbs[0].0
        } else {
            0
        };
        if limbs[0].0 != expected {
            return Err(VmAirCompositionInputError::InactiveInputIsNonZero {
                node_id: binding.node_id,
            });
        }
        let source = CompositionInputSource::Recursion {
            verifier_id: witness.verifier_id,
            statement_scope: witness.statement_scope,
            source: binding.source,
        };
        if values
            .insert((witness.circuit_id, binding.node_id, source), expected)
            .is_some()
        {
            return Err(VmAirCompositionInputError::InputCoordinateMismatch {
                node_id: binding.node_id,
            });
        }
    }
    Ok(())
}

/// Invalid composition input layout, coordinate, or mode assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmAirCompositionInputError {
    VerifierIdNotCanonical {
        verifier_id: u32,
    },
    StatementScopeNotCanonical {
        statement_scope: u32,
    },
    CircuitIdNotCanonical {
        circuit_id: u32,
    },
    DuplicateCircuitId {
        circuit_id: u32,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    NodeIdNotCanonical {
        node_id: u32,
    },
    NodeIndexOutOfRange {
        node_id: usize,
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
        source: VmAirCompositionInputSource,
    },
    DuplicateRecursionInputSource {
        circuit_id: u32,
        source: RecursionAirCompositionInputSource,
    },
    SecureItemIndexOutOfRange {
        kind: VmAirCompositionInputKind,
        item_index: u32,
        item_count: u32,
    },
    SecureWordIndexOutOfRange {
        kind: VmAirCompositionInputKind,
        word_index: u32,
    },
    ChallengeIndexOutOfRange {
        challenge: u32,
    },
    ChallengeWordOutOfRange {
        word_index: u32,
    },
    RandomnessWordOutOfRange {
        kind: VerifierRandomnessKind,
        word_index: u32,
    },
    SelectorCountMismatch {
        actual: usize,
    },
    RecursionSelectorCountMismatch {
        parent: usize,
        child: usize,
    },
    StatementWordIndexOutOfRange {
        word_index: u32,
    },
    RecursionSecureWordIndexOutOfRange {
        word_index: u32,
    },
    RecursionLaneCountMismatch {
        expected: usize,
        actual: usize,
    },
    VmInputLaneMissing,
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

impl fmt::Display for VmAirCompositionInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirCompositionInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::components::{COMPONENT_COUNT, COMPONENT_NAMES};
    use prover::relations::Relations;
    use rstest::rstest;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::air_relation_parameters::RELATION_CHALLENGE_WORD_COUNT;
    use crate::vm_air_composition_circuit::{
        VmAirCompositionWitness, build_vm_air_composition_circuit,
        build_vm_air_composition_reference,
    };
    use crate::vm_air_program::VmAirProgram;

    const CIRCUIT_ID: u32 = 43;

    fn component_log_sizes() -> [u32; COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    fn circuits(kind: ProofKind) -> (VmAirCompositionCircuit, VmAirCompositionCircuit) {
        let reference = build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture reference is constructible");
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let samples = vec![SecureField::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![SecureField::zero(); COMPONENT_COUNT];
        let challenges =
            vec![[M31Word::ZERO; RELATION_CHALLENGE_WORD_COUNT]; Relations::DESCRIPTORS.len()];
        let witness = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: kind == ProofKind::SegmentLeaf,
                sampled_values: &samples,
                claimed_sums: &claimed_sums,
                relation_challenges: &challenges,
                composition_randomness: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
                oods_point: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
            },
        )
        .expect("zero fixture has fixed composition structure");
        (reference, witness)
    }

    fn assert_constraints(kind: ProofKind) {
        let (reference, witness) = circuits(kind);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        let mut table = VmAirCompositionInputTable::new();
        push_vm_air_composition_inputs(&mut table, &preprocessing, &reference, &witness, kind)
            .expect("mode assignment matches its selector");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let challenge_relations = RelationChallengeRelations::dummy();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let statement_relations = StatementInputRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
            &statement_relations,
            &circuit_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &challenge_relations,
            &verifier_input_relations,
            &randomness_relations,
            &statement_relations,
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
    fn every_universal_mode_satisfies_composition_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[test]
    fn preprocessing_owns_every_tracked_input_once() {
        let (reference, _) = circuits(ProofKind::EmptyLeaf);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        assert_eq!(
            preprocessing.input_count(),
            reference.input_bindings().len()
        );
    }

    #[test]
    fn active_selector_cannot_be_reused_in_binary_mode() {
        let (reference, active) = circuits(ProofKind::SegmentLeaf);
        let preprocessing = VmAirCompositionInputPreprocessed::new(&reference, CIRCUIT_ID)
            .expect("reference owns every input once");
        let result = push_vm_air_composition_inputs(
            &mut VmAirCompositionInputTable::new(),
            &preprocessing,
            &reference,
            &active,
            ProofKind::BinaryNode,
        );
        assert!(matches!(
            result,
            Err(VmAirCompositionInputError::InactiveInputIsNonZero { .. })
        ));
    }
}
