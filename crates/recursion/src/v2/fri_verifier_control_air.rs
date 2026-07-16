//! Control-step and query-route adapter for fixed FRI verification.
//!
//! Trusted preprocessing extracts every DEEP, FRI-fold, and last-layer step
//! from the verifier plans for all three lanes. Fold and last-layer rows also
//! consume the atomic query-position tuple and export its scalar fields to the
//! fixed arithmetic circuit. This keeps schedule ownership and route splitting
//! in one component without letting committed values choose either layout.

use core::fmt;

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::{CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry,
};
use stwo_macros::define_component_tables;

use super::control_air::{
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::fri_verifier_circuit::FriVerifierProfile;
use super::fri_verifier_input_air::{FriVerifierRouteField, FriVerifierRouteRelations};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::query_position_air::{
    QueryPositionKind, QueryPositionPreprocessed, QueryPositionRelations,
};
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const ROUTE_MASK_COLUMN: usize = 3;
const OFFSET_OUTPUT_MASK_COLUMN: usize = 4;
const VERIFIER_ID_COLUMN: usize = 5;
const ROUTE_KIND_COLUMN: usize = 6;
const ITEM_COLUMN: usize = 7;
const QUERY_COLUMN: usize = 8;
const SEQUENCE_COLUMN: usize = 9;
const TAG_COLUMN: usize = 10;
const ARG_0_COLUMN: usize = 11;
const ARG_1_COLUMN: usize = 12;
const ARG_2_COLUMN: usize = 13;
const ARG_3_COLUMN: usize = 14;
const PREPROCESSED_COLUMN_COUNT: usize = 15;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_fri_control_row_mask",
    "recursion_v2_fri_control_segment_mask",
    "recursion_v2_fri_control_binary_mask",
    "recursion_v2_fri_control_route_mask",
    "recursion_v2_fri_control_offset_output_mask",
    "recursion_v2_fri_control_verifier_id",
    "recursion_v2_fri_control_route_kind",
    "recursion_v2_fri_control_item",
    "recursion_v2_fri_control_query",
    "recursion_v2_fri_control_sequence",
    "recursion_v2_fri_control_tag",
    "recursion_v2_fri_control_arg_0",
    "recursion_v2_fri_control_arg_1",
    "recursion_v2_fri_control_arg_2",
    "recursion_v2_fri_control_arg_3",
];

define_component_tables! {
    fri_verifier_control: {
        committed: { position, offset },
        constraints: {},
    },
}

use prover_columns::FriVerifierControlColumns;

/// One verifier plan and its fixed FRI circuit geometry.
#[derive(Clone, Copy)]
pub struct FriVerifierControlLane<'a> {
    pub verifier_id: u32,
    pub plan: &'a VerifierControlPlan,
    pub profile: &'a FriVerifierProfile,
}

/// Raw queries used to materialize one verifier lane's trusted routes.
#[derive(Clone, Copy)]
pub struct FriVerifierQueryLane<'a> {
    pub verifier_id: u32,
    pub raw_queries: &'a [M31Word],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    lane: usize,
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    route_kind: Option<QueryPositionKind>,
    item: u32,
    query: u32,
    offset_output: bool,
    sequence: u32,
    tag: u32,
    args: [u32; 4],
}

/// Trusted PCS-arithmetic control steps and route coordinates for all lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriVerifierControlPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    query_counts: [usize; 3],
}

impl FriVerifierControlPreprocessed {
    pub fn new(lanes: [FriVerifierControlLane<'_>; 3]) -> Result<Self, FriVerifierControlError> {
        validate_lane_order(&lanes)?;
        let mut rows = Vec::new();
        let mut query_counts = [0_usize; 3];
        for (lane_index, lane) in lanes.iter().copied().enumerate() {
            let expected_schema = if lane.verifier_id == SEGMENT_VERIFIER_ID {
                VerifierSchema::Vm
            } else {
                VerifierSchema::Recursion
            };
            if lane.plan.schema() != expected_schema {
                return Err(FriVerifierControlError::SchemaMismatch {
                    verifier_id: lane.verifier_id,
                    expected: expected_schema,
                    actual: lane.plan.schema(),
                });
            }
            let (segment_mask, binary_mask) = lane_masks(lane.verifier_id)?;
            rows.extend(validated_lane_rows(
                lane_index,
                segment_mask,
                binary_mask,
                lane.verifier_id,
                lane.plan.steps(),
                lane.profile,
            )?);
            query_counts[lane_index] = lane.profile.query_count();
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(FriVerifierControlError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
            return Err(FriVerifierControlError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            query_counts,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn row_count(&self) -> usize {
        self.rows.len()
    }

    pub fn column_ids() -> Vec<PreProcessedColumnId> {
        PREPROCESSED_COLUMN_IDS
            .iter()
            .map(|id| PreProcessedColumnId { id: (*id).into() })
            .collect()
    }

    pub fn gen_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.log_size;
        let mut columns = zero_columns(PREPROCESSED_COLUMN_COUNT, size);
        for (index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][index] = 1;
            columns[SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[ROUTE_MASK_COLUMN][index] = u32::from(row.route_kind.is_some());
            columns[OFFSET_OUTPUT_MASK_COLUMN][index] = u32::from(row.offset_output);
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[ROUTE_KIND_COLUMN][index] = row.route_kind.map_or(0, QueryPositionKind::as_u32);
            columns[ITEM_COLUMN][index] = row.item;
            columns[QUERY_COLUMN][index] = row.query;
            columns[SEQUENCE_COLUMN][index] = row.sequence;
            columns[TAG_COLUMN][index] = row.tag;
            columns[ARG_0_COLUMN][index] = row.args[0];
            columns[ARG_1_COLUMN][index] = row.args[1];
            columns[ARG_2_COLUMN][index] = row.args[2];
            columns[ARG_3_COLUMN][index] = row.args[3];
        }
        into_evaluations(columns, self.log_size)
    }
}

fn validate_lane_order(
    lanes: &[FriVerifierControlLane<'_>; 3],
) -> Result<(), FriVerifierControlError> {
    for (lane, expected) in lanes.iter().zip([
        SEGMENT_VERIFIER_ID,
        LEFT_RECURSION_VERIFIER_ID,
        RIGHT_RECURSION_VERIFIER_ID,
    ]) {
        if lane.verifier_id != expected {
            return Err(FriVerifierControlError::VerifierLaneOrderMismatch {
                expected,
                actual: lane.verifier_id,
            });
        }
    }
    Ok(())
}

fn validate_query_lane_order(
    lanes: &[FriVerifierQueryLane<'_>; 3],
) -> Result<(), FriVerifierControlError> {
    for (lane, expected) in lanes.iter().zip([
        SEGMENT_VERIFIER_ID,
        LEFT_RECURSION_VERIFIER_ID,
        RIGHT_RECURSION_VERIFIER_ID,
    ]) {
        if lane.verifier_id != expected {
            return Err(FriVerifierControlError::VerifierLaneOrderMismatch {
                expected,
                actual: lane.verifier_id,
            });
        }
    }
    Ok(())
}

fn lane_masks(verifier_id: u32) -> Result<(u32, u32), FriVerifierControlError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok((1, 0)),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => Ok((0, 1)),
        _ => Err(FriVerifierControlError::UnknownVerifierId { verifier_id }),
    }
}

#[allow(clippy::too_many_arguments)]
fn validated_lane_rows(
    lane: usize,
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    steps: &[VerifierStep],
    profile: &FriVerifierProfile,
) -> Result<Vec<PreprocessedRow>, FriVerifierControlError> {
    let mut rows = Vec::new();
    let mut deep_query = 0_usize;
    let mut fold_index = 0_usize;
    let mut last_query = 0_usize;
    for (sequence, step) in steps.iter().copied().enumerate() {
        let route =
            match step {
                VerifierStep::EvaluateDeepQuotient { query, .. } => {
                    let expected = checked_u32("DEEP query", deep_query)?;
                    if query != expected {
                        return Err(FriVerifierControlError::NonCanonicalDeepQuery {
                            expected,
                            actual: query,
                        });
                    }
                    deep_query += 1;
                    Some((None, 0, query, false))
                }
                VerifierStep::FoldFri {
                    layer,
                    query,
                    width,
                } => {
                    let expected_layer = fold_index / profile.query_count();
                    let expected_query = fold_index % profile.query_count();
                    if expected_layer >= profile.layer_count() {
                        return Err(FriVerifierControlError::ExtraFoldStep { layer, query });
                    }
                    let expected_layer_u32 = checked_u32("FRI layer", expected_layer)?;
                    let expected_query_u32 = checked_u32("FRI query", expected_query)?;
                    if layer != expected_layer_u32 || query != expected_query_u32 {
                        return Err(FriVerifierControlError::NonCanonicalFoldCoordinate {
                            expected_layer: expected_layer_u32,
                            expected_query: expected_query_u32,
                            actual_layer: layer,
                            actual_query: query,
                        });
                    }
                    let expected_width = u32::try_from(profile.fold_widths()[expected_layer])
                        .map_err(|_| FriVerifierControlError::IndexOutOfRange {
                            field: "FRI fold width",
                            value: profile.fold_widths()[expected_layer],
                        })?;
                    if width != expected_width {
                        return Err(FriVerifierControlError::FoldWidthMismatch {
                            layer,
                            expected: expected_width,
                            actual: width,
                        });
                    }
                    fold_index += 1;
                    Some((Some(QueryPositionKind::FriFold), layer, query, true))
                }
                VerifierStep::VerifyLastLayer { query } => {
                    let expected = checked_u32("last-layer query", last_query)?;
                    if query != expected {
                        return Err(FriVerifierControlError::NonCanonicalLastLayerQuery {
                            expected,
                            actual: query,
                        });
                    }
                    last_query += 1;
                    Some((Some(QueryPositionKind::LastLayer), 0, query, false))
                }
                _ => None,
            };
        if let Some((route_kind, item, query, offset_output)) = route {
            let encoded = step.encode();
            rows.push(PreprocessedRow {
                lane,
                segment_mask,
                binary_mask,
                verifier_id,
                route_kind,
                item,
                query,
                offset_output,
                sequence: u32::try_from(sequence)
                    .map_err(|_| FriVerifierControlError::SequenceOutOfRange { sequence })?,
                tag: encoded.tag(),
                args: encoded.args(),
            });
        }
    }
    if deep_query != profile.query_count() {
        return Err(FriVerifierControlError::DeepStepCountMismatch {
            expected: profile.query_count(),
            actual: deep_query,
        });
    }
    let expected_folds = profile
        .layer_count()
        .checked_mul(profile.query_count())
        .ok_or(FriVerifierControlError::RowCountOverflow)?;
    if fold_index != expected_folds {
        return Err(FriVerifierControlError::FoldStepCountMismatch {
            expected: expected_folds,
            actual: fold_index,
        });
    }
    if last_query != profile.query_count() {
        return Err(FriVerifierControlError::LastLayerStepCountMismatch {
            expected: profile.query_count(),
            actual: last_query,
        });
    }
    Ok(rows)
}

fn checked_u32(field: &'static str, value: usize) -> Result<u32, FriVerifierControlError> {
    u32::try_from(value).map_err(|_| FriVerifierControlError::IndexOutOfRange { field, value })
}

fn zero_columns(count: usize, size: usize) -> Vec<AlignedVec<u32>> {
    (0..count)
        .map(|_| {
            let mut column = AlignedVec::with_capacity(size);
            column.resize(size, 0);
            column
        })
        .collect()
}

fn into_evaluations(
    columns: Vec<AlignedVec<u32>>,
    log_size: u32,
) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
    let domain = CanonicCoset::new(log_size).circle_domain();
    columns
        .into_iter()
        .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
        .collect()
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub control_relations: ControlRelations,
    pub query_relations: QueryPositionRelations,
    pub route_relations: FriVerifierRouteRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = FriVerifierControlColumns::from_eval(&mut eval);
        let ids = FriVerifierControlPreprocessed::column_ids();
        let pp = |eval: &mut E, column: usize| eval.get_preprocessed_column(ids[column].clone());
        let row_mask = pp(&mut eval, ROW_MASK_COLUMN);
        let segment_mask = pp(&mut eval, SEGMENT_MASK_COLUMN);
        let binary_mask = pp(&mut eval, BINARY_MASK_COLUMN);
        let route_mask = pp(&mut eval, ROUTE_MASK_COLUMN);
        let offset_output_mask = pp(&mut eval, OFFSET_OUTPUT_MASK_COLUMN);
        let verifier_id = pp(&mut eval, VERIFIER_ID_COLUMN);
        let route_kind = pp(&mut eval, ROUTE_KIND_COLUMN);
        let item = pp(&mut eval, ITEM_COLUMN);
        let query = pp(&mut eval, QUERY_COLUMN);
        let sequence = pp(&mut eval, SEQUENCE_COLUMN);
        let tag = pp(&mut eval, TAG_COLUMN);
        let arg_0 = pp(&mut eval, ARG_0_COLUMN);
        let arg_1 = pp(&mut eval, ARG_1_COLUMN);
        let arg_2 = pp(&mut eval, ARG_2_COLUMN);
        let arg_3 = pp(&mut eval, ARG_3_COLUMN);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = segment_mask * segment + binary_mask * binary;
        let one = E::F::from(BaseField::from(1));

        eval.add_constraint(cols.enabler.clone() - row_mask.clone());
        eval.add_constraint((one.clone() - active.clone()) * cols.position.clone());
        eval.add_constraint((one - active.clone()) * cols.offset.clone());
        eval.add_constraint((row_mask.clone() - route_mask.clone()) * cols.position.clone());
        eval.add_constraint((row_mask.clone() - route_mask.clone()) * cols.offset.clone());
        eval.add_constraint(
            (route_mask.clone() - offset_output_mask.clone()) * cols.offset.clone(),
        );

        eval.add_to_relation(RelationEntry::new(
            &self.control_relations.step,
            -E::EF::from(active.clone() * row_mask),
            &[
                verifier_id.clone(),
                sequence,
                tag,
                arg_0,
                arg_1,
                arg_2,
                arg_3,
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.position,
            -E::EF::from(active.clone() * route_mask.clone()),
            &[
                verifier_id.clone(),
                route_kind.clone(),
                item.clone(),
                query.clone(),
                cols.position.clone(),
                cols.offset.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.route_relations.word,
            E::EF::from(active.clone() * route_mask),
            &[
                verifier_id.clone(),
                route_kind.clone(),
                item.clone(),
                query.clone(),
                E::F::from(BaseField::from(FriVerifierRouteField::Position.as_u32())),
                cols.position,
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.route_relations.word,
            E::EF::from(active * offset_output_mask),
            &[
                verifier_id,
                route_kind,
                item,
                query,
                E::F::from(BaseField::from(FriVerifierRouteField::Offset.as_u32())),
                cols.offset,
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates control consumers, atomic route consumers, and scalar producers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
    query_relations: &QueryPositionRelations,
    route_relations: &FriVerifierRouteRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = FriVerifierControlColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[SEGMENT_MASK_COLUMN][row] * segment + pp[BINARY_MASK_COLUMN][row] * binary,
            )
        })
        .collect::<Vec<_>>();
    let numerator = |mask: usize, sign: i32| {
        (0..size)
            .map(|row| active[row] * pp[mask][row] * BaseField::from(sign))
            .collect::<Vec<_>>()
    };
    let control_numerator = numerator(ROW_MASK_COLUMN, -1);
    let query_numerator = numerator(ROUTE_MASK_COLUMN, -1);
    let position_numerator = numerator(ROUTE_MASK_COLUMN, 1);
    let offset_numerator = numerator(OFFSET_OUTPUT_MASK_COLUMN, 1);
    let position_field =
        vec![PackedM31::broadcast(BaseField::from(FriVerifierRouteField::Position.as_u32())); size];
    let offset_field =
        vec![PackedM31::broadcast(BaseField::from(FriVerifierRouteField::Offset.as_u32())); size];
    let control_denominator = combine!(
        control_relations.step,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[SEQUENCE_COLUMN],
            pp[TAG_COLUMN],
            pp[ARG_0_COLUMN],
            pp[ARG_1_COLUMN],
            pp[ARG_2_COLUMN],
            pp[ARG_3_COLUMN]
        ]
    );
    let query_denominator = combine!(
        query_relations.position,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[ROUTE_KIND_COLUMN],
            pp[ITEM_COLUMN],
            pp[QUERY_COLUMN],
            cols.position,
            cols.offset
        ]
    );
    let position_denominator = combine!(
        route_relations.word,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[ROUTE_KIND_COLUMN],
            pp[ITEM_COLUMN],
            pp[QUERY_COLUMN],
            position_field,
            cols.position
        ]
    );
    let offset_denominator = combine!(
        route_relations.word,
        [
            pp[VERIFIER_ID_COLUMN],
            pp[ROUTE_KIND_COLUMN],
            pp[ITEM_COLUMN],
            pp[QUERY_COLUMN],
            offset_field,
            cols.offset
        ]
    );
    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &control_numerator,
        &control_denominator,
        &query_numerator,
        &query_denominator,
        logup
    );
    write_pair!(
        &position_numerator,
        &position_denominator,
        &offset_numerator,
        &offset_denominator,
        logup
    );
    logup.finalize_last()
}

/// Materializes trusted routes from canonical raw queries for the active mode.
pub fn push_fri_verifier_control(
    table: &mut FriVerifierControlTable,
    preprocessed: &FriVerifierControlPreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    query_lanes: [FriVerifierQueryLane<'_>; 3],
    proof_kind: ProofKind,
) -> Result<(), FriVerifierControlError> {
    validate_query_lane_order(&query_lanes)?;
    for (lane, expected) in query_lanes.iter().zip(preprocessed.query_counts) {
        if lane.raw_queries.len() != expected {
            return Err(FriVerifierControlError::RawQueryCountMismatch {
                verifier_id: lane.verifier_id,
                expected,
                actual: lane.raw_queries.len(),
            });
        }
    }
    for row in &preprocessed.rows {
        let active = verifier_is_active(row.verifier_id, proof_kind)?;
        let (position, offset) = if active {
            match row.route_kind {
                Some(kind) => {
                    let raw = query_lanes[row.lane].raw_queries[row.query as usize];
                    query_preprocessed
                        .evaluate_route(row.verifier_id, kind, row.item, row.query, raw)
                        .map_err(FriVerifierControlError::QueryRoute)?
                }
                None => (0, 0),
            }
        } else {
            (0, 0)
        };
        table.push(position, offset);
    }
    Ok(())
}

fn verifier_is_active(
    verifier_id: u32,
    proof_kind: ProofKind,
) -> Result<bool, FriVerifierControlError> {
    match verifier_id {
        SEGMENT_VERIFIER_ID => Ok(proof_kind == ProofKind::SegmentLeaf),
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => {
            Ok(proof_kind == ProofKind::BinaryNode)
        }
        _ => Err(FriVerifierControlError::UnknownVerifierId { verifier_id }),
    }
}

/// Invalid FRI control slice or routed-query assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriVerifierControlError {
    VerifierLaneOrderMismatch {
        expected: u32,
        actual: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    SchemaMismatch {
        verifier_id: u32,
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
    IndexOutOfRange {
        field: &'static str,
        value: usize,
    },
    NonCanonicalDeepQuery {
        expected: u32,
        actual: u32,
    },
    NonCanonicalFoldCoordinate {
        expected_layer: u32,
        expected_query: u32,
        actual_layer: u32,
        actual_query: u32,
    },
    ExtraFoldStep {
        layer: u32,
        query: u32,
    },
    FoldWidthMismatch {
        layer: u32,
        expected: u32,
        actual: u32,
    },
    NonCanonicalLastLayerQuery {
        expected: u32,
        actual: u32,
    },
    DeepStepCountMismatch {
        expected: usize,
        actual: usize,
    },
    FoldStepCountMismatch {
        expected: usize,
        actual: usize,
    },
    LastLayerStepCountMismatch {
        expected: usize,
        actual: usize,
    },
    RawQueryCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    QueryRoute(super::query_position_air::QueryPositionError),
}

impl fmt::Display for FriVerifierControlError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FriVerifierControlError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;
    use crate::v2::kernel::VerifierProgramSpec;
    use crate::v2::protocol::{FixedProofShape, OptionalM31Word, PcsParameters};

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn pcs_parameters() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(3),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        }
    }

    fn shape() -> FixedProofShape<2, 4, 4> {
        FixedProofShape {
            claimed_sum_count: word(7),
            sampled_value_count: word(8),
            queried_value_count: word(12),
            trace_path_count: word(12),
            raw_query_count: word(3),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8), word(8), word(8), word(8)],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        }
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 3, 5, 7, 4)
            .expect("fixture verifier program is valid");
        VerifierControlPlan::new(spec, pcs_parameters(), &shape())
            .expect("fixture verifier plan is valid")
    }

    struct Fixture {
        vm_plan: VerifierControlPlan,
        recursion_plan: VerifierControlPlan,
        profile: FriVerifierProfile,
        query_preprocessed: QueryPositionPreprocessed,
    }

    impl Fixture {
        fn preprocessing(&self) -> FriVerifierControlPreprocessed {
            FriVerifierControlPreprocessed::new([
                FriVerifierControlLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    plan: &self.vm_plan,
                    profile: &self.profile,
                },
                FriVerifierControlLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    plan: &self.recursion_plan,
                    profile: &self.profile,
                },
                FriVerifierControlLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    plan: &self.recursion_plan,
                    profile: &self.profile,
                },
            ])
            .expect("fixture FRI control preprocessing is valid")
        }
    }

    fn fixture() -> Fixture {
        let pcs = pcs_parameters().validate().expect("fixture PCS is valid");
        let profile =
            FriVerifierProfile::from_shape(pcs, &shape()).expect("fixture FRI profile is valid");
        let query_preprocessed = QueryPositionPreprocessed::new(pcs, &shape(), pcs, &shape())
            .expect("fixture query preprocessing is valid");
        Fixture {
            vm_plan: plan(VerifierSchema::Vm),
            recursion_plan: plan(VerifierSchema::Recursion),
            profile,
            query_preprocessed,
        }
    }

    fn assert_constraints(kind: ProofKind) {
        let fixture = fixture();
        let preprocessing = fixture.preprocessing();
        let raw = [word(3), word(91), word(173)];
        let mut table = FriVerifierControlTable::new();
        push_fri_verifier_control(
            &mut table,
            &preprocessing,
            &fixture.query_preprocessed,
            [
                FriVerifierQueryLane {
                    verifier_id: SEGMENT_VERIFIER_ID,
                    raw_queries: &raw,
                },
                FriVerifierQueryLane {
                    verifier_id: LEFT_RECURSION_VERIFIER_ID,
                    raw_queries: &raw,
                },
                FriVerifierQueryLane {
                    verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                    raw_queries: &raw,
                },
            ],
            kind,
        )
        .expect("fixture routes materialize");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let control_relations = ControlRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let route_relations = FriVerifierRouteRelations::dummy();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &control_relations,
            &query_relations,
            &route_relations,
        );
        let log_size = preprocessed[0].domain.log_size();
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size,
            proof_kind: kind,
            control_relations,
            query_relations,
            route_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(eval.log_size),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    #[rstest]
    #[case(ProofKind::SegmentLeaf)]
    #[case(ProofKind::BinaryNode)]
    #[case(ProofKind::EmptyLeaf)]
    fn constraints_hold_in_every_universal_mode(#[case] kind: ProofKind) {
        assert_constraints(kind);
    }

    #[rstest]
    fn preprocessing_owns_every_pcs_arithmetic_step() {
        let fixture = fixture();
        let expected_per_lane = fixture.profile.query_count() * (fixture.profile.layer_count() + 2);
        assert_eq!(fixture.preprocessing().row_count(), expected_per_lane * 3);
    }

    #[rstest]
    fn changed_fold_geometry_is_rejected() {
        let fixture = fixture();
        let changed = FriVerifierProfile::new(8, 1, 0, vec![2, 4, 4, 4], 3)
            .expect("changed profile preserves the total fold count");
        let error = FriVerifierControlPreprocessed::new([
            FriVerifierControlLane {
                verifier_id: SEGMENT_VERIFIER_ID,
                plan: &fixture.vm_plan,
                profile: &changed,
            },
            FriVerifierControlLane {
                verifier_id: LEFT_RECURSION_VERIFIER_ID,
                plan: &fixture.recursion_plan,
                profile: &changed,
            },
            FriVerifierControlLane {
                verifier_id: RIGHT_RECURSION_VERIFIER_ID,
                plan: &fixture.recursion_plan,
                profile: &changed,
            },
        ]);
        assert!(matches!(
            error,
            Err(FriVerifierControlError::FoldWidthMismatch { layer: 0, .. })
        ));
    }
}
