//! Fixed trace-leaf hashing and Merkle leaf anchoring for inner PCS proofs.
//!
//! Every queried trace value appears once in STWO's stable log-size-sorted
//! leaf stream. The leaf sponge is chained from the Poseidon2 Merkle domain,
//! its digest terminates the verifier-scoped authentication path at the exact
//! transcript-derived position, and the same values are exported once for the
//! DEEP quotient. The final row also consumes the mandatory verifier-control
//! step, preventing a proof from omitting any tree/query opening.

use core::fmt;

use air::digest::{Digest8, M31Word};
use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use prover::relations::Relations;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::{BaseField, P};
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::relation;

use super::control_air::{
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, POSEIDON2_VERIFIER_ID,
    RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::merkle_root_air::{MerkleRootError, trace_tree_id};
use super::protocol::{FixedProofShape, PcsParameterError, ProofShapeError};
use super::query_position_air::{
    QueryPositionError, QueryPositionKind, QueryPositionPreprocessed, QueryPositionRelations,
};
use super::wire::MerklePathWire;
use super::wire::ProofKind;
use crate::MerklePathTable;
use crate::merkle_path::{PathStep, push_path_step};
use crate::relations::RecursionRelations;

const RATE: usize = T / 2;
const LEAF_TAG: u32 = 1;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const VERIFIER_ID_COLUMN: usize = 3;
const TREE_COLUMN: usize = 4;
const QUERY_COLUMN: usize = 5;
const TREE_ID_COLUMN: usize = 6;
const TREE_HEIGHT_COLUMN: usize = 7;
const STEP_COLUMN: usize = 8;
const FIRST_MASK_COLUMN: usize = 9;
const LAST_MASK_COLUMN: usize = 10;
const CONTROL_SEQUENCE_COLUMN: usize = 11;
const CONTROL_TAG_COLUMN: usize = 12;
const CONTROL_ARG_0_COLUMN: usize = 13;
const CONTROL_ARG_1_COLUMN: usize = 14;
const CONTROL_ARG_2_COLUMN: usize = 15;
const CONTROL_ARG_3_COLUMN: usize = 16;
const CHUNK_COLUMNS_START: usize = 17;
const CHUNK_COLUMNS_PER_WORD: usize = 3;
const PREPROCESSED_COLUMN_COUNT: usize = CHUNK_COLUMNS_START + RATE * CHUNK_COLUMNS_PER_WORD;

// verifier, tree, query, step, and the complete Poseidon2 state.
relation!(TraceLeafHashStateRelation, 20);
// verifier, tree, original column, raw query, and authenticated value.
relation!(TraceQueryValueRelation, 5);

/// Relations connecting trace leaf hashes to DEEP and their internal sponge.
#[derive(Clone)]
pub struct TraceMerkleRelations {
    pub state: TraceLeafHashStateRelation,
    pub value: TraceQueryValueRelation,
}

impl TraceMerkleRelations {
    pub fn dummy() -> Self {
        Self {
            state: TraceLeafHashStateRelation::dummy(),
            value: TraceQueryValueRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            state: TraceLeafHashStateRelation::draw(channel),
            value: TraceQueryValueRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChunkSource {
    Value { column: u32, flat_index: usize },
    Constant(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    tree: u32,
    query: u32,
    tree_id: u32,
    tree_height: u32,
    step: u32,
    first: bool,
    last: bool,
    control_sequence: u32,
    control_tag: u32,
    control_args: [u32; 4],
    chunks: [ChunkSource; RATE],
}

/// Trusted leaf streams for both segment constituents and recursion children.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceMerklePreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_queried_value_count: usize,
    vm_query_count: usize,
    poseidon2_queried_value_count: usize,
    poseidon2_query_count: usize,
    recursion_queried_value_count: usize,
    recursion_query_count: usize,
}

impl TraceMerklePreprocessed {
    #[allow(clippy::too_many_arguments)]
    pub fn new<
        const VM_TABLES: usize,
        const VM_TREES: usize,
        const VM_FRI_LAYERS: usize,
        const POSEIDON2_TABLES: usize,
        const POSEIDON2_TREES: usize,
        const POSEIDON2_FRI_LAYERS: usize,
        const RECURSION_TABLES: usize,
        const RECURSION_TREES: usize,
        const RECURSION_FRI_LAYERS: usize,
    >(
        vm_plan: &VerifierControlPlan,
        vm_shape: &FixedProofShape<VM_TABLES, VM_TREES, VM_FRI_LAYERS>,
        vm_column_log_sizes: &[Vec<u32>],
        poseidon2_plan: &VerifierControlPlan,
        poseidon2_shape: &FixedProofShape<POSEIDON2_TABLES, POSEIDON2_TREES, POSEIDON2_FRI_LAYERS>,
        poseidon2_column_log_sizes: &[Vec<u32>],
        recursion_plan: &VerifierControlPlan,
        recursion_shape: &FixedProofShape<RECURSION_TABLES, RECURSION_TREES, RECURSION_FRI_LAYERS>,
        recursion_column_log_sizes: &[Vec<u32>],
    ) -> Result<Self, TraceMerkleError> {
        let vm = validate_profile(
            "VM",
            VerifierSchema::Vm,
            vm_plan,
            vm_shape,
            vm_column_log_sizes,
        )?;
        let recursion = validate_profile(
            "recursion",
            VerifierSchema::Recursion,
            recursion_plan,
            recursion_shape,
            recursion_column_log_sizes,
        )?;
        let poseidon2 = validate_profile(
            "Poseidon2",
            VerifierSchema::Poseidon2,
            poseidon2_plan,
            poseidon2_shape,
            poseidon2_column_log_sizes,
        )?;
        let mut rows = Vec::new();
        append_lane_rows(
            &mut rows,
            vm_plan,
            vm_column_log_sizes,
            &vm_shape.tree_heights.map(M31Word::as_u32),
            vm.query_count,
            SEGMENT_VERIFIER_ID,
            1,
            0,
        )?;
        append_lane_rows(
            &mut rows,
            poseidon2_plan,
            poseidon2_column_log_sizes,
            &poseidon2_shape.tree_heights.map(M31Word::as_u32),
            poseidon2.query_count,
            POSEIDON2_VERIFIER_ID,
            1,
            0,
        )?;
        for verifier_id in [LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID] {
            append_lane_rows(
                &mut rows,
                recursion_plan,
                recursion_column_log_sizes,
                &recursion_shape.tree_heights.map(M31Word::as_u32),
                recursion.query_count,
                verifier_id,
                0,
                1,
            )?;
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(TraceMerkleError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(TraceMerkleError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            vm_queried_value_count: vm.queried_value_count,
            vm_query_count: vm.query_count,
            poseidon2_queried_value_count: poseidon2.queried_value_count,
            poseidon2_query_count: poseidon2.query_count,
            recursion_queried_value_count: recursion.queried_value_count,
            recursion_query_count: recursion.query_count,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
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
            columns[VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[TREE_COLUMN][index] = row.tree;
            columns[QUERY_COLUMN][index] = row.query;
            columns[TREE_ID_COLUMN][index] = row.tree_id;
            columns[TREE_HEIGHT_COLUMN][index] = row.tree_height;
            columns[STEP_COLUMN][index] = row.step;
            columns[FIRST_MASK_COLUMN][index] = u32::from(row.first);
            columns[LAST_MASK_COLUMN][index] = u32::from(row.last);
            columns[CONTROL_SEQUENCE_COLUMN][index] = row.control_sequence;
            columns[CONTROL_TAG_COLUMN][index] = row.control_tag;
            columns[CONTROL_ARG_0_COLUMN][index] = row.control_args[0];
            columns[CONTROL_ARG_1_COLUMN][index] = row.control_args[1];
            columns[CONTROL_ARG_2_COLUMN][index] = row.control_args[2];
            columns[CONTROL_ARG_3_COLUMN][index] = row.control_args[3];
            for (slot, source) in row.chunks.into_iter().enumerate() {
                let start = chunk_column(slot);
                match source {
                    ChunkSource::Value { column, .. } => {
                        columns[start][index] = 1;
                        columns[start + 1][index] = column;
                    }
                    ChunkSource::Constant(value) => columns[start + 2][index] = value,
                }
            }
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

#[derive(Clone, Copy)]
struct ValidatedProfile {
    query_count: usize,
    queried_value_count: usize,
}

fn validate_profile<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    profile: &'static str,
    schema: VerifierSchema,
    plan: &VerifierControlPlan,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    column_log_sizes: &[Vec<u32>],
) -> Result<ValidatedProfile, TraceMerkleError> {
    if plan.schema() != schema {
        return Err(TraceMerkleError::SchemaMismatch {
            profile,
            expected: schema,
            actual: plan.schema(),
        });
    }
    let pcs = plan
        .pcs_parameters()
        .validate()
        .map_err(TraceMerkleError::Pcs)?;
    shape.validate(pcs).map_err(|error| match schema {
        VerifierSchema::Vm => TraceMerkleError::VmShape(error),
        VerifierSchema::Recursion => TraceMerkleError::RecursionShape(error),
        VerifierSchema::Poseidon2 => TraceMerkleError::Poseidon2Shape(error),
    })?;
    if column_log_sizes.len() != N_TREES {
        return Err(TraceMerkleError::TreeCountMismatch {
            profile,
            expected: N_TREES,
            actual: column_log_sizes.len(),
        });
    }
    let flattened = column_log_sizes
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    if flattened.len() != N_TABLES {
        return Err(TraceMerkleError::ColumnCountMismatch {
            profile,
            expected: N_TABLES,
            actual: flattened.len(),
        });
    }
    for (column, (expected, actual)) in flattened
        .iter()
        .copied()
        .zip(shape.table_log_sizes)
        .enumerate()
    {
        if expected != actual.as_u32() {
            return Err(TraceMerkleError::ColumnLogSizeMismatch {
                profile,
                column,
                expected,
                actual: actual.as_u32(),
            });
        }
    }
    for (tree, (columns, height)) in column_log_sizes.iter().zip(shape.tree_heights).enumerate() {
        let Some(largest) = columns.iter().copied().max() else {
            if height != M31Word::ZERO {
                return Err(TraceMerkleError::EmptyTreeHasNonzeroHeight {
                    profile,
                    tree,
                    height: height.as_u32(),
                });
            }
            continue;
        };
        let natural = largest
            .checked_add(pcs.config().fri_config.log_blowup_factor)
            .ok_or(TraceMerkleError::ArithmeticOverflow {
                field: "trace tree height",
            })?;
        let expected = pcs.config().lifting_log_size.unwrap_or(natural);
        if expected != height.as_u32() {
            return Err(TraceMerkleError::TreeHeightMismatch {
                profile,
                tree,
                expected,
                actual: height.as_u32(),
            });
        }
    }
    let query_count = pcs.config().fri_config.n_queries;
    let queried_value_count =
        flattened
            .len()
            .checked_mul(query_count)
            .ok_or(TraceMerkleError::ArithmeticOverflow {
                field: "queried value count",
            })?;
    let actual = usize::try_from(shape.queried_value_count.as_u32()).map_err(|_| {
        TraceMerkleError::CountOutOfRange {
            field: "queried values",
            value: shape.queried_value_count.as_u32(),
        }
    })?;
    if queried_value_count != actual {
        return Err(TraceMerkleError::QueriedValueCountMismatch {
            profile,
            expected: queried_value_count,
            actual,
        });
    }
    Ok(ValidatedProfile {
        query_count,
        queried_value_count,
    })
}

#[allow(clippy::too_many_arguments)]
fn append_lane_rows(
    rows: &mut Vec<PreprocessedRow>,
    plan: &VerifierControlPlan,
    column_log_sizes: &[Vec<u32>],
    tree_heights: &[u32],
    query_count: usize,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<(), TraceMerkleError> {
    let mut tree_offset = 0_usize;
    for (tree, (columns, tree_height)) in column_log_sizes.iter().zip(tree_heights).enumerate() {
        if columns.is_empty() {
            continue;
        }
        let tree_u32 = canonical_usize("commitment tree", tree)?;
        let mut order = (0..columns.len()).collect::<Vec<_>>();
        // STWO hashes lifted leaf values in stable ascending log-size order.
        order.sort_by_key(|column| columns[*column]);
        let row_count = columns
            .len()
            .checked_add(1)
            .ok_or(TraceMerkleError::RowCountOverflow)?
            .div_ceil(RATE);
        for query in 0..query_count {
            let query_u32 = canonical_usize("raw query", query)?;
            let control = VerifierStep::VerifyTraceMerklePath {
                tree: tree_u32,
                query: query_u32,
                depth: *tree_height,
            };
            let control_sequence = control_sequence(plan, control)?;
            let encoded = control.encode();
            for step in 0..row_count {
                let mut chunks = [ChunkSource::Constant(0); RATE];
                for (slot, chunk) in chunks.iter_mut().enumerate() {
                    let stream_index = step
                        .checked_mul(RATE)
                        .and_then(|start| start.checked_add(slot))
                        .ok_or(TraceMerkleError::RowCountOverflow)?;
                    *chunk = if let Some(&column) = order.get(stream_index) {
                        let flat_index = tree_offset
                            .checked_add(column)
                            .and_then(|column| column.checked_mul(query_count))
                            .and_then(|base| base.checked_add(query))
                            .ok_or(TraceMerkleError::ArithmeticOverflow {
                                field: "queried value index",
                            })?;
                        ChunkSource::Value {
                            column: canonical_usize("tree column", column)?,
                            flat_index,
                        }
                    } else if stream_index == columns.len() {
                        ChunkSource::Constant(1)
                    } else {
                        ChunkSource::Constant(0)
                    };
                }
                rows.push(PreprocessedRow {
                    segment_mask,
                    binary_mask,
                    verifier_id,
                    tree: tree_u32,
                    query: query_u32,
                    tree_id: trace_tree_id(verifier_id, tree)
                        .map_err(TraceMerkleError::TreeNamespace)?,
                    tree_height: *tree_height,
                    step: canonical_usize("leaf hash step", step)?,
                    first: step == 0,
                    last: step + 1 == row_count,
                    control_sequence,
                    control_tag: encoded.tag(),
                    control_args: encoded.args(),
                    chunks,
                });
            }
        }
        tree_offset =
            tree_offset
                .checked_add(columns.len())
                .ok_or(TraceMerkleError::ArithmeticOverflow {
                    field: "tree column offset",
                })?;
    }
    Ok(())
}

fn control_sequence(
    plan: &VerifierControlPlan,
    expected: VerifierStep,
) -> Result<u32, TraceMerkleError> {
    let mut matches = plan
        .steps()
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, step)| *step == expected);
    let (sequence, _) = matches
        .next()
        .ok_or(TraceMerkleError::ControlStepMissing { expected })?;
    if matches.next().is_some() {
        return Err(TraceMerkleError::DuplicateControlStep { expected });
    }
    canonical_usize("control sequence", sequence)
}

fn canonical_usize(field: &'static str, value: usize) -> Result<u32, TraceMerkleError> {
    let value =
        u32::try_from(value).map_err(|_| TraceMerkleError::IndexOutOfRange { field, value })?;
    M31Word::try_from(value)
        .map(M31Word::as_u32)
        .map_err(|_| TraceMerkleError::IndexNotCanonical { field, value })
}

const fn chunk_column(slot: usize) -> usize {
    CHUNK_COLUMNS_START + slot * CHUNK_COLUMNS_PER_WORD
}

/// Relations used by the macro-generated trace-leaf hash component.
#[derive(Clone)]
pub struct TraceMerkleLeafComponentRelations {
    pub poseidon2_io: air::relations::relation_types::poseidon2_io,
    pub control_step: super::control_air::VerifierStepRelation,
    pub query_position: super::query_position_air::QueryPositionRelation,
    pub state: TraceLeafHashStateRelation,
    pub value: TraceQueryValueRelation,
    pub merkle_node: crate::relations::MerkleNodeRelation,
}

impl TraceMerkleLeafComponentRelations {
    /// Combine leaf hashing, routed positions, control, and path ownership.
    pub fn new(
        vm_relations: &Relations,
        control_relations: &ControlRelations,
        query_relations: &QueryPositionRelations,
        trace_relations: &TraceMerkleRelations,
        recursion_relations: &RecursionRelations,
    ) -> Self {
        Self {
            poseidon2_io: vm_relations.poseidon2_io.clone(),
            control_step: control_relations.step.clone(),
            query_position: query_relations.position.clone(),
            state: trace_relations.state.clone(),
            value: trace_relations.value.clone(),
            merkle_node: recursion_relations.merkle_node.clone(),
        }
    }
}

stwo_macros::define_air_fns! {
    max_degree: 3,
    embedded: [],
    embedded_component: true,
    embedded_enabler_boolean: false,
    embedded_relations: crate::trace_merkle_air::TraceMerkleLeafComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_trace_leaf_row_mask",
        segment_mask: "recursion_trace_leaf_segment_mask",
        binary_mask: "recursion_trace_leaf_binary_mask",
        verifier_id: "recursion_trace_leaf_verifier_id",
        tree: "recursion_trace_leaf_tree",
        query: "recursion_trace_leaf_query",
        tree_id: "recursion_trace_leaf_tree_id",
        tree_height: "recursion_trace_leaf_tree_height",
        step: "recursion_trace_leaf_step",
        first: "recursion_trace_leaf_first_mask",
        last: "recursion_trace_leaf_last_mask",
        control_sequence: "recursion_trace_leaf_control_sequence",
        control_tag: "recursion_trace_leaf_control_tag",
        control_arg_0: "recursion_trace_leaf_control_arg_0",
        control_arg_1: "recursion_trace_leaf_control_arg_1",
        control_arg_2: "recursion_trace_leaf_control_arg_2",
        control_arg_3: "recursion_trace_leaf_control_arg_3",
        chunk_0_source_mask: "recursion_trace_leaf_chunk_0_source_mask",
        chunk_0_column: "recursion_trace_leaf_chunk_0_column",
        chunk_0_constant: "recursion_trace_leaf_chunk_0_constant",
        chunk_1_source_mask: "recursion_trace_leaf_chunk_1_source_mask",
        chunk_1_column: "recursion_trace_leaf_chunk_1_column",
        chunk_1_constant: "recursion_trace_leaf_chunk_1_constant",
        chunk_2_source_mask: "recursion_trace_leaf_chunk_2_source_mask",
        chunk_2_column: "recursion_trace_leaf_chunk_2_column",
        chunk_2_constant: "recursion_trace_leaf_chunk_2_constant",
        chunk_3_source_mask: "recursion_trace_leaf_chunk_3_source_mask",
        chunk_3_column: "recursion_trace_leaf_chunk_3_column",
        chunk_3_constant: "recursion_trace_leaf_chunk_3_constant",
        chunk_4_source_mask: "recursion_trace_leaf_chunk_4_source_mask",
        chunk_4_column: "recursion_trace_leaf_chunk_4_column",
        chunk_4_constant: "recursion_trace_leaf_chunk_4_constant",
        chunk_5_source_mask: "recursion_trace_leaf_chunk_5_source_mask",
        chunk_5_column: "recursion_trace_leaf_chunk_5_column",
        chunk_5_constant: "recursion_trace_leaf_chunk_5_constant",
        chunk_6_source_mask: "recursion_trace_leaf_chunk_6_source_mask",
        chunk_6_column: "recursion_trace_leaf_chunk_6_column",
        chunk_6_constant: "recursion_trace_leaf_chunk_6_constant",
        chunk_7_source_mask: "recursion_trace_leaf_chunk_7_source_mask",
        chunk_7_column: "recursion_trace_leaf_chunk_7_column",
        chunk_7_constant: "recursion_trace_leaf_chunk_7_constant",
    },
    embedded_params: [
        segment_active, binary_active, leaf_tag, trace_position_kind,
    ],

    relation poseidon2_io(32);
    relation control_step(7);
    relation query_position(6);
    relation state(20);
    relation value(5);
    relation merkle_node(11);

    fn trace_merkle_leaf(
        position,
        previous_0, previous_1, previous_2, previous_3, previous_4, previous_5, previous_6, previous_7, previous_8, previous_9, previous_10, previous_11, previous_12, previous_13, previous_14, previous_15,
        chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7,
        output_0, output_1, output_2, output_3, output_4, output_5, output_6, output_7, output_8, output_9, output_10, output_11, output_12, output_13, output_14, output_15,
        row_mask, segment_mask, binary_mask, verifier_id, tree, query, tree_id, tree_height, step, first, last, control_sequence, control_tag, control_arg_0, control_arg_1, control_arg_2, control_arg_3,
        chunk_0_source_mask, chunk_0_column, chunk_0_constant, chunk_1_source_mask, chunk_1_column, chunk_1_constant, chunk_2_source_mask, chunk_2_column, chunk_2_constant, chunk_3_source_mask, chunk_3_column, chunk_3_constant, chunk_4_source_mask, chunk_4_column, chunk_4_constant, chunk_5_source_mask, chunk_5_column, chunk_5_constant, chunk_6_source_mask, chunk_6_column, chunk_6_constant, chunk_7_source_mask, chunk_7_column, chunk_7_constant,
        segment_active, binary_active, leaf_tag, trace_position_kind,
    ) {
        // Trusted lane masks are disjoint subsets of the row mask.
        let active = segment_mask * segment_active + binary_mask * binary_active;
        let final_active = active * last;

        constrain enabler - active;
        constrain (1 - active) * previous_0;
        constrain (1 - active) * previous_1;
        constrain (1 - active) * previous_2;
        constrain (1 - active) * previous_3;
        constrain (1 - active) * previous_4;
        constrain (1 - active) * previous_5;
        constrain (1 - active) * previous_6;
        constrain (1 - active) * previous_7;
        constrain (1 - active) * previous_8;
        constrain (1 - active) * previous_9;
        constrain (1 - active) * previous_10;
        constrain (1 - active) * previous_11;
        constrain (1 - active) * previous_12;
        constrain (1 - active) * previous_13;
        constrain (1 - active) * previous_14;
        constrain (1 - active) * previous_15;
        constrain (1 - active) * chunk_0;
        constrain (1 - active) * chunk_1;
        constrain (1 - active) * chunk_2;
        constrain (1 - active) * chunk_3;
        constrain (1 - active) * chunk_4;
        constrain (1 - active) * chunk_5;
        constrain (1 - active) * chunk_6;
        constrain (1 - active) * chunk_7;
        constrain (1 - active) * output_0;
        constrain (1 - active) * output_1;
        constrain (1 - active) * output_2;
        constrain (1 - active) * output_3;
        constrain (1 - active) * output_4;
        constrain (1 - active) * output_5;
        constrain (1 - active) * output_6;
        constrain (1 - active) * output_7;
        constrain (1 - active) * output_8;
        constrain (1 - active) * output_9;
        constrain (1 - active) * output_10;
        constrain (1 - active) * output_11;
        constrain (1 - active) * output_12;
        constrain (1 - active) * output_13;
        constrain (1 - active) * output_14;
        constrain (1 - active) * output_15;
        constrain (1 - final_active) * position;
        constrain active * first * previous_0;
        constrain active * first * previous_1;
        constrain active * first * previous_2;
        constrain active * first * previous_3;
        constrain active * first * previous_4;
        constrain active * first * previous_5;
        constrain active * first * previous_6;
        constrain active * first * previous_7;
        constrain active * first * previous_8;
        constrain active * first * previous_9;
        constrain active * first * previous_10;
        constrain active * first * previous_11;
        constrain active * first * previous_12;
        constrain active * first * previous_13;
        constrain active * first * previous_14;
        constrain active * first * (previous_15 - leaf_tag);
        constrain active * (1 - chunk_0_source_mask) * (chunk_0 - chunk_0_constant);
        constrain active * (1 - chunk_1_source_mask) * (chunk_1 - chunk_1_constant);
        constrain active * (1 - chunk_2_source_mask) * (chunk_2 - chunk_2_constant);
        constrain active * (1 - chunk_3_source_mask) * (chunk_3 - chunk_3_constant);
        constrain active * (1 - chunk_4_source_mask) * (chunk_4 - chunk_4_constant);
        constrain active * (1 - chunk_5_source_mask) * (chunk_5 - chunk_5_constant);
        constrain active * (1 - chunk_6_source_mask) * (chunk_6 - chunk_6_constant);
        constrain active * (1 - chunk_7_source_mask) * (chunk_7 - chunk_7_constant);

        consume(active) poseidon2_io(
            previous_0 + chunk_0,
            previous_1 + chunk_1,
            previous_2 + chunk_2,
            previous_3 + chunk_3,
            previous_4 + chunk_4,
            previous_5 + chunk_5,
            previous_6 + chunk_6,
            previous_7 + chunk_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        emit(active * chunk_0_source_mask) value(
            verifier_id, tree, chunk_0_column, query, chunk_0,
        );
        emit(active * chunk_1_source_mask) value(
            verifier_id, tree, chunk_1_column, query, chunk_1,
        );
        emit(active * chunk_2_source_mask) value(
            verifier_id, tree, chunk_2_column, query, chunk_2,
        );
        emit(active * chunk_3_source_mask) value(
            verifier_id, tree, chunk_3_column, query, chunk_3,
        );
        emit(active * chunk_4_source_mask) value(
            verifier_id, tree, chunk_4_column, query, chunk_4,
        );
        emit(active * chunk_5_source_mask) value(
            verifier_id, tree, chunk_5_column, query, chunk_5,
        );
        emit(active * chunk_6_source_mask) value(
            verifier_id, tree, chunk_6_column, query, chunk_6,
        );
        emit(active * chunk_7_source_mask) value(
            verifier_id, tree, chunk_7_column, query, chunk_7,
        );
        consume(active * (1 - first)) state(
            verifier_id, tree, query, step,
            previous_0, previous_1, previous_2, previous_3,
            previous_4, previous_5, previous_6, previous_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
        );
        emit(active * (1 - last)) state(
            verifier_id, tree, query, step + 1,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        );
        consume(final_active) query_position(
            verifier_id, trace_position_kind, tree, query, position, 0,
        );
        consume(final_active) merkle_node(
            tree_id, tree_height, position,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
        consume(final_active) control_step(
            verifier_id, control_sequence, control_tag,
            control_arg_0, control_arg_1, control_arg_2, control_arg_3,
        );

        return (
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
        );
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated leaf evaluator for the selected proof kind.
#[allow(clippy::too_many_arguments)]
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    vm_relations: &Relations,
    control_relations: &ControlRelations,
    query_relations: &QueryPositionRelations,
    trace_relations: &TraceMerkleRelations,
    recursion_relations: &RecursionRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        leaf_tag: BaseField::from(LEAF_TAG),
        trace_position_kind: BaseField::from(QueryPositionKind::TraceTree.as_u32()),
        relations: TraceMerkleLeafComponentRelations::new(
            vm_relations,
            control_relations,
            query_relations,
            trace_relations,
            recursion_relations,
        ),
    }
}

/// Generate hash, value, state, position, leaf, and control interactions.
#[allow(clippy::too_many_arguments)]
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    control_relations: &ControlRelations,
    query_relations: &QueryPositionRelations,
    trace_relations: &TraceMerkleRelations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(LEAF_TAG),
        BaseField::from(QueryPositionKind::TraceTree.as_u32()),
        &TraceMerkleLeafComponentRelations::new(
            vm_relations,
            control_relations,
            query_relations,
            trace_relations,
            recursion_relations,
        ),
    )
}

/// Queried values and raw transcript words for one inner proof lane.
#[derive(Clone, Copy)]
pub struct TraceOpeningSet<'a> {
    pub queried_values: &'a [M31Word],
    pub raw_queries: &'a [M31Word],
}

/// Trace-opening witnesses selected by the universal proof kind.
#[derive(Clone, Copy)]
pub enum UniversalTraceOpeningWitness<'a> {
    Segment {
        vm: TraceOpeningSet<'a>,
        poseidon2: TraceOpeningSet<'a>,
    },
    Binary {
        left: TraceOpeningSet<'a>,
        right: TraceOpeningSet<'a>,
    },
    Empty,
}

/// One authenticated leaf endpoint produced by the fixed hash schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraceLeafClaim {
    pub verifier_id: u32,
    pub tree: u32,
    pub query: u32,
    pub tree_id: u32,
    pub height: u32,
    pub position: u32,
    pub digest: [u32; RATE],
}

/// Records every fixed trace leaf sponge and its reused Poseidon2 calls.
pub fn push_trace_merkle_leaves(
    table: &mut TraceMerkleLeafTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &TraceMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalTraceOpeningWitness<'_>,
) -> Result<Vec<TraceLeafClaim>, TraceMerkleError> {
    validate_witness(preprocessed, witness)?;
    let mut state = [0_u32; T];
    let mut claims = Vec::new();
    for row in &preprocessed.rows {
        let opening = select_opening(witness, row.verifier_id)?;
        let Some(opening) = opening else {
            table.push_row(&[0; 1 + 1 + T + RATE + T]);
            continue;
        };
        if row.first {
            state = [0; T];
            state[T - 1] = LEAF_TAG;
        }
        let chunks = row.chunks.map(|source| match source {
            ChunkSource::Value { flat_index, .. } => opening
                .queried_values
                .get(flat_index)
                .copied()
                .map(M31Word::as_u32)
                .ok_or(TraceMerkleError::QueriedValueMissing {
                    verifier_id: row.verifier_id,
                    index: flat_index,
                }),
            ChunkSource::Constant(value) => Ok(value),
        });
        let chunks = transpose_array(chunks)?;
        let position = if row.last {
            let raw = opening.raw_queries.get(row.query as usize).copied().ok_or(
                TraceMerkleError::RawQueryMissing {
                    verifier_id: row.verifier_id,
                    query: row.query,
                },
            )?;
            let (position, offset) = query_preprocessed
                .evaluate_route(
                    row.verifier_id,
                    QueryPositionKind::TraceTree,
                    row.tree,
                    row.query,
                    raw,
                )
                .map_err(TraceMerkleError::QueryPosition)?;
            if offset != 0 {
                return Err(TraceMerkleError::TraceOffsetNotZero {
                    verifier_id: row.verifier_id,
                    tree: row.tree,
                    query: row.query,
                    offset,
                });
            }
            position
        } else {
            0
        };
        let previous = state;
        let mut permutation_input = previous;
        for (slot, chunk) in chunks.iter().copied().enumerate() {
            permutation_input[slot] = (u64::from(permutation_input[slot]) + u64::from(chunk))
                .rem_euclid(u64::from(P)) as u32;
        }
        let output = poseidon2_traced_state(poseidon2, permutation_input, false, true);
        let mut values = Vec::with_capacity(1 + 1 + T + RATE + T);
        values.extend([1, position]);
        values.extend(previous);
        values.extend(chunks);
        values.extend(output);
        table.push_row(&values);
        if row.last {
            claims.push(TraceLeafClaim {
                verifier_id: row.verifier_id,
                tree: row.tree,
                query: row.query,
                tree_id: row.tree_id,
                height: row.tree_height,
                position,
                digest: output[..RATE]
                    .try_into()
                    .expect("Merkle digest is one rate block"),
            });
        }
        state = output;
    }
    Ok(claims)
}

/// Roots and bottom-up sibling paths for one fixed inner proof.
#[derive(Clone, Copy)]
pub struct TracePathSet<'a, const MAX_DEPTH: usize> {
    pub roots: &'a [Digest8],
    pub paths: &'a [MerklePathWire<MAX_DEPTH>],
}

/// Path witnesses selected by the public universal proof kind.
#[derive(Clone, Copy)]
pub enum UniversalTracePathWitness<'a, const MAX_DEPTH: usize> {
    Segment {
        vm: TracePathSet<'a, MAX_DEPTH>,
        poseidon2: TracePathSet<'a, MAX_DEPTH>,
    },
    Binary {
        left: TracePathSet<'a, MAX_DEPTH>,
        right: TracePathSet<'a, MAX_DEPTH>,
    },
    Empty,
}

/// Connects every trace leaf to its transcript root through the shared path AIR.
pub fn push_trace_merkle_paths<const MAX_DEPTH: usize>(
    table: &mut MerklePathTable,
    poseidon2: &mut Poseidon2Table,
    claims: &[TraceLeafClaim],
    witness: UniversalTracePathWitness<'_, MAX_DEPTH>,
) -> Result<(), TraceMerkleError> {
    let expected_claims = match witness {
        UniversalTracePathWitness::Segment { vm, poseidon2 } => {
            let vm_count = validate_path_set(
                SEGMENT_VERIFIER_ID,
                claims,
                vm,
                claims
                    .iter()
                    .filter(|claim| claim.verifier_id == SEGMENT_VERIFIER_ID),
            )?;
            let poseidon2_count = validate_path_set(
                POSEIDON2_VERIFIER_ID,
                claims,
                poseidon2,
                claims
                    .iter()
                    .filter(|claim| claim.verifier_id == POSEIDON2_VERIFIER_ID),
            )?;
            vm_count
                .checked_add(poseidon2_count)
                .ok_or(TraceMerkleError::RowCountOverflow)?
        }
        UniversalTracePathWitness::Binary { left, right } => {
            let left_count = validate_path_set(
                LEFT_RECURSION_VERIFIER_ID,
                claims,
                left,
                claims
                    .iter()
                    .filter(|claim| claim.verifier_id == LEFT_RECURSION_VERIFIER_ID),
            )?;
            let right_count = validate_path_set(
                RIGHT_RECURSION_VERIFIER_ID,
                claims,
                right,
                claims
                    .iter()
                    .filter(|claim| claim.verifier_id == RIGHT_RECURSION_VERIFIER_ID),
            )?;
            left_count
                .checked_add(right_count)
                .ok_or(TraceMerkleError::RowCountOverflow)?
        }
        UniversalTracePathWitness::Empty => 0,
    };
    if claims.len() != expected_claims {
        return Err(TraceMerkleError::LeafClaimCountMismatch {
            expected: expected_claims,
            actual: claims.len(),
        });
    }

    for claim in claims {
        let paths = select_paths(witness, claim.verifier_id)?.ok_or(
            TraceMerkleError::ActivePathSetMissing {
                verifier_id: claim.verifier_id,
            },
        )?;
        let active_trees = claims
            .iter()
            .filter(|candidate| candidate.verifier_id == claim.verifier_id)
            .map(|candidate| candidate.tree)
            .max()
            .map_or(0, |_| {
                claims
                    .iter()
                    .filter(|candidate| {
                        candidate.verifier_id == claim.verifier_id && candidate.query == 0
                    })
                    .count()
            });
        if active_trees == 0 || paths.paths.len() % active_trees != 0 {
            return Err(TraceMerkleError::InvalidPathLayout {
                verifier_id: claim.verifier_id,
                roots: paths.roots.len(),
                paths: paths.paths.len(),
            });
        }
        let query_count = paths.paths.len() / active_trees;
        let tree_rank = claims
            .iter()
            .filter(|candidate| {
                candidate.verifier_id == claim.verifier_id
                    && candidate.query == 0
                    && candidate.tree < claim.tree
            })
            .count();
        let path_index = tree_rank
            .checked_mul(query_count)
            .and_then(|base| base.checked_add(claim.query as usize))
            .ok_or(TraceMerkleError::ArithmeticOverflow {
                field: "trace path index",
            })?;
        let path = paths
            .paths
            .get(path_index)
            .ok_or(TraceMerkleError::TracePathMissing {
                verifier_id: claim.verifier_id,
                tree: claim.tree,
                query: claim.query,
            })?;
        if path.active_depth() != claim.height {
            return Err(TraceMerkleError::TracePathDepthMismatch {
                verifier_id: claim.verifier_id,
                tree: claim.tree,
                query: claim.query,
                expected: claim.height,
                actual: path.active_depth(),
            });
        }
        let mut child = claim.digest;
        for level in 0..claim.height {
            let sibling = path.siblings()[level as usize].words().map(M31Word::as_u32);
            let depth = claim.height - level - 1;
            child = push_path_step(
                table,
                poseidon2,
                claim.tree_id,
                depth,
                claim.position >> (level + 1),
                child,
                PathStep {
                    direction: (claim.position >> level) & 1,
                    sibling,
                },
                false,
            );
        }
        let expected_root = paths
            .roots
            .get(claim.tree as usize)
            .ok_or(TraceMerkleError::TraceRootMissing {
                verifier_id: claim.verifier_id,
                tree: claim.tree,
            })?
            .words()
            .map(M31Word::as_u32);
        if child != expected_root {
            return Err(TraceMerkleError::TracePathRootMismatch {
                verifier_id: claim.verifier_id,
                tree: claim.tree,
                query: claim.query,
            });
        }
    }
    Ok(())
}

fn validate_path_set<'a, const MAX_DEPTH: usize>(
    verifier_id: u32,
    all_claims: &[TraceLeafClaim],
    paths: TracePathSet<'_, MAX_DEPTH>,
    lane_claims: impl Iterator<Item = &'a TraceLeafClaim>,
) -> Result<usize, TraceMerkleError> {
    let claim_count = lane_claims.count();
    if paths.paths.len() != claim_count {
        return Err(TraceMerkleError::TracePathCountMismatch {
            verifier_id,
            expected: claim_count,
            actual: paths.paths.len(),
        });
    }
    let tree_count = all_claims
        .iter()
        .filter(|claim| claim.verifier_id == verifier_id)
        .map(|claim| claim.tree)
        .max()
        .map_or(0, |tree| tree as usize + 1);
    if paths.roots.len() != tree_count {
        return Err(TraceMerkleError::TraceRootCountMismatch {
            verifier_id,
            expected: tree_count,
            actual: paths.roots.len(),
        });
    }
    Ok(claim_count)
}

fn select_paths<const MAX_DEPTH: usize>(
    witness: UniversalTracePathWitness<'_, MAX_DEPTH>,
    verifier_id: u32,
) -> Result<Option<TracePathSet<'_, MAX_DEPTH>>, TraceMerkleError> {
    match (witness, verifier_id) {
        (UniversalTracePathWitness::Segment { vm, .. }, SEGMENT_VERIFIER_ID) => Ok(Some(vm)),
        (UniversalTracePathWitness::Segment { poseidon2, .. }, POSEIDON2_VERIFIER_ID) => {
            Ok(Some(poseidon2))
        }
        (UniversalTracePathWitness::Binary { left, .. }, LEFT_RECURSION_VERIFIER_ID) => {
            Ok(Some(left))
        }
        (UniversalTracePathWitness::Binary { right, .. }, RIGHT_RECURSION_VERIFIER_ID) => {
            Ok(Some(right))
        }
        (UniversalTracePathWitness::Empty, SEGMENT_VERIFIER_ID)
        | (UniversalTracePathWitness::Empty, POSEIDON2_VERIFIER_ID)
        | (UniversalTracePathWitness::Empty, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalTracePathWitness::Empty, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalTracePathWitness::Segment { .. }, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalTracePathWitness::Segment { .. }, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalTracePathWitness::Binary { .. }, SEGMENT_VERIFIER_ID)
        | (UniversalTracePathWitness::Binary { .. }, POSEIDON2_VERIFIER_ID) => Ok(None),
        (_, verifier_id) => Err(TraceMerkleError::UnknownVerifierId { verifier_id }),
    }
}

fn transpose_array<T, E, const N: usize>(values: [Result<T, E>; N]) -> Result<[T; N], E> {
    let values = values.into_iter().collect::<Result<Vec<_>, _>>()?;
    Ok(values
        .try_into()
        .unwrap_or_else(|_| unreachable!("array collection preserves its fixed length")))
}

fn validate_witness(
    preprocessed: &TraceMerklePreprocessed,
    witness: UniversalTraceOpeningWitness<'_>,
) -> Result<(), TraceMerkleError> {
    match witness {
        UniversalTraceOpeningWitness::Segment { vm, poseidon2 } => {
            validate_opening(
                SEGMENT_VERIFIER_ID,
                preprocessed.vm_queried_value_count,
                preprocessed.vm_query_count,
                vm,
            )?;
            validate_opening(
                POSEIDON2_VERIFIER_ID,
                preprocessed.poseidon2_queried_value_count,
                preprocessed.poseidon2_query_count,
                poseidon2,
            )
        }
        UniversalTraceOpeningWitness::Binary { left, right } => {
            validate_opening(
                LEFT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_queried_value_count,
                preprocessed.recursion_query_count,
                left,
            )?;
            validate_opening(
                RIGHT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_queried_value_count,
                preprocessed.recursion_query_count,
                right,
            )
        }
        UniversalTraceOpeningWitness::Empty => Ok(()),
    }
}

fn validate_opening(
    verifier_id: u32,
    expected_values: usize,
    expected_queries: usize,
    opening: TraceOpeningSet<'_>,
) -> Result<(), TraceMerkleError> {
    if opening.queried_values.len() != expected_values {
        return Err(TraceMerkleError::QueriedValueCountMismatchForWitness {
            verifier_id,
            expected: expected_values,
            actual: opening.queried_values.len(),
        });
    }
    if opening.raw_queries.len() != expected_queries {
        return Err(TraceMerkleError::RawQueryCountMismatch {
            verifier_id,
            expected: expected_queries,
            actual: opening.raw_queries.len(),
        });
    }
    Ok(())
}

fn select_opening(
    witness: UniversalTraceOpeningWitness<'_>,
    verifier_id: u32,
) -> Result<Option<TraceOpeningSet<'_>>, TraceMerkleError> {
    match (witness, verifier_id) {
        (UniversalTraceOpeningWitness::Segment { vm, .. }, SEGMENT_VERIFIER_ID) => Ok(Some(vm)),
        (UniversalTraceOpeningWitness::Segment { poseidon2, .. }, POSEIDON2_VERIFIER_ID) => {
            Ok(Some(poseidon2))
        }
        (UniversalTraceOpeningWitness::Binary { left, .. }, LEFT_RECURSION_VERIFIER_ID) => {
            Ok(Some(left))
        }
        (UniversalTraceOpeningWitness::Binary { right, .. }, RIGHT_RECURSION_VERIFIER_ID) => {
            Ok(Some(right))
        }
        (UniversalTraceOpeningWitness::Empty, SEGMENT_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Empty, POSEIDON2_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Empty, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Empty, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Segment { .. }, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Segment { .. }, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Binary { .. }, SEGMENT_VERIFIER_ID)
        | (UniversalTraceOpeningWitness::Binary { .. }, POSEIDON2_VERIFIER_ID) => Ok(None),
        (_, verifier_id) => Err(TraceMerkleError::UnknownVerifierId { verifier_id }),
    }
}

/// Invalid trace layout, control schedule, query route, or witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceMerkleError {
    Pcs(PcsParameterError),
    VmShape(ProofShapeError),
    Poseidon2Shape(ProofShapeError),
    RecursionShape(ProofShapeError),
    TreeNamespace(MerkleRootError),
    QueryPosition(QueryPositionError),
    SchemaMismatch {
        profile: &'static str,
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    TreeCountMismatch {
        profile: &'static str,
        expected: usize,
        actual: usize,
    },
    ColumnCountMismatch {
        profile: &'static str,
        expected: usize,
        actual: usize,
    },
    ColumnLogSizeMismatch {
        profile: &'static str,
        column: usize,
        expected: u32,
        actual: u32,
    },
    EmptyTreeHasNonzeroHeight {
        profile: &'static str,
        tree: usize,
        height: u32,
    },
    TreeHeightMismatch {
        profile: &'static str,
        tree: usize,
        expected: u32,
        actual: u32,
    },
    QueriedValueCountMismatch {
        profile: &'static str,
        expected: usize,
        actual: usize,
    },
    CountOutOfRange {
        field: &'static str,
        value: u32,
    },
    ControlStepMissing {
        expected: VerifierStep,
    },
    DuplicateControlStep {
        expected: VerifierStep,
    },
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    ArithmeticOverflow {
        field: &'static str,
    },
    IndexOutOfRange {
        field: &'static str,
        value: usize,
    },
    IndexNotCanonical {
        field: &'static str,
        value: u32,
    },
    QueriedValueCountMismatchForWitness {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    RawQueryCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    QueriedValueMissing {
        verifier_id: u32,
        index: usize,
    },
    RawQueryMissing {
        verifier_id: u32,
        query: u32,
    },
    TraceOffsetNotZero {
        verifier_id: u32,
        tree: u32,
        query: u32,
        offset: u32,
    },
    LeafClaimCountMismatch {
        expected: usize,
        actual: usize,
    },
    ActivePathSetMissing {
        verifier_id: u32,
    },
    InvalidPathLayout {
        verifier_id: u32,
        roots: usize,
        paths: usize,
    },
    TracePathCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    TraceRootCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    TracePathMissing {
        verifier_id: u32,
        tree: u32,
        query: u32,
    },
    TracePathDepthMismatch {
        verifier_id: u32,
        tree: u32,
        query: u32,
        expected: u32,
        actual: u32,
    },
    TraceRootMissing {
        verifier_id: u32,
        tree: u32,
    },
    TracePathRootMismatch {
        verifier_id: u32,
        tree: u32,
        query: u32,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
}

impl fmt::Display for TraceMerkleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for TraceMerkleError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use prover::poseidon2_channel::{Poseidon2M31Hash, Poseidon2M31MerkleHasher};
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::kernel::VerifierProgramSpec;
    use crate::protocol::{OptionalM31Word, PcsParameters, ValidatedPcsParameters};

    const TABLE_COUNT: usize = 6;
    const TREE_COUNT: usize = 4;
    const FRI_LAYER_COUNT: usize = 2;
    const QUERY_COUNT: usize = 2;
    const QUERY_VALUE_COUNT: usize = TABLE_COUNT * QUERY_COUNT;

    #[derive(Clone, Copy)]
    enum LeafTamper {
        InitialCapacity,
        EndMarker,
        InactiveState,
    }

    fn pcs_parameters() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: M31Word::from(1_u16),
            fri_n_queries: M31Word::from(QUERY_COUNT as u16),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: M31Word::from(4_u16),
            lifting_log_size: OptionalM31Word::None,
        }
    }

    fn pcs() -> ValidatedPcsParameters {
        pcs_parameters()
            .validate()
            .expect("fixture PCS parameters are valid")
    }

    fn shape() -> FixedProofShape<TABLE_COUNT, TREE_COUNT, FRI_LAYER_COUNT> {
        FixedProofShape {
            claimed_sum_count: M31Word::from(1_u16),
            sampled_value_count: M31Word::from(1_u16),
            queried_value_count: M31Word::from(QUERY_VALUE_COUNT as u16),
            trace_path_count: M31Word::from((TREE_COUNT * QUERY_COUNT) as u16),
            raw_query_count: M31Word::from(QUERY_COUNT as u16),
            last_layer_coefficient_count: M31Word::from(1_u16),
            table_log_sizes: [5_u16, 4, 7, 6, 7, 7].map(M31Word::from),
            tree_heights: [6_u16, 8, 8, 8].map(M31Word::from),
            fri_layer_fold_widths: [16_u16, 8].map(M31Word::from),
            fri_layer_tree_heights: [6_u16, 2].map(M31Word::from),
        }
    }

    fn column_log_sizes() -> Vec<Vec<u32>> {
        vec![vec![5, 4], vec![7, 6], vec![7], vec![7]]
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 1, 1, 1, 1)
            .expect("fixture verifier program is valid");
        VerifierControlPlan::new(spec, pcs_parameters(), &shape())
            .expect("fixture verifier plan is valid")
    }

    fn preprocessing() -> (TraceMerklePreprocessed, QueryPositionPreprocessed) {
        let vm = plan(VerifierSchema::Vm);
        let poseidon2 = plan(VerifierSchema::Poseidon2);
        let recursion = plan(VerifierSchema::Recursion);
        let columns = column_log_sizes();
        let trace = TraceMerklePreprocessed::new(
            &vm,
            &shape(),
            &columns,
            &poseidon2,
            &shape(),
            &columns,
            &recursion,
            &shape(),
            &columns,
        )
        .expect("fixture trace Merkle geometry is valid");
        let query =
            QueryPositionPreprocessed::new(pcs(), &shape(), pcs(), &shape(), pcs(), &shape())
                .expect("fixture query geometry is valid");
        (trace, query)
    }

    fn values(seed: u16) -> [M31Word; QUERY_VALUE_COUNT] {
        core::array::from_fn(|index| M31Word::from(seed + index as u16))
    }

    fn queries(seed: u16) -> [M31Word; QUERY_COUNT] {
        [M31Word::from(seed), M31Word::from(seed + 1)]
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new(core::array::from_fn(|index| {
            M31Word::from(seed + index as u16)
        }))
    }

    fn materialize(
        kind: ProofKind,
    ) -> (
        TraceMerklePreprocessed,
        QueryPositionPreprocessed,
        TraceMerkleLeafTable,
        Poseidon2Table,
    ) {
        let (preprocessing, query_preprocessing) = preprocessing();
        let vm_values = values(10);
        let vm_queries = queries(183);
        let left_values = values(100);
        let left_queries = queries(77);
        let right_values = values(200);
        let right_queries = queries(99);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalTraceOpeningWitness::Segment {
                vm: TraceOpeningSet {
                    queried_values: &vm_values,
                    raw_queries: &vm_queries,
                },
                poseidon2: TraceOpeningSet {
                    queried_values: &vm_values,
                    raw_queries: &vm_queries,
                },
            },
            ProofKind::BinaryNode => UniversalTraceOpeningWitness::Binary {
                left: TraceOpeningSet {
                    queried_values: &left_values,
                    raw_queries: &left_queries,
                },
                right: TraceOpeningSet {
                    queried_values: &right_values,
                    raw_queries: &right_queries,
                },
            },
            ProofKind::EmptyLeaf => UniversalTraceOpeningWitness::Empty,
        };
        let mut table = TraceMerkleLeafTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        let _claims = push_trace_merkle_leaves(
            &mut table,
            &mut poseidon2,
            &preprocessing,
            &query_preprocessing,
            witness,
        )
        .expect("fixture trace leaves materialize");
        (preprocessing, query_preprocessing, table, poseidon2)
    }

    fn assert_constraints(kind: ProofKind, tamper: Option<LeafTamper>) {
        let (preprocessing, _, mut table, _) = materialize(kind);
        match tamper {
            Some(LeafTamper::InitialCapacity) => table.previous_15[0] = 0,
            Some(LeafTamper::EndMarker) => table.chunk_2[0] = 0,
            Some(LeafTamper::InactiveState) => table.previous_0[0] = 1,
            None => {}
        }
        let vm_relations = Relations::dummy();
        let control_relations = ControlRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let trace_relations = TraceMerkleRelations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &control_relations,
            &query_relations,
            &trace_relations,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &vm_relations,
            &control_relations,
            &query_relations,
            &trace_relations,
            &recursion_relations,
        );
        assert_constraints_on_polys(
            &polys,
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
    fn every_universal_mode_satisfies_trace_leaf_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, None);
    }

    #[rstest]
    #[case::initial_capacity(LeafTamper::InitialCapacity)]
    #[case::end_marker(LeafTamper::EndMarker)]
    #[should_panic]
    fn trace_leaf_domain_and_padding_cannot_change(#[case] tamper: LeafTamper) {
        assert_constraints(ProofKind::SegmentLeaf, Some(tamper));
    }

    #[test]
    #[should_panic]
    fn inactive_trace_leaf_state_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, Some(LeafTamper::InactiveState));
    }

    #[test]
    fn trace_leaf_hash_matches_stwo_stable_column_order() {
        let (_, _, table, _) = materialize(ProofKind::SegmentLeaf);
        let queried_values = values(10);
        let mut hasher = Poseidon2M31MerkleHasher::default();
        hasher.update_leaf(&[
            BaseField::from(queried_values[2].as_u32()),
            BaseField::from(queried_values[0].as_u32()),
        ]);
        let expected = hasher.finalize();
        let actual = Poseidon2M31Hash([
            table.output_0[0],
            table.output_1[0],
            table.output_2[0],
            table.output_3[0],
            table.output_4[0],
            table.output_5[0],
            table.output_6[0],
            table.output_7[0],
        ]);
        assert_eq!(actual, expected);
    }

    fn table_chunk(table: &TraceMerkleLeafTable, slot: usize, row: usize) -> u32 {
        match slot {
            0 => table.chunk_0[row],
            1 => table.chunk_1[row],
            2 => table.chunk_2[row],
            3 => table.chunk_3[row],
            4 => table.chunk_4[row],
            5 => table.chunk_5[row],
            6 => table.chunk_6[row],
            7 => table.chunk_7[row],
            _ => unreachable!("leaf chunk slot is rate-bounded"),
        }
    }

    fn table_digest(table: &TraceMerkleLeafTable, row: usize) -> [u32; RATE] {
        [
            table.output_0[row],
            table.output_1[row],
            table.output_2[row],
            table.output_3[row],
            table.output_4[row],
            table.output_5[row],
            table.output_6[row],
            table.output_7[row],
        ]
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    fn trace_leaf_relations_close_exactly(#[case] kind: ProofKind) {
        let (preprocessing, _, table, poseidon2) = materialize(kind);
        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let control_relations = ControlRelations::draw(&mut channel);
        let query_relations = QueryPositionRelations::draw(&mut channel);
        let trace_relations = TraceMerkleRelations::draw(&mut channel);
        let recursion_relations = RecursionRelations::draw(&mut channel);
        let external = preprocessing
            .rows
            .iter()
            .enumerate()
            .filter(|(_, row)| match kind {
                ProofKind::SegmentLeaf => row.segment_mask == 1,
                ProofKind::BinaryNode => row.binary_mask == 1,
                ProofKind::EmptyLeaf => false,
            })
            .fold(QM31::zero(), |sum, (row_index, row)| {
                let value_terms =
                    row.chunks
                        .iter()
                        .enumerate()
                        .fold(QM31::zero(), |sum, (slot, source)| {
                            let ChunkSource::Value { column, .. } = source else {
                                return sum;
                            };
                            let denominator: QM31 = trace_relations.value.combine(&[
                                M31::from(row.verifier_id),
                                M31::from(row.tree),
                                M31::from(*column),
                                M31::from(row.query),
                                M31::from(table_chunk(&table, slot, row_index)),
                            ]);
                            sum - denominator.inverse()
                        });
                if !row.last {
                    return sum + value_terms;
                }
                let position = table.position[row_index];
                let query_denominator: QM31 = query_relations.position.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(QueryPositionKind::TraceTree.as_u32()),
                    M31::from(row.tree),
                    M31::from(row.query),
                    M31::from(position),
                    M31::from(0),
                ]);
                let digest = table_digest(&table, row_index);
                let mut leaf_tuple = vec![
                    M31::from(row.tree_id),
                    M31::from(row.tree_height),
                    M31::from(position),
                ];
                leaf_tuple.extend(digest.map(M31::from));
                let leaf_denominator: QM31 = recursion_relations.merkle_node.combine(&leaf_tuple);
                let control_denominator: QM31 = control_relations.step.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(row.control_sequence),
                    M31::from(row.control_tag),
                    M31::from(row.control_args[0]),
                    M31::from(row.control_args[1]),
                    M31::from(row.control_args[2]),
                    M31::from(row.control_args[3]),
                ]);
                sum + value_terms
                    + query_denominator.inverse()
                    + leaf_denominator.inverse()
                    + control_denominator.inverse()
            });
        let trace = table.into_witness();
        let (_, leaf_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            kind,
            &vm_relations,
            &control_relations,
            &query_relations,
            &trace_relations,
            &recursion_relations,
        );
        let poseidon_trace = poseidon2.into_witness();
        let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
            &poseidon_trace,
            &vm_relations,
        );
        assert!((leaf_sum + poseidon_sum + external).is_zero());
    }

    fn push_duplicate_trace_paths(tamper_root: bool) -> Result<(), TraceMerkleError> {
        const MAX_DEPTH: usize = 8;

        let (preprocessing, query_preprocessing) = preprocessing();
        let queried_values =
            [10_u16, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15].map(M31Word::from);
        let raw_queries = [M31Word::from(183_u16); QUERY_COUNT];
        let mut leaf_table = TraceMerkleLeafTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        let claims = push_trace_merkle_leaves(
            &mut leaf_table,
            &mut poseidon2,
            &preprocessing,
            &query_preprocessing,
            UniversalTraceOpeningWitness::Segment {
                vm: TraceOpeningSet {
                    queried_values: &queried_values,
                    raw_queries: &raw_queries,
                },
                poseidon2: TraceOpeningSet {
                    queried_values: &queried_values,
                    raw_queries: &raw_queries,
                },
            },
        )?;
        let mut roots = [[Digest8::ZERO; TREE_COUNT]; 2];
        let mut paths: [Vec<_>; 2] =
            core::array::from_fn(|_| Vec::with_capacity(TREE_COUNT * QUERY_COUNT));
        for claim in &claims {
            let lane = usize::from(claim.verifier_id == POSEIDON2_VERIFIER_ID);
            let mut siblings = [Digest8::ZERO; MAX_DEPTH];
            let mut child = Poseidon2M31Hash(claim.digest);
            for level in 0..claim.height {
                let sibling = digest(1_000 + claim.tree as u16 * 100 + level as u16 * 10);
                siblings[level as usize] = sibling;
                let sibling = Poseidon2M31Hash(sibling.words().map(M31Word::as_u32));
                let children = if (claim.position >> level) & 1 == 0 {
                    (child, sibling)
                } else {
                    (sibling, child)
                };
                child = Poseidon2M31MerkleHasher::hash_children(children);
            }
            let root = Digest8::try_from(child.0).expect("Poseidon2 root limbs are canonical");
            if claim.query == 0 {
                roots[lane][claim.tree as usize] = root;
            } else if roots[lane][claim.tree as usize] != root {
                return Err(TraceMerkleError::TracePathRootMismatch {
                    verifier_id: claim.verifier_id,
                    tree: claim.tree,
                    query: claim.query,
                });
            }
            paths[lane].push(
                MerklePathWire::new(claim.height, siblings)
                    .expect("fixture path fills the declared depth"),
            );
        }
        if tamper_root {
            roots[0][0] = digest(9_000);
        }
        push_trace_merkle_paths(
            &mut MerklePathTable::new(),
            &mut poseidon2,
            &claims,
            UniversalTracePathWitness::Segment {
                vm: TracePathSet {
                    roots: &roots[0],
                    paths: &paths[0],
                },
                poseidon2: TracePathSet {
                    roots: &roots[1],
                    paths: &paths[1],
                },
            },
        )
    }

    #[test]
    fn duplicate_trace_query_paths_reach_one_shared_root() {
        assert_eq!(push_duplicate_trace_paths(false), Ok(()));
    }

    #[test]
    fn trace_path_root_substitution_is_rejected() {
        assert_eq!(
            push_duplicate_trace_paths(true),
            Err(TraceMerkleError::TracePathRootMismatch {
                verifier_id: SEGMENT_VERIFIER_ID,
                tree: 0,
                query: 0,
            })
        );
    }
}
