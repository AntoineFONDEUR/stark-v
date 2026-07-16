//! Fixed packed-subtree authentication for every FRI query.
//!
//! STWO authenticates a complete `2^fold_step` subset before each fold. FRI
//! layers wider than two pack four secure evaluations into one Merkle leaf;
//! the leaves inside the queried subset and their common subtree are rebuilt
//! locally, while the proof carries only the siblings above that subtree.
//! Trusted preprocessing fixes every leaf word, internal node, query route,
//! verifier-control step, and tree namespace for the segment and child lanes.

use core::fmt;
use std::collections::BTreeMap;

use air::digest::{Digest8, M31Word};
use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use num_traits::One;
use prover::relations::Relations;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::{BaseField, P};
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::{CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::core::vcs_lifted::verifier::PACKED_LEAF_SIZE;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::m31::PackedM31;
use stwo::prover::backend::simd::qm31::PackedQM31;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, Relation, RelationEntry,
    relation,
};
use stwo_macros::define_component_tables;

use super::control_air::{
    ControlRelations, LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::kernel::{VerifierControlPlan, VerifierSchema, VerifierStep};
use super::merkle_root_air::{MerkleRootError, fri_tree_id};
use super::protocol::{FixedProofShape, PcsParameterError, ProofShapeError, fri_query_path_depth};
use super::query_position_air::{
    QueryPositionError, QueryPositionKind, QueryPositionPreprocessed, QueryPositionRelations,
};
use super::wire::ProofKind;
use super::wire::{FriLayerWire, Qm31Wire};
use crate::MerklePathTable;
use crate::merkle_path::{PathStep, push_path_step};
use crate::relations::RecursionRelations;

const RATE: usize = T / 2;
const DIGEST_WORDS: usize = RATE;
const SECURE_WORDS: usize = 4;
const LEAF_TAG: u32 = 1;
const MIN_LOG_SIZE: u32 = 4;

type LeafChunkMetadata<F> = [(F, F, F, F); RATE];

const LEAF_ROW_MASK_COLUMN: usize = 0;
const LEAF_SEGMENT_MASK_COLUMN: usize = 1;
const LEAF_BINARY_MASK_COLUMN: usize = 2;
const LEAF_VERIFIER_ID_COLUMN: usize = 3;
const LEAF_LAYER_COLUMN: usize = 4;
const LEAF_QUERY_COLUMN: usize = 5;
const LEAF_PACKED_INDEX_COLUMN: usize = 6;
const LEAF_COUNT_COLUMN: usize = 7;
const LEAF_LOCAL_ROOT_MASK_COLUMN: usize = 8;
const LEAF_TREE_ID_COLUMN: usize = 9;
const LEAF_TREE_HEIGHT_COLUMN: usize = 10;
const LEAF_STEP_COLUMN: usize = 11;
const LEAF_FIRST_MASK_COLUMN: usize = 12;
const LEAF_LAST_MASK_COLUMN: usize = 13;
const LEAF_CHUNKS_START: usize = 14;
const LEAF_CHUNK_COLUMNS: usize = 4;
const LEAF_PREPROCESSED_COLUMN_COUNT: usize = LEAF_CHUNKS_START + RATE * LEAF_CHUNK_COLUMNS;

const NODE_ROW_MASK_COLUMN: usize = 0;
const NODE_SEGMENT_MASK_COLUMN: usize = 1;
const NODE_BINARY_MASK_COLUMN: usize = 2;
const NODE_TREE_ID_COLUMN: usize = 3;
const NODE_DEPTH_COLUMN: usize = 4;
const NODE_LOCAL_ROOT_MASK_COLUMN: usize = 5;
const NODE_PREPROCESSED_COLUMN_COUNT: usize = 6;

const ANCHOR_ROW_MASK_COLUMN: usize = 0;
const ANCHOR_SEGMENT_MASK_COLUMN: usize = 1;
const ANCHOR_BINARY_MASK_COLUMN: usize = 2;
const ANCHOR_VERIFIER_ID_COLUMN: usize = 3;
const ANCHOR_LAYER_COLUMN: usize = 4;
const ANCHOR_QUERY_COLUMN: usize = 5;
const ANCHOR_TREE_ID_COLUMN: usize = 6;
const ANCHOR_PATH_DEPTH_COLUMN: usize = 7;
const ANCHOR_LEAF_COUNT_COLUMN: usize = 8;
const ANCHOR_CONTROL_SEQUENCE_COLUMN: usize = 9;
const ANCHOR_CONTROL_TAG_COLUMN: usize = 10;
const ANCHOR_CONTROL_ARG_0_COLUMN: usize = 11;
const ANCHOR_CONTROL_ARG_1_COLUMN: usize = 12;
const ANCHOR_CONTROL_ARG_2_COLUMN: usize = 13;
const ANCHOR_CONTROL_ARG_3_COLUMN: usize = 14;
const ANCHOR_PREPROCESSED_COLUMN_COUNT: usize = 15;

const NODE_PREPROCESSED_COLUMN_IDS: [&str; NODE_PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_fri_merkle_node_row_mask",
    "recursion_v2_fri_merkle_node_segment_mask",
    "recursion_v2_fri_merkle_node_binary_mask",
    "recursion_v2_fri_merkle_node_tree_id",
    "recursion_v2_fri_merkle_node_depth",
    "recursion_v2_fri_merkle_node_local_root_mask",
];

const ANCHOR_PREPROCESSED_COLUMN_IDS: [&str; ANCHOR_PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_fri_merkle_anchor_row_mask",
    "recursion_v2_fri_merkle_anchor_segment_mask",
    "recursion_v2_fri_merkle_anchor_binary_mask",
    "recursion_v2_fri_merkle_anchor_verifier_id",
    "recursion_v2_fri_merkle_anchor_layer",
    "recursion_v2_fri_merkle_anchor_query",
    "recursion_v2_fri_merkle_anchor_tree_id",
    "recursion_v2_fri_merkle_anchor_path_depth",
    "recursion_v2_fri_merkle_anchor_leaf_count",
    "recursion_v2_fri_merkle_anchor_control_sequence",
    "recursion_v2_fri_merkle_anchor_control_tag",
    "recursion_v2_fri_merkle_anchor_control_arg_0",
    "recursion_v2_fri_merkle_anchor_control_arg_1",
    "recursion_v2_fri_merkle_anchor_control_arg_2",
    "recursion_v2_fri_merkle_anchor_control_arg_3",
];

define_component_tables! {
    fri_merkle_leaf: {
        committed: {
            position,
            previous_0, previous_1, previous_2, previous_3,
            previous_4, previous_5, previous_6, previous_7,
            previous_8, previous_9, previous_10, previous_11,
            previous_12, previous_13, previous_14, previous_15,
            chunk_0, chunk_1, chunk_2, chunk_3,
            chunk_4, chunk_5, chunk_6, chunk_7,
            output_0, output_1, output_2, output_3,
            output_4, output_5, output_6, output_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        },
        constraints: {},
    },
    fri_merkle_node: {
        committed: {
            index,
            left_0, left_1, left_2, left_3,
            left_4, left_5, left_6, left_7,
            right_0, right_1, right_2, right_3,
            right_4, right_5, right_6, right_7,
            parent_0, parent_1, parent_2, parent_3,
            parent_4, parent_5, parent_6, parent_7,
            output_8, output_9, output_10, output_11,
            output_12, output_13, output_14, output_15,
        },
        constraints: {},
    },
    fri_merkle_anchor: {
        committed: {
            position,
            digest_0, digest_1, digest_2, digest_3,
            digest_4, digest_5, digest_6, digest_7,
        },
        constraints: {},
    },
}

use prover_columns::{FriMerkleAnchorColumns, FriMerkleLeafColumns, FriMerkleNodeColumns};

// One chained leaf sponge state: verifier, layer, query, packed leaf, step, state.
relation!(FriMerkleLeafStateRelation, 21);
// One authenticated secure word: verifier, layer, query, offset, limb, value.
relation!(FriMerkleValueWordRelation, 6);
// One routed local-subtree root: verifier, layer, query, root position.
relation!(FriMerkleRouteRelation, 4);
// The external path's exact endpoint, separated from internal node claims.
relation!(FriMerkleLocalRootRelation, 11);

/// Relations exported by authenticated FRI fold subsets.
#[derive(Clone)]
pub struct FriMerkleRelations {
    pub state: FriMerkleLeafStateRelation,
    pub value_word: FriMerkleValueWordRelation,
    pub route: FriMerkleRouteRelation,
    pub local_root: FriMerkleLocalRootRelation,
}

impl FriMerkleRelations {
    pub fn dummy() -> Self {
        Self {
            state: FriMerkleLeafStateRelation::dummy(),
            value_word: FriMerkleValueWordRelation::dummy(),
            route: FriMerkleRouteRelation::dummy(),
            local_root: FriMerkleLocalRootRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            state: FriMerkleLeafStateRelation::draw(channel),
            value_word: FriMerkleValueWordRelation::draw(channel),
            route: FriMerkleRouteRelation::draw(channel),
            local_root: FriMerkleLocalRootRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LeafChunkSource {
    Value { offset: u32, word: u32 },
    Constant(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LeafRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    layer: u32,
    query: u32,
    packed_index: u32,
    leaf_count: u32,
    tree_id: u32,
    tree_height: u32,
    step: u32,
    first: bool,
    last: bool,
    chunks: [LeafChunkSource; RATE],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NodeRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    layer: u32,
    query: u32,
    tree_id: u32,
    depth: u32,
    relative_index: u32,
    local_root: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AnchorRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    layer: u32,
    query: u32,
    tree_id: u32,
    path_depth: u32,
    leaf_count: u32,
    control_sequence: u32,
    control_tag: u32,
    control_args: [u32; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LayerGeometry {
    width: u32,
    leaf_size: u32,
    leaf_count: u32,
    subtree_height: u32,
    tree_height: u32,
    path_depth: u32,
}

/// Fixed leaf, local-subtree, and routed-anchor layouts for three verifier lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriMerklePreprocessed {
    leaf_log_size: u32,
    node_log_size: u32,
    anchor_log_size: u32,
    leaf_rows: Vec<LeafRow>,
    node_rows: Vec<NodeRow>,
    anchor_rows: Vec<AnchorRow>,
    vm_query_count: usize,
    vm_layer_count: usize,
    recursion_query_count: usize,
    recursion_layer_count: usize,
    vm_layers: Vec<LayerGeometry>,
    recursion_layers: Vec<LayerGeometry>,
}

impl FriMerklePreprocessed {
    pub fn new<
        const VM_TABLES: usize,
        const VM_TREES: usize,
        const VM_FRI_LAYERS: usize,
        const RECURSION_TABLES: usize,
        const RECURSION_TREES: usize,
        const RECURSION_FRI_LAYERS: usize,
    >(
        vm_plan: &VerifierControlPlan,
        vm_shape: &FixedProofShape<VM_TABLES, VM_TREES, VM_FRI_LAYERS>,
        recursion_plan: &VerifierControlPlan,
        recursion_shape: &FixedProofShape<RECURSION_TABLES, RECURSION_TREES, RECURSION_FRI_LAYERS>,
    ) -> Result<Self, FriMerkleError> {
        let vm = validated_geometry("VM", VerifierSchema::Vm, vm_plan, vm_shape)?;
        let recursion = validated_geometry(
            "recursion",
            VerifierSchema::Recursion,
            recursion_plan,
            recursion_shape,
        )?;
        let mut leaf_rows = Vec::new();
        let mut node_rows = Vec::new();
        let mut anchor_rows = Vec::new();
        append_lane_rows(
            &mut leaf_rows,
            &mut node_rows,
            &mut anchor_rows,
            vm_plan,
            &vm,
            SEGMENT_VERIFIER_ID,
            1,
            0,
        )?;
        for verifier_id in [LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID] {
            append_lane_rows(
                &mut leaf_rows,
                &mut node_rows,
                &mut anchor_rows,
                recursion_plan,
                &recursion,
                verifier_id,
                0,
                1,
            )?;
        }
        Ok(Self {
            leaf_log_size: padded_log_size(leaf_rows.len())?,
            node_log_size: padded_log_size(node_rows.len())?,
            anchor_log_size: padded_log_size(anchor_rows.len())?,
            leaf_rows,
            node_rows,
            anchor_rows,
            vm_query_count: vm.query_count,
            vm_layer_count: vm.layers.len(),
            recursion_query_count: recursion.query_count,
            recursion_layer_count: recursion.layers.len(),
            vm_layers: vm.layers,
            recursion_layers: recursion.layers,
        })
    }

    pub const fn leaf_log_size(&self) -> u32 {
        self.leaf_log_size
    }

    pub const fn node_log_size(&self) -> u32 {
        self.node_log_size
    }

    pub const fn anchor_log_size(&self) -> u32 {
        self.anchor_log_size
    }

    pub fn leaf_column_ids() -> Vec<PreProcessedColumnId> {
        let mut ids = [
            "recursion_v2_fri_merkle_leaf_row_mask",
            "recursion_v2_fri_merkle_leaf_segment_mask",
            "recursion_v2_fri_merkle_leaf_binary_mask",
            "recursion_v2_fri_merkle_leaf_verifier_id",
            "recursion_v2_fri_merkle_leaf_layer",
            "recursion_v2_fri_merkle_leaf_query",
            "recursion_v2_fri_merkle_leaf_packed_index",
            "recursion_v2_fri_merkle_leaf_count",
            "recursion_v2_fri_merkle_leaf_local_root_mask",
            "recursion_v2_fri_merkle_leaf_tree_id",
            "recursion_v2_fri_merkle_leaf_tree_height",
            "recursion_v2_fri_merkle_leaf_step",
            "recursion_v2_fri_merkle_leaf_first_mask",
            "recursion_v2_fri_merkle_leaf_last_mask",
        ]
        .into_iter()
        .map(|id| PreProcessedColumnId { id: id.into() })
        .collect::<Vec<_>>();
        for slot in 0..RATE {
            ids.extend([
                PreProcessedColumnId {
                    id: format!("recursion_v2_fri_merkle_leaf_chunk_{slot}_source_mask"),
                },
                PreProcessedColumnId {
                    id: format!("recursion_v2_fri_merkle_leaf_chunk_{slot}_offset"),
                },
                PreProcessedColumnId {
                    id: format!("recursion_v2_fri_merkle_leaf_chunk_{slot}_word"),
                },
                PreProcessedColumnId {
                    id: format!("recursion_v2_fri_merkle_leaf_chunk_{slot}_constant"),
                },
            ]);
        }
        ids
    }

    pub fn node_column_ids() -> Vec<PreProcessedColumnId> {
        ids(&NODE_PREPROCESSED_COLUMN_IDS)
    }

    pub fn anchor_column_ids() -> Vec<PreProcessedColumnId> {
        ids(&ANCHOR_PREPROCESSED_COLUMN_IDS)
    }

    pub fn gen_leaf_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let mut columns = zero_columns(LEAF_PREPROCESSED_COLUMN_COUNT, self.leaf_log_size);
        for (index, row) in self.leaf_rows.iter().copied().enumerate() {
            columns[LEAF_ROW_MASK_COLUMN][index] = 1;
            columns[LEAF_SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[LEAF_BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[LEAF_VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[LEAF_LAYER_COLUMN][index] = row.layer;
            columns[LEAF_QUERY_COLUMN][index] = row.query;
            columns[LEAF_PACKED_INDEX_COLUMN][index] = row.packed_index;
            columns[LEAF_COUNT_COLUMN][index] = row.leaf_count;
            columns[LEAF_LOCAL_ROOT_MASK_COLUMN][index] = u32::from(row.leaf_count == 1);
            columns[LEAF_TREE_ID_COLUMN][index] = row.tree_id;
            columns[LEAF_TREE_HEIGHT_COLUMN][index] = row.tree_height;
            columns[LEAF_STEP_COLUMN][index] = row.step;
            columns[LEAF_FIRST_MASK_COLUMN][index] = u32::from(row.first);
            columns[LEAF_LAST_MASK_COLUMN][index] = u32::from(row.last);
            for (slot, source) in row.chunks.into_iter().enumerate() {
                let start = leaf_chunk_column(slot);
                match source {
                    LeafChunkSource::Value { offset, word } => {
                        columns[start][index] = 1;
                        columns[start + 1][index] = offset;
                        columns[start + 2][index] = word;
                    }
                    LeafChunkSource::Constant(value) => columns[start + 3][index] = value,
                }
            }
        }
        into_evaluations(columns, self.leaf_log_size)
    }

    pub fn gen_node_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let mut columns = zero_columns(NODE_PREPROCESSED_COLUMN_COUNT, self.node_log_size);
        for (index, row) in self.node_rows.iter().copied().enumerate() {
            columns[NODE_ROW_MASK_COLUMN][index] = 1;
            columns[NODE_SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[NODE_BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[NODE_TREE_ID_COLUMN][index] = row.tree_id;
            columns[NODE_DEPTH_COLUMN][index] = row.depth;
            columns[NODE_LOCAL_ROOT_MASK_COLUMN][index] = u32::from(row.local_root);
        }
        into_evaluations(columns, self.node_log_size)
    }

    pub fn gen_anchor_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let mut columns = zero_columns(ANCHOR_PREPROCESSED_COLUMN_COUNT, self.anchor_log_size);
        for (index, row) in self.anchor_rows.iter().copied().enumerate() {
            columns[ANCHOR_ROW_MASK_COLUMN][index] = 1;
            columns[ANCHOR_SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[ANCHOR_BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[ANCHOR_VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[ANCHOR_LAYER_COLUMN][index] = row.layer;
            columns[ANCHOR_QUERY_COLUMN][index] = row.query;
            columns[ANCHOR_TREE_ID_COLUMN][index] = row.tree_id;
            columns[ANCHOR_PATH_DEPTH_COLUMN][index] = row.path_depth;
            columns[ANCHOR_LEAF_COUNT_COLUMN][index] = row.leaf_count;
            columns[ANCHOR_CONTROL_SEQUENCE_COLUMN][index] = row.control_sequence;
            columns[ANCHOR_CONTROL_TAG_COLUMN][index] = row.control_tag;
            columns[ANCHOR_CONTROL_ARG_0_COLUMN][index] = row.control_args[0];
            columns[ANCHOR_CONTROL_ARG_1_COLUMN][index] = row.control_args[1];
            columns[ANCHOR_CONTROL_ARG_2_COLUMN][index] = row.control_args[2];
            columns[ANCHOR_CONTROL_ARG_3_COLUMN][index] = row.control_args[3];
        }
        into_evaluations(columns, self.anchor_log_size)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ValidatedGeometry {
    query_count: usize,
    layers: Vec<LayerGeometry>,
}

fn validated_geometry<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    profile: &'static str,
    schema: VerifierSchema,
    plan: &VerifierControlPlan,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
) -> Result<ValidatedGeometry, FriMerkleError> {
    if plan.schema() != schema {
        return Err(FriMerkleError::SchemaMismatch {
            profile,
            expected: schema,
            actual: plan.schema(),
        });
    }
    let pcs = plan
        .pcs_parameters()
        .validate()
        .map_err(FriMerkleError::Pcs)?;
    shape.validate(pcs).map_err(|error| match schema {
        VerifierSchema::Vm => FriMerkleError::VmShape(error),
        VerifierSchema::Recursion => FriMerkleError::RecursionShape(error),
    })?;
    let mut layers = Vec::with_capacity(N_FRI_LAYERS);
    for layer in 0..N_FRI_LAYERS {
        let width = shape.fri_layer_fold_widths[layer].as_u32();
        let fold_step = width.ilog2();
        let leaf_size = if fold_step > 1 {
            u32::try_from(PACKED_LEAF_SIZE).expect("packed FRI leaf size fits u32")
        } else {
            1
        };
        let leaf_count = width / leaf_size;
        let subtree_height = leaf_count.ilog2();
        let tree_height = shape.fri_layer_tree_heights[layer].as_u32();
        let path_depth = fri_query_path_depth(tree_height, width)
            .expect("validated FRI geometry has a packed-subtree path");
        if path_depth
            .checked_add(subtree_height)
            .ok_or(FriMerkleError::ArithmeticOverflow {
                field: "FRI packed subtree height",
            })?
            != tree_height
        {
            return Err(FriMerkleError::PackedSubtreeHeightMismatch {
                profile,
                layer,
                tree_height,
                path_depth,
                subtree_height,
            });
        }
        layers.push(LayerGeometry {
            width,
            leaf_size,
            leaf_count,
            subtree_height,
            tree_height,
            path_depth,
        });
    }
    Ok(ValidatedGeometry {
        query_count: pcs.config().fri_config.n_queries,
        layers,
    })
}

#[allow(clippy::too_many_arguments)]
fn append_lane_rows(
    leaf_rows: &mut Vec<LeafRow>,
    node_rows: &mut Vec<NodeRow>,
    anchor_rows: &mut Vec<AnchorRow>,
    plan: &VerifierControlPlan,
    geometry: &ValidatedGeometry,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
) -> Result<(), FriMerkleError> {
    let query_count = geometry.query_count;
    for (layer, geometry) in geometry.layers.iter().copied().enumerate() {
        let layer_u32 = canonical_usize("FRI layer", layer)?;
        let tree_id = fri_tree_id(verifier_id, layer).map_err(FriMerkleError::TreeNamespace)?;
        let semantic_words = geometry.leaf_size.checked_mul(SECURE_WORDS as u32).ok_or(
            FriMerkleError::ArithmeticOverflow {
                field: "FRI leaf semantic word count",
            },
        )?;
        let hash_steps = semantic_words
            .checked_add(1)
            .ok_or(FriMerkleError::ArithmeticOverflow {
                field: "FRI leaf end marker",
            })?
            .div_ceil(RATE as u32);
        for query in 0..query_count {
            let query_u32 = canonical_usize("raw query", query)?;
            let control = VerifierStep::VerifyFriMerklePath {
                layer: layer_u32,
                query: query_u32,
                depth: geometry.path_depth,
                width: geometry.width,
            };
            let control_sequence = control_sequence(plan, control)?;
            let encoded = control.encode();
            anchor_rows.push(AnchorRow {
                segment_mask,
                binary_mask,
                verifier_id,
                layer: layer_u32,
                query: query_u32,
                tree_id,
                path_depth: geometry.path_depth,
                leaf_count: geometry.leaf_count,
                control_sequence,
                control_tag: encoded.tag(),
                control_args: encoded.args(),
            });
            // Bottom-up order lets witness generation derive every parent
            // immediately from already materialized children.
            for local_depth in (0..geometry.subtree_height).rev() {
                let depth = geometry.path_depth.checked_add(local_depth).ok_or(
                    FriMerkleError::ArithmeticOverflow {
                        field: "FRI local node depth",
                    },
                )?;
                for relative_index in 0..1_u32 << local_depth {
                    node_rows.push(NodeRow {
                        segment_mask,
                        binary_mask,
                        verifier_id,
                        layer: layer_u32,
                        query: query_u32,
                        tree_id,
                        depth,
                        relative_index,
                        local_root: local_depth == 0,
                    });
                }
            }
            for packed_index in 0..geometry.leaf_count {
                for step in 0..hash_steps {
                    let mut chunks = [LeafChunkSource::Constant(0); RATE];
                    for (slot, chunk) in chunks.iter_mut().enumerate() {
                        let stream_index = step
                            .checked_mul(RATE as u32)
                            .and_then(|start| start.checked_add(slot as u32))
                            .ok_or(FriMerkleError::ArithmeticOverflow {
                                field: "FRI leaf stream index",
                            })?;
                        *chunk = if stream_index < semantic_words {
                            let offset = packed_index
                                .checked_mul(geometry.leaf_size)
                                .and_then(|start| {
                                    start.checked_add(stream_index / SECURE_WORDS as u32)
                                })
                                .ok_or(FriMerkleError::ArithmeticOverflow {
                                    field: "FRI value offset",
                                })?;
                            LeafChunkSource::Value {
                                offset,
                                word: stream_index % SECURE_WORDS as u32,
                            }
                        } else if stream_index == semantic_words {
                            LeafChunkSource::Constant(1)
                        } else {
                            LeafChunkSource::Constant(0)
                        };
                    }
                    leaf_rows.push(LeafRow {
                        segment_mask,
                        binary_mask,
                        verifier_id,
                        layer: layer_u32,
                        query: query_u32,
                        packed_index,
                        leaf_count: geometry.leaf_count,
                        tree_id,
                        tree_height: geometry.tree_height,
                        step,
                        first: step == 0,
                        last: step + 1 == hash_steps,
                        chunks,
                    });
                }
            }
        }
    }
    Ok(())
}

fn control_sequence(
    plan: &VerifierControlPlan,
    expected: VerifierStep,
) -> Result<u32, FriMerkleError> {
    let mut matches = plan
        .steps()
        .iter()
        .copied()
        .enumerate()
        .filter(|(_, step)| *step == expected);
    let (sequence, _) = matches
        .next()
        .ok_or(FriMerkleError::ControlStepMissing { expected })?;
    if matches.next().is_some() {
        return Err(FriMerkleError::DuplicateControlStep { expected });
    }
    canonical_usize("control sequence", sequence)
}

fn padded_log_size(row_count: usize) -> Result<u32, FriMerkleError> {
    let padded = row_count
        .max(1)
        .checked_next_power_of_two()
        .ok_or(FriMerkleError::RowCountOverflow)?
        .max(1 << MIN_LOG_SIZE);
    let log_size = padded.ilog2();
    if log_size > MAX_CIRCLE_DOMAIN_LOG_SIZE {
        return Err(FriMerkleError::LogSizeOutOfRange { log_size });
    }
    Ok(log_size)
}

fn canonical_usize(field: &'static str, value: usize) -> Result<u32, FriMerkleError> {
    let value =
        u32::try_from(value).map_err(|_| FriMerkleError::IndexOutOfRange { field, value })?;
    M31Word::try_from(value)
        .map(M31Word::as_u32)
        .map_err(|_| FriMerkleError::IndexNotCanonical { field, value })
}

fn ids<const N: usize>(names: &[&str; N]) -> Vec<PreProcessedColumnId> {
    names
        .iter()
        .map(|id| PreProcessedColumnId { id: (*id).into() })
        .collect()
}

fn zero_columns(count: usize, log_size: u32) -> Vec<AlignedVec<u32>> {
    let size = 1_usize << log_size;
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

const fn leaf_chunk_column(slot: usize) -> usize {
    LEAF_CHUNKS_START + slot * LEAF_CHUNK_COLUMNS
}

pub type LeafComponent = FrameworkComponent<LeafEval>;
pub type NodeComponent = FrameworkComponent<NodeEval>;
pub type AnchorComponent = FrameworkComponent<AnchorEval>;

/// Verifies fixed FRI leaf sponges and exports their authenticated words.
#[derive(Clone)]
pub struct LeafEval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub vm_relations: Relations,
    pub fri_relations: FriMerkleRelations,
    pub recursion_relations: RecursionRelations,
}

impl FrameworkEval for LeafEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = FriMerkleLeafColumns::from_eval(&mut eval);
        let ids = FriMerklePreprocessed::leaf_column_ids();
        let row_mask = eval.get_preprocessed_column(ids[LEAF_ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[LEAF_SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[LEAF_BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[LEAF_VERIFIER_ID_COLUMN].clone());
        let layer = eval.get_preprocessed_column(ids[LEAF_LAYER_COLUMN].clone());
        let query = eval.get_preprocessed_column(ids[LEAF_QUERY_COLUMN].clone());
        let packed_index = eval.get_preprocessed_column(ids[LEAF_PACKED_INDEX_COLUMN].clone());
        let leaf_count = eval.get_preprocessed_column(ids[LEAF_COUNT_COLUMN].clone());
        let local_root = eval.get_preprocessed_column(ids[LEAF_LOCAL_ROOT_MASK_COLUMN].clone());
        let tree_id = eval.get_preprocessed_column(ids[LEAF_TREE_ID_COLUMN].clone());
        let tree_height = eval.get_preprocessed_column(ids[LEAF_TREE_HEIGHT_COLUMN].clone());
        let step = eval.get_preprocessed_column(ids[LEAF_STEP_COLUMN].clone());
        let first = eval.get_preprocessed_column(ids[LEAF_FIRST_MASK_COLUMN].clone());
        let last = eval.get_preprocessed_column(ids[LEAF_LAST_MASK_COLUMN].clone());
        let chunk_metadata: LeafChunkMetadata<E::F> = core::array::from_fn(|slot| {
            let start = leaf_chunk_column(slot);
            (
                eval.get_preprocessed_column(ids[start].clone()),
                eval.get_preprocessed_column(ids[start + 1].clone()),
                eval.get_preprocessed_column(ids[start + 2].clone()),
                eval.get_preprocessed_column(ids[start + 3].clone()),
            )
        });
        let previous = leaf_previous_columns(&cols);
        let chunks = leaf_chunk_columns(&cols);
        let output = leaf_output_columns(&cols);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        let final_active = active.clone() * last.clone();

        eval.add_constraint(cols.enabler.clone() - active.clone());
        for value in previous.iter().chain(&chunks).chain(&output) {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }
        eval.add_constraint((one.clone() - final_active.clone()) * cols.position.clone());
        for (index, value) in previous.iter().enumerate() {
            let initial = u32::from(index + 1 == T) * LEAF_TAG;
            eval.add_constraint(
                active.clone()
                    * first.clone()
                    * (value.clone() - E::F::from(BaseField::from(initial))),
            );
        }
        for (slot, chunk) in chunks.iter().enumerate() {
            let (source_mask, _, _, constant) = &chunk_metadata[slot];
            eval.add_constraint(
                active.clone()
                    * (one.clone() - source_mask.clone())
                    * (chunk.clone() - constant.clone()),
            );
        }

        let mut poseidon_tuple = Vec::with_capacity(2 * T);
        for (index, value) in previous.iter().enumerate() {
            poseidon_tuple.push(if index < RATE {
                value.clone() + chunks[index].clone()
            } else {
                value.clone()
            });
        }
        poseidon_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.vm_relations.poseidon2_io,
            -E::EF::from(active.clone()),
            &poseidon_tuple,
        ));

        for (slot, chunk) in chunks.iter().enumerate() {
            let (source_mask, offset, word, _) = &chunk_metadata[slot];
            eval.add_to_relation(RelationEntry::new(
                &self.fri_relations.value_word,
                E::EF::from(active.clone() * source_mask.clone()),
                &[
                    verifier_id.clone(),
                    layer.clone(),
                    query.clone(),
                    offset.clone(),
                    word.clone(),
                    chunk.clone(),
                ],
            ));
        }

        let mut previous_tuple = vec![
            verifier_id.clone(),
            layer.clone(),
            query.clone(),
            packed_index.clone(),
            step.clone(),
        ];
        previous_tuple.extend(previous.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.state,
            -E::EF::from(active.clone() * (one.clone() - first)),
            &previous_tuple,
        ));
        let mut output_tuple = vec![
            verifier_id.clone(),
            layer.clone(),
            query.clone(),
            packed_index.clone(),
            step + one.clone(),
        ];
        output_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.state,
            E::EF::from(active.clone() * (one.clone() - last)),
            &output_tuple,
        ));

        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.route,
            -E::EF::from(final_active.clone()),
            &[verifier_id, layer, query, cols.position.clone()],
        ));
        let leaf_index = cols.position.clone() * leaf_count + packed_index;
        let mut leaf_tuple = vec![tree_id, tree_height, leaf_index];
        leaf_tuple.extend(output[..DIGEST_WORDS].iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            -E::EF::from(final_active.clone() * (one.clone() - local_root.clone())),
            &leaf_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.local_root,
            -E::EF::from(final_active * local_root),
            &leaf_tuple,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Rebuilds every internal node of an authenticated FRI fold subset.
#[derive(Clone)]
pub struct NodeEval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub vm_relations: Relations,
    pub fri_relations: FriMerkleRelations,
    pub recursion_relations: RecursionRelations,
}

impl FrameworkEval for NodeEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = FriMerkleNodeColumns::from_eval(&mut eval);
        let ids = FriMerklePreprocessed::node_column_ids();
        let row_mask = eval.get_preprocessed_column(ids[NODE_ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[NODE_SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[NODE_BINARY_MASK_COLUMN].clone());
        let tree_id = eval.get_preprocessed_column(ids[NODE_TREE_ID_COLUMN].clone());
        let depth = eval.get_preprocessed_column(ids[NODE_DEPTH_COLUMN].clone());
        let local_root = eval.get_preprocessed_column(ids[NODE_LOCAL_ROOT_MASK_COLUMN].clone());
        let left = node_left_columns(&cols);
        let right = node_right_columns(&cols);
        let parent = node_parent_columns(&cols);
        let tail = node_tail_columns(&cols);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        let two = E::F::from(BaseField::from(2));

        eval.add_constraint(cols.enabler.clone() - active.clone());
        for value in core::iter::once(&cols.index)
            .chain(left.iter())
            .chain(&right)
            .chain(&parent)
            .chain(&tail)
        {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        let mut poseidon_tuple = Vec::with_capacity(2 * T);
        poseidon_tuple.extend(left.iter().cloned());
        poseidon_tuple.extend(right.iter().cloned());
        poseidon_tuple.extend(parent.iter().cloned());
        poseidon_tuple.extend(tail.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.vm_relations.poseidon2_io,
            -E::EF::from(active.clone()),
            &poseidon_tuple,
        ));

        let mut own_tuple = vec![tree_id.clone(), depth.clone(), cols.index.clone()];
        own_tuple.extend(parent.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            -E::EF::from(active.clone() * (one.clone() - local_root.clone())),
            &own_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.local_root,
            -E::EF::from(active.clone() * local_root),
            &own_tuple,
        ));

        let child_depth = depth + one;
        let left_index = cols.index.clone() * two;
        let mut left_tuple = vec![tree_id.clone(), child_depth.clone(), left_index.clone()];
        left_tuple.extend(left.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            E::EF::from(active.clone()),
            &left_tuple,
        ));
        let mut right_tuple = vec![
            tree_id,
            child_depth,
            left_index + E::F::from(BaseField::from(1)),
        ];
        right_tuple.extend(right.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            E::EF::from(active),
            &right_tuple,
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Binds each external FRI path endpoint to its routed local subtree.
#[derive(Clone)]
pub struct AnchorEval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub control_relations: ControlRelations,
    pub query_relations: QueryPositionRelations,
    pub fri_relations: FriMerkleRelations,
    pub recursion_relations: RecursionRelations,
}

impl FrameworkEval for AnchorEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = FriMerkleAnchorColumns::from_eval(&mut eval);
        let ids = FriMerklePreprocessed::anchor_column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ANCHOR_ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[ANCHOR_SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[ANCHOR_BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[ANCHOR_VERIFIER_ID_COLUMN].clone());
        let layer = eval.get_preprocessed_column(ids[ANCHOR_LAYER_COLUMN].clone());
        let query = eval.get_preprocessed_column(ids[ANCHOR_QUERY_COLUMN].clone());
        let tree_id = eval.get_preprocessed_column(ids[ANCHOR_TREE_ID_COLUMN].clone());
        let path_depth = eval.get_preprocessed_column(ids[ANCHOR_PATH_DEPTH_COLUMN].clone());
        let leaf_count = eval.get_preprocessed_column(ids[ANCHOR_LEAF_COUNT_COLUMN].clone());
        let control_sequence =
            eval.get_preprocessed_column(ids[ANCHOR_CONTROL_SEQUENCE_COLUMN].clone());
        let control_tag = eval.get_preprocessed_column(ids[ANCHOR_CONTROL_TAG_COLUMN].clone());
        let control_args = [
            eval.get_preprocessed_column(ids[ANCHOR_CONTROL_ARG_0_COLUMN].clone()),
            eval.get_preprocessed_column(ids[ANCHOR_CONTROL_ARG_1_COLUMN].clone()),
            eval.get_preprocessed_column(ids[ANCHOR_CONTROL_ARG_2_COLUMN].clone()),
            eval.get_preprocessed_column(ids[ANCHOR_CONTROL_ARG_3_COLUMN].clone()),
        ];
        let digest = anchor_digest_columns(&cols);
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));

        eval.add_constraint(cols.enabler.clone() - active.clone());
        for value in core::iter::once(&cols.position).chain(&digest) {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.position,
            -E::EF::from(active.clone()),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(QueryPositionKind::FriMerkle.as_u32())),
                layer.clone(),
                query.clone(),
                cols.position.clone(),
                E::F::from(BaseField::from(0)),
            ],
        ));
        let mut root_tuple = vec![tree_id, path_depth, cols.position.clone()];
        root_tuple.extend(digest.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            -E::EF::from(active.clone()),
            &root_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.local_root,
            E::EF::from(active.clone()),
            &root_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.fri_relations.route,
            E::EF::from(active.clone() * leaf_count),
            &[verifier_id.clone(), layer, query, cols.position.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.control_relations.step,
            -E::EF::from(active),
            &[
                verifier_id,
                control_sequence,
                control_tag,
                control_args[0].clone(),
                control_args[1].clone(),
                control_args[2].clone(),
                control_args[3].clone(),
            ],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn leaf_previous_columns<F: Clone>(cols: &FriMerkleLeafColumns<F>) -> [F; T] {
    [
        cols.previous_0.clone(),
        cols.previous_1.clone(),
        cols.previous_2.clone(),
        cols.previous_3.clone(),
        cols.previous_4.clone(),
        cols.previous_5.clone(),
        cols.previous_6.clone(),
        cols.previous_7.clone(),
        cols.previous_8.clone(),
        cols.previous_9.clone(),
        cols.previous_10.clone(),
        cols.previous_11.clone(),
        cols.previous_12.clone(),
        cols.previous_13.clone(),
        cols.previous_14.clone(),
        cols.previous_15.clone(),
    ]
}

fn leaf_chunk_columns<F: Clone>(cols: &FriMerkleLeafColumns<F>) -> [F; RATE] {
    [
        cols.chunk_0.clone(),
        cols.chunk_1.clone(),
        cols.chunk_2.clone(),
        cols.chunk_3.clone(),
        cols.chunk_4.clone(),
        cols.chunk_5.clone(),
        cols.chunk_6.clone(),
        cols.chunk_7.clone(),
    ]
}

fn leaf_output_columns<F: Clone>(cols: &FriMerkleLeafColumns<F>) -> [F; T] {
    [
        cols.output_0.clone(),
        cols.output_1.clone(),
        cols.output_2.clone(),
        cols.output_3.clone(),
        cols.output_4.clone(),
        cols.output_5.clone(),
        cols.output_6.clone(),
        cols.output_7.clone(),
        cols.output_8.clone(),
        cols.output_9.clone(),
        cols.output_10.clone(),
        cols.output_11.clone(),
        cols.output_12.clone(),
        cols.output_13.clone(),
        cols.output_14.clone(),
        cols.output_15.clone(),
    ]
}

fn node_left_columns<F: Clone>(cols: &FriMerkleNodeColumns<F>) -> [F; DIGEST_WORDS] {
    [
        cols.left_0.clone(),
        cols.left_1.clone(),
        cols.left_2.clone(),
        cols.left_3.clone(),
        cols.left_4.clone(),
        cols.left_5.clone(),
        cols.left_6.clone(),
        cols.left_7.clone(),
    ]
}

fn node_right_columns<F: Clone>(cols: &FriMerkleNodeColumns<F>) -> [F; DIGEST_WORDS] {
    [
        cols.right_0.clone(),
        cols.right_1.clone(),
        cols.right_2.clone(),
        cols.right_3.clone(),
        cols.right_4.clone(),
        cols.right_5.clone(),
        cols.right_6.clone(),
        cols.right_7.clone(),
    ]
}

fn node_parent_columns<F: Clone>(cols: &FriMerkleNodeColumns<F>) -> [F; DIGEST_WORDS] {
    [
        cols.parent_0.clone(),
        cols.parent_1.clone(),
        cols.parent_2.clone(),
        cols.parent_3.clone(),
        cols.parent_4.clone(),
        cols.parent_5.clone(),
        cols.parent_6.clone(),
        cols.parent_7.clone(),
    ]
}

fn node_tail_columns<F: Clone>(cols: &FriMerkleNodeColumns<F>) -> [F; DIGEST_WORDS] {
    [
        cols.output_8.clone(),
        cols.output_9.clone(),
        cols.output_10.clone(),
        cols.output_11.clone(),
        cols.output_12.clone(),
        cols.output_13.clone(),
        cols.output_14.clone(),
        cols.output_15.clone(),
    ]
}

fn anchor_digest_columns<F: Clone>(cols: &FriMerkleAnchorColumns<F>) -> [F; DIGEST_WORDS] {
    [
        cols.digest_0.clone(),
        cols.digest_1.clone(),
        cols.digest_2.clone(),
        cols.digest_3.clone(),
        cols.digest_4.clone(),
        cols.digest_5.clone(),
        cols.digest_6.clone(),
        cols.digest_7.clone(),
    ]
}

/// Generates leaf hash, value, state, route, and endpoint interactions.
#[allow(clippy::too_many_arguments)]
pub fn gen_leaf_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    fri_relations: &FriMerkleRelations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = FriMerkleLeafColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let previous = leaf_previous_columns(&cols);
    let chunks = leaf_chunk_columns(&cols);
    let output = leaf_output_columns(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[LEAF_ROW_MASK_COLUMN][row]
                    * (pp[LEAF_SEGMENT_MASK_COLUMN][row] * segment
                        + pp[LEAF_BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let first = (0..size)
        .map(|row| PackedQM31::from(pp[LEAF_FIRST_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let last = (0..size)
        .map(|row| PackedQM31::from(pp[LEAF_LAST_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let previous_numerator = active
        .iter()
        .zip(&first)
        .map(|(active, first)| -*active * (PackedQM31::one() - *first))
        .collect::<Vec<_>>();
    let output_numerator = active
        .iter()
        .zip(&last)
        .map(|(active, last)| *active * (PackedQM31::one() - *last))
        .collect::<Vec<_>>();
    let final_numerator = active
        .iter()
        .zip(&last)
        .map(|(active, last)| -*active * *last)
        .collect::<Vec<_>>();

    let in_rate = core::array::from_fn::<_, RATE, _>(|slot| {
        previous[slot]
            .iter()
            .zip(chunks[slot])
            .map(|(previous, chunk)| *previous + *chunk)
            .collect::<Vec<PackedM31>>()
    });
    let poseidon_denominator = combine!(
        vm_relations.poseidon2_io,
        [
            &in_rate[0],
            &in_rate[1],
            &in_rate[2],
            &in_rate[3],
            &in_rate[4],
            &in_rate[5],
            &in_rate[6],
            &in_rate[7],
            previous[8],
            previous[9],
            previous[10],
            previous[11],
            previous[12],
            previous[13],
            previous[14],
            previous[15],
            output[0],
            output[1],
            output[2],
            output[3],
            output[4],
            output[5],
            output[6],
            output[7],
            output[8],
            output[9],
            output[10],
            output[11],
            output[12],
            output[13],
            output[14],
            output[15]
        ]
    );

    let value_numerators = (0..RATE)
        .map(|slot| {
            (0..size)
                .map(|row| active[row] * pp[leaf_chunk_column(slot)][row])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let value_denominators = (0..RATE)
        .map(|slot| {
            (0..size)
                .map(|row| {
                    fri_relations.value_word.combine(&[
                        pp[LEAF_VERIFIER_ID_COLUMN][row],
                        pp[LEAF_LAYER_COLUMN][row],
                        pp[LEAF_QUERY_COLUMN][row],
                        pp[leaf_chunk_column(slot) + 1][row],
                        pp[leaf_chunk_column(slot) + 2][row],
                        chunks[slot][row],
                    ])
                })
                .collect::<Vec<PackedQM31>>()
        })
        .collect::<Vec<_>>();

    let one = PackedM31::broadcast(BaseField::from(1));
    let previous_denominator = (0..size)
        .map(|row| {
            let mut tuple = vec![
                pp[LEAF_VERIFIER_ID_COLUMN][row],
                pp[LEAF_LAYER_COLUMN][row],
                pp[LEAF_QUERY_COLUMN][row],
                pp[LEAF_PACKED_INDEX_COLUMN][row],
                pp[LEAF_STEP_COLUMN][row],
            ];
            tuple.extend(previous.iter().map(|column| column[row]));
            fri_relations.state.combine(&tuple)
        })
        .collect::<Vec<PackedQM31>>();
    let output_denominator = (0..size)
        .map(|row| {
            let mut tuple = vec![
                pp[LEAF_VERIFIER_ID_COLUMN][row],
                pp[LEAF_LAYER_COLUMN][row],
                pp[LEAF_QUERY_COLUMN][row],
                pp[LEAF_PACKED_INDEX_COLUMN][row],
                pp[LEAF_STEP_COLUMN][row] + one,
            ];
            tuple.extend(output.iter().map(|column| column[row]));
            fri_relations.state.combine(&tuple)
        })
        .collect::<Vec<PackedQM31>>();
    let route_denominator = (0..size)
        .map(|row| {
            fri_relations.route.combine(&[
                pp[LEAF_VERIFIER_ID_COLUMN][row],
                pp[LEAF_LAYER_COLUMN][row],
                pp[LEAF_QUERY_COLUMN][row],
                cols.position[row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let leaf_indices = (0..size)
        .map(|row| {
            cols.position[row] * pp[LEAF_COUNT_COLUMN][row] + pp[LEAF_PACKED_INDEX_COLUMN][row]
        })
        .collect::<Vec<_>>();
    let merkle_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[LEAF_TREE_ID_COLUMN][row],
                pp[LEAF_TREE_HEIGHT_COLUMN][row],
                leaf_indices[row],
                output[0][row],
                output[1][row],
                output[2][row],
                output[3][row],
                output[4][row],
                output[5][row],
                output[6][row],
                output[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let local_root_denominator = (0..size)
        .map(|row| {
            fri_relations.local_root.combine(&[
                pp[LEAF_TREE_ID_COLUMN][row],
                pp[LEAF_TREE_HEIGHT_COLUMN][row],
                leaf_indices[row],
                output[0][row],
                output[1][row],
                output[2][row],
                output[3][row],
                output[4][row],
                output[5][row],
                output[6][row],
                output[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let merkle_numerator = (0..size)
        .map(|row| {
            final_numerator[row]
                * (PackedQM31::one() - PackedQM31::from(pp[LEAF_LOCAL_ROOT_MASK_COLUMN][row]))
        })
        .collect::<Vec<_>>();
    let local_root_numerator = (0..size)
        .map(|row| final_numerator[row] * pp[LEAF_LOCAL_ROOT_MASK_COLUMN][row])
        .collect::<Vec<_>>();

    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &poseidon_denominator,
        &value_numerators[0],
        &value_denominators[0],
        logup
    );
    write_pair!(
        &value_numerators[1],
        &value_denominators[1],
        &value_numerators[2],
        &value_denominators[2],
        logup
    );
    write_pair!(
        &value_numerators[3],
        &value_denominators[3],
        &value_numerators[4],
        &value_denominators[4],
        logup
    );
    write_pair!(
        &value_numerators[5],
        &value_denominators[5],
        &value_numerators[6],
        &value_denominators[6],
        logup
    );
    write_pair!(
        &value_numerators[7],
        &value_denominators[7],
        &previous_numerator,
        &previous_denominator,
        logup
    );
    write_pair!(
        &output_numerator,
        &output_denominator,
        &final_numerator,
        &route_denominator,
        logup
    );
    write_pair!(
        &merkle_numerator,
        &merkle_denominator,
        &local_root_numerator,
        &local_root_denominator,
        logup
    );
    logup.finalize_last()
}

/// Generates internal-node hash and binary-subtree interactions.
pub fn gen_node_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    fri_relations: &FriMerkleRelations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = FriMerkleNodeColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let left = node_left_columns(&cols);
    let right = node_right_columns(&cols);
    let parent = node_parent_columns(&cols);
    let tail = node_tail_columns(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[NODE_ROW_MASK_COLUMN][row]
                    * (pp[NODE_SEGMENT_MASK_COLUMN][row] * segment
                        + pp[NODE_BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let regular_numerator = (0..size)
        .map(|row| {
            -active[row]
                * (PackedQM31::one() - PackedQM31::from(pp[NODE_LOCAL_ROOT_MASK_COLUMN][row]))
        })
        .collect::<Vec<_>>();
    let local_root_numerator = (0..size)
        .map(|row| -active[row] * pp[NODE_LOCAL_ROOT_MASK_COLUMN][row])
        .collect::<Vec<_>>();

    let poseidon_denominator = combine!(
        vm_relations.poseidon2_io,
        [
            left[0], left[1], left[2], left[3], left[4], left[5], left[6], left[7], right[0],
            right[1], right[2], right[3], right[4], right[5], right[6], right[7], parent[0],
            parent[1], parent[2], parent[3], parent[4], parent[5], parent[6], parent[7], tail[0],
            tail[1], tail[2], tail[3], tail[4], tail[5], tail[6], tail[7]
        ]
    );
    let own_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[NODE_TREE_ID_COLUMN][row],
                pp[NODE_DEPTH_COLUMN][row],
                cols.index[row],
                parent[0][row],
                parent[1][row],
                parent[2][row],
                parent[3][row],
                parent[4][row],
                parent[5][row],
                parent[6][row],
                parent[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let local_root_denominator = (0..size)
        .map(|row| {
            fri_relations.local_root.combine(&[
                pp[NODE_TREE_ID_COLUMN][row],
                pp[NODE_DEPTH_COLUMN][row],
                cols.index[row],
                parent[0][row],
                parent[1][row],
                parent[2][row],
                parent[3][row],
                parent[4][row],
                parent[5][row],
                parent[6][row],
                parent[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let one = PackedM31::broadcast(BaseField::from(1));
    let two = PackedM31::broadcast(BaseField::from(2));
    let child_depth = (0..size)
        .map(|row| pp[NODE_DEPTH_COLUMN][row] + one)
        .collect::<Vec<_>>();
    let left_index = (0..size)
        .map(|row| cols.index[row] * two)
        .collect::<Vec<_>>();
    let right_index = left_index
        .iter()
        .map(|index| *index + one)
        .collect::<Vec<_>>();
    let left_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[NODE_TREE_ID_COLUMN][row],
                child_depth[row],
                left_index[row],
                left[0][row],
                left[1][row],
                left[2][row],
                left[3][row],
                left[4][row],
                left[5][row],
                left[6][row],
                left[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let right_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[NODE_TREE_ID_COLUMN][row],
                child_depth[row],
                right_index[row],
                right[0][row],
                right[1][row],
                right[2][row],
                right[3][row],
                right[4][row],
                right[5][row],
                right[6][row],
                right[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();

    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &poseidon_denominator,
        &regular_numerator,
        &own_denominator,
        logup
    );
    write_pair!(
        &local_root_numerator,
        &local_root_denominator,
        &active,
        &left_denominator,
        logup
    );
    let mut right_column = logup.new_col();
    for row in 0..size {
        right_column.write_frac(row, active[row], right_denominator[row]);
    }
    right_column.finalize_col();
    logup.finalize_last()
}

/// Generates query, external-path, local-root, route, and control interactions.
#[allow(clippy::too_many_arguments)]
pub fn gen_anchor_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    control_relations: &ControlRelations,
    query_relations: &QueryPositionRelations,
    fri_relations: &FriMerkleRelations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = FriMerkleAnchorColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let digest = anchor_digest_columns(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[ANCHOR_ROW_MASK_COLUMN][row]
                    * (pp[ANCHOR_SEGMENT_MASK_COLUMN][row] * segment
                        + pp[ANCHOR_BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let route_numerator = (0..size)
        .map(|row| active[row] * pp[ANCHOR_LEAF_COUNT_COLUMN][row])
        .collect::<Vec<_>>();
    let fri_merkle_kind =
        PackedM31::broadcast(BaseField::from(QueryPositionKind::FriMerkle.as_u32()));
    let zero = PackedM31::broadcast(BaseField::from(0));
    let query_denominator = (0..size)
        .map(|row| {
            query_relations.position.combine(&[
                pp[ANCHOR_VERIFIER_ID_COLUMN][row],
                fri_merkle_kind,
                pp[ANCHOR_LAYER_COLUMN][row],
                pp[ANCHOR_QUERY_COLUMN][row],
                cols.position[row],
                zero,
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let external_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[ANCHOR_TREE_ID_COLUMN][row],
                pp[ANCHOR_PATH_DEPTH_COLUMN][row],
                cols.position[row],
                digest[0][row],
                digest[1][row],
                digest[2][row],
                digest[3][row],
                digest[4][row],
                digest[5][row],
                digest[6][row],
                digest[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let local_root_denominator = (0..size)
        .map(|row| {
            fri_relations.local_root.combine(&[
                pp[ANCHOR_TREE_ID_COLUMN][row],
                pp[ANCHOR_PATH_DEPTH_COLUMN][row],
                cols.position[row],
                digest[0][row],
                digest[1][row],
                digest[2][row],
                digest[3][row],
                digest[4][row],
                digest[5][row],
                digest[6][row],
                digest[7][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let route_denominator = (0..size)
        .map(|row| {
            fri_relations.route.combine(&[
                pp[ANCHOR_VERIFIER_ID_COLUMN][row],
                pp[ANCHOR_LAYER_COLUMN][row],
                pp[ANCHOR_QUERY_COLUMN][row],
                cols.position[row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let control_denominator = (0..size)
        .map(|row| {
            control_relations.step.combine(&[
                pp[ANCHOR_VERIFIER_ID_COLUMN][row],
                pp[ANCHOR_CONTROL_SEQUENCE_COLUMN][row],
                pp[ANCHOR_CONTROL_TAG_COLUMN][row],
                pp[ANCHOR_CONTROL_ARG_0_COLUMN][row],
                pp[ANCHOR_CONTROL_ARG_1_COLUMN][row],
                pp[ANCHOR_CONTROL_ARG_2_COLUMN][row],
                pp[ANCHOR_CONTROL_ARG_3_COLUMN][row],
            ])
        })
        .collect::<Vec<PackedQM31>>();

    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &query_denominator,
        &negative_active,
        &external_denominator,
        logup
    );
    write_pair!(
        &active,
        &local_root_denominator,
        &route_numerator,
        &route_denominator,
        logup
    );
    let mut control_column = logup.new_col();
    for row in 0..size {
        control_column.write_frac(row, negative_active[row], control_denominator[row]);
    }
    control_column.finalize_col();
    logup.finalize_last()
}

/// One raw-query opening of a complete FRI fold subset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriMerkleQueryOpening {
    pub values: Vec<Qm31Wire>,
    pub path: Vec<Digest8>,
}

/// One FRI commitment and every fixed raw-query opening against it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriMerkleLayerOpening {
    pub active_width: u32,
    pub commitment: Digest8,
    pub queries: Vec<FriMerkleQueryOpening>,
}

/// Raw transcript queries and all FRI layers for one verifier lane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriMerkleOpeningSet {
    pub raw_queries: Vec<M31Word>,
    pub layers: Vec<FriMerkleLayerOpening>,
}

impl FriMerkleOpeningSet {
    /// Copies only active wire slots into a validated witness-friendly shape.
    pub fn from_wire<const N_QUERIES: usize, const FOLD_WIDTH: usize, const MAX_DEPTH: usize>(
        raw_queries: &[M31Word],
        layers: &[FriLayerWire<N_QUERIES, FOLD_WIDTH, MAX_DEPTH>],
    ) -> Self {
        let layers = layers
            .iter()
            .map(|layer| {
                let width = usize::try_from(layer.active_width())
                    .expect("a constructed FRI wire width fits usize");
                let queries = layer
                    .queries()
                    .iter()
                    .map(|query| {
                        let depth = usize::try_from(query.path().active_depth())
                            .expect("a constructed Merkle path depth fits usize");
                        FriMerkleQueryOpening {
                            values: query.values()[..width].to_vec(),
                            path: query.path().siblings()[..depth].to_vec(),
                        }
                    })
                    .collect();
                FriMerkleLayerOpening {
                    active_width: layer.active_width(),
                    commitment: layer.commitment(),
                    queries,
                }
            })
            .collect();
        Self {
            raw_queries: raw_queries.to_vec(),
            layers,
        }
    }
}

/// FRI openings selected by the public universal proof kind.
#[derive(Clone, Copy)]
pub enum UniversalFriMerkleWitness<'a> {
    Segment(&'a FriMerkleOpeningSet),
    Binary {
        left: &'a FriMerkleOpeningSet,
        right: &'a FriMerkleOpeningSet,
    },
    Empty,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LocalNodeKey {
    verifier_id: u32,
    layer: u32,
    query: u32,
    depth: u32,
    index: u32,
}

fn validate_opening_witness(
    preprocessed: &FriMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalFriMerkleWitness<'_>,
) -> Result<(), FriMerkleError> {
    if preprocessed.vm_query_count != query_preprocessed.vm_query_count() {
        return Err(FriMerkleError::QueryPreprocessedCountMismatch {
            profile: "VM",
            expected: preprocessed.vm_query_count,
            actual: query_preprocessed.vm_query_count(),
        });
    }
    if preprocessed.recursion_query_count != query_preprocessed.recursion_query_count() {
        return Err(FriMerkleError::QueryPreprocessedCountMismatch {
            profile: "recursion",
            expected: preprocessed.recursion_query_count,
            actual: query_preprocessed.recursion_query_count(),
        });
    }
    match witness {
        UniversalFriMerkleWitness::Segment(opening) => validate_opening_set(
            SEGMENT_VERIFIER_ID,
            preprocessed.vm_query_count,
            &preprocessed.vm_layers,
            opening,
        ),
        UniversalFriMerkleWitness::Binary { left, right } => {
            validate_opening_set(
                LEFT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_query_count,
                &preprocessed.recursion_layers,
                left,
            )?;
            validate_opening_set(
                RIGHT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_query_count,
                &preprocessed.recursion_layers,
                right,
            )
        }
        UniversalFriMerkleWitness::Empty => Ok(()),
    }
}

fn validate_opening_set(
    verifier_id: u32,
    expected_queries: usize,
    geometry: &[LayerGeometry],
    opening: &FriMerkleOpeningSet,
) -> Result<(), FriMerkleError> {
    if opening.raw_queries.len() != expected_queries {
        return Err(FriMerkleError::RawQueryCountMismatch {
            verifier_id,
            expected: expected_queries,
            actual: opening.raw_queries.len(),
        });
    }
    if opening.layers.len() != geometry.len() {
        return Err(FriMerkleError::LayerCountMismatch {
            verifier_id,
            expected: geometry.len(),
            actual: opening.layers.len(),
        });
    }
    for (layer, (opening, geometry)) in opening.layers.iter().zip(geometry).enumerate() {
        if opening.active_width != geometry.width {
            return Err(FriMerkleError::LayerWidthMismatch {
                verifier_id,
                layer,
                expected: geometry.width,
                actual: opening.active_width,
            });
        }
        if opening.queries.len() != expected_queries {
            return Err(FriMerkleError::LayerQueryCountMismatch {
                verifier_id,
                layer,
                expected: expected_queries,
                actual: opening.queries.len(),
            });
        }
        let expected_values =
            usize::try_from(geometry.width).expect("validated FRI fold width fits usize");
        let expected_depth =
            usize::try_from(geometry.path_depth).expect("validated FRI path depth fits usize");
        for (query, opening) in opening.queries.iter().enumerate() {
            if opening.values.len() != expected_values {
                return Err(FriMerkleError::QueryValueCountMismatch {
                    verifier_id,
                    layer,
                    query,
                    expected: expected_values,
                    actual: opening.values.len(),
                });
            }
            if opening.path.len() != expected_depth {
                return Err(FriMerkleError::PathDepthMismatch {
                    verifier_id,
                    layer,
                    query,
                    expected: expected_depth,
                    actual: opening.path.len(),
                });
            }
        }
    }
    Ok(())
}

fn select_opening(
    witness: UniversalFriMerkleWitness<'_>,
    verifier_id: u32,
) -> Result<Option<&FriMerkleOpeningSet>, FriMerkleError> {
    match (witness, verifier_id) {
        (UniversalFriMerkleWitness::Segment(opening), SEGMENT_VERIFIER_ID) => Ok(Some(opening)),
        (UniversalFriMerkleWitness::Binary { left, .. }, LEFT_RECURSION_VERIFIER_ID) => {
            Ok(Some(left))
        }
        (UniversalFriMerkleWitness::Binary { right, .. }, RIGHT_RECURSION_VERIFIER_ID) => {
            Ok(Some(right))
        }
        (UniversalFriMerkleWitness::Empty, SEGMENT_VERIFIER_ID)
        | (UniversalFriMerkleWitness::Empty, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalFriMerkleWitness::Empty, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalFriMerkleWitness::Segment(_), LEFT_RECURSION_VERIFIER_ID)
        | (UniversalFriMerkleWitness::Segment(_), RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalFriMerkleWitness::Binary { .. }, SEGMENT_VERIFIER_ID) => Ok(None),
        (_, verifier_id) => Err(FriMerkleError::UnknownVerifierId { verifier_id }),
    }
}

fn layer_geometry(
    preprocessed: &FriMerklePreprocessed,
    verifier_id: u32,
    layer: u32,
) -> Result<LayerGeometry, FriMerkleError> {
    let geometry = match verifier_id {
        SEGMENT_VERIFIER_ID => &preprocessed.vm_layers,
        LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => &preprocessed.recursion_layers,
        _ => return Err(FriMerkleError::UnknownVerifierId { verifier_id }),
    };
    geometry
        .get(layer as usize)
        .copied()
        .ok_or(FriMerkleError::LayerMissing { verifier_id, layer })
}

fn opening_query(
    opening: &FriMerkleOpeningSet,
    verifier_id: u32,
    layer: u32,
    query: u32,
) -> Result<&FriMerkleQueryOpening, FriMerkleError> {
    opening
        .layers
        .get(layer as usize)
        .and_then(|layer| layer.queries.get(query as usize))
        .ok_or(FriMerkleError::QueryOpeningMissing {
            verifier_id,
            layer,
            query,
        })
}

fn routed_root_position(
    query_preprocessed: &QueryPositionPreprocessed,
    opening: &FriMerkleOpeningSet,
    verifier_id: u32,
    layer: u32,
    query: u32,
) -> Result<u32, FriMerkleError> {
    let raw = opening
        .raw_queries
        .get(query as usize)
        .copied()
        .ok_or(FriMerkleError::RawQueryMissing { verifier_id, query })?;
    let (position, offset) = query_preprocessed
        .evaluate_route(verifier_id, QueryPositionKind::FriMerkle, layer, query, raw)
        .map_err(FriMerkleError::QueryPosition)?;
    if offset != 0 {
        return Err(FriMerkleError::FriMerkleOffsetNotZero {
            verifier_id,
            layer,
            query,
            offset,
        });
    }
    Ok(position)
}

/// Records every packed FRI leaf, local node, routed anchor, and outer path.
#[allow(clippy::too_many_arguments)]
pub fn push_fri_merkle_authentication(
    leaf_table: &mut FriMerkleLeafTable,
    node_table: &mut FriMerkleNodeTable,
    anchor_table: &mut FriMerkleAnchorTable,
    path_table: &mut MerklePathTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &FriMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalFriMerkleWitness<'_>,
) -> Result<(), FriMerkleError> {
    validate_opening_witness(preprocessed, query_preprocessed, witness)?;
    let mut local_nodes = BTreeMap::<LocalNodeKey, [u32; DIGEST_WORDS]>::new();
    push_fri_leaves(
        leaf_table,
        poseidon2,
        preprocessed,
        query_preprocessed,
        witness,
        &mut local_nodes,
    )?;
    push_fri_nodes(
        node_table,
        poseidon2,
        preprocessed,
        query_preprocessed,
        witness,
        &mut local_nodes,
    )?;
    push_fri_anchors_and_paths(
        anchor_table,
        path_table,
        poseidon2,
        preprocessed,
        query_preprocessed,
        witness,
        &local_nodes,
    )
}

#[allow(clippy::too_many_arguments)]
fn push_fri_leaves(
    table: &mut FriMerkleLeafTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &FriMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalFriMerkleWitness<'_>,
    local_nodes: &mut BTreeMap<LocalNodeKey, [u32; DIGEST_WORDS]>,
) -> Result<(), FriMerkleError> {
    let mut state = [0_u32; T];
    for row in &preprocessed.leaf_rows {
        let Some(opening) = select_opening(witness, row.verifier_id)? else {
            table.push_row(&[0; 1 + 1 + T + RATE + T]);
            continue;
        };
        let query_opening = opening_query(opening, row.verifier_id, row.layer, row.query)?;
        if row.first {
            state = [0; T];
            state[T - 1] = LEAF_TAG;
        }
        let chunks = row.chunks.map(|source| match source {
            LeafChunkSource::Value { offset, word } => query_opening
                .values
                .get(offset as usize)
                .and_then(|value| value.words().get(word as usize))
                .copied()
                .map(M31Word::as_u32)
                .ok_or(FriMerkleError::QueryValueMissing {
                    verifier_id: row.verifier_id,
                    layer: row.layer,
                    query: row.query,
                    offset,
                    word,
                }),
            LeafChunkSource::Constant(value) => Ok(value),
        });
        let chunks = transpose_array(chunks)?;
        let position = if row.last {
            routed_root_position(
                query_preprocessed,
                opening,
                row.verifier_id,
                row.layer,
                row.query,
            )?
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
            let index = checked_mul_add_index(
                "FRI packed leaf index",
                position,
                row.leaf_count,
                row.packed_index,
            )?;
            let key = LocalNodeKey {
                verifier_id: row.verifier_id,
                layer: row.layer,
                query: row.query,
                depth: row.tree_height,
                index,
            };
            let digest = output[..DIGEST_WORDS]
                .try_into()
                .expect("Merkle digest is one rate block");
            insert_local_node(local_nodes, key, digest)?;
        }
        state = output;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_fri_nodes(
    table: &mut FriMerkleNodeTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &FriMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalFriMerkleWitness<'_>,
    local_nodes: &mut BTreeMap<LocalNodeKey, [u32; DIGEST_WORDS]>,
) -> Result<(), FriMerkleError> {
    for row in &preprocessed.node_rows {
        let Some(opening) = select_opening(witness, row.verifier_id)? else {
            table.push_row(&[0; 1 + 1 + DIGEST_WORDS * 4]);
            continue;
        };
        let geometry = layer_geometry(preprocessed, row.verifier_id, row.layer)?;
        let root_position = routed_root_position(
            query_preprocessed,
            opening,
            row.verifier_id,
            row.layer,
            row.query,
        )?;
        let local_depth = row.depth.checked_sub(geometry.path_depth).ok_or(
            FriMerkleError::ArithmeticOverflow {
                field: "FRI local node depth",
            },
        )?;
        let index = checked_shift_add_index(
            "FRI local node index",
            root_position,
            local_depth,
            row.relative_index,
        )?;
        let child_depth = row
            .depth
            .checked_add(1)
            .ok_or(FriMerkleError::ArithmeticOverflow {
                field: "FRI child node depth",
            })?;
        let left_index = index
            .checked_mul(2)
            .ok_or(FriMerkleError::ArithmeticOverflow {
                field: "FRI left child index",
            })?;
        let right_index = left_index
            .checked_add(1)
            .ok_or(FriMerkleError::ArithmeticOverflow {
                field: "FRI right child index",
            })?;
        let left_key = LocalNodeKey {
            verifier_id: row.verifier_id,
            layer: row.layer,
            query: row.query,
            depth: child_depth,
            index: left_index,
        };
        let right_key = LocalNodeKey {
            index: right_index,
            ..left_key
        };
        let left = get_local_node(local_nodes, left_key)?;
        let right = get_local_node(local_nodes, right_key)?;
        let mut permutation_input = [0_u32; T];
        permutation_input[..DIGEST_WORDS].copy_from_slice(&left);
        permutation_input[DIGEST_WORDS..].copy_from_slice(&right);
        let output = poseidon2_traced_state(poseidon2, permutation_input, false, true);
        let parent = output[..DIGEST_WORDS]
            .try_into()
            .expect("Merkle digest is one rate block");
        let mut values = Vec::with_capacity(1 + 1 + DIGEST_WORDS * 4);
        values.extend([1, index]);
        values.extend(left);
        values.extend(right);
        values.extend(parent);
        values.extend_from_slice(&output[DIGEST_WORDS..]);
        table.push_row(&values);
        insert_local_node(
            local_nodes,
            LocalNodeKey {
                verifier_id: row.verifier_id,
                layer: row.layer,
                query: row.query,
                depth: row.depth,
                index,
            },
            parent,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn push_fri_anchors_and_paths(
    anchor_table: &mut FriMerkleAnchorTable,
    path_table: &mut MerklePathTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &FriMerklePreprocessed,
    query_preprocessed: &QueryPositionPreprocessed,
    witness: UniversalFriMerkleWitness<'_>,
    local_nodes: &BTreeMap<LocalNodeKey, [u32; DIGEST_WORDS]>,
) -> Result<(), FriMerkleError> {
    for row in &preprocessed.anchor_rows {
        let Some(opening) = select_opening(witness, row.verifier_id)? else {
            anchor_table.push_row(&[0; 1 + 1 + DIGEST_WORDS]);
            continue;
        };
        let position = routed_root_position(
            query_preprocessed,
            opening,
            row.verifier_id,
            row.layer,
            row.query,
        )?;
        let root_key = LocalNodeKey {
            verifier_id: row.verifier_id,
            layer: row.layer,
            query: row.query,
            depth: row.path_depth,
            index: position,
        };
        let local_root = get_local_node(local_nodes, root_key)?;
        let mut values = Vec::with_capacity(1 + 1 + DIGEST_WORDS);
        values.extend([1, position]);
        values.extend(local_root);
        anchor_table.push_row(&values);

        let query_opening = opening_query(opening, row.verifier_id, row.layer, row.query)?;
        let mut child = local_root;
        for (level, sibling) in query_opening.path.iter().enumerate() {
            let level = canonical_usize("FRI authentication level", level)?;
            let depth = row
                .path_depth
                .checked_sub(level)
                .and_then(|depth| depth.checked_sub(1))
                .ok_or(FriMerkleError::ArithmeticOverflow {
                    field: "FRI authentication depth",
                })?;
            child = push_path_step(
                path_table,
                poseidon2,
                row.tree_id,
                depth,
                position >> (level + 1),
                child,
                PathStep {
                    direction: (position >> level) & 1,
                    sibling: sibling.words().map(M31Word::as_u32),
                },
                false,
            );
        }
        let expected = opening
            .layers
            .get(row.layer as usize)
            .ok_or(FriMerkleError::LayerMissing {
                verifier_id: row.verifier_id,
                layer: row.layer,
            })?
            .commitment
            .words()
            .map(M31Word::as_u32);
        if child != expected {
            return Err(FriMerkleError::PathRootMismatch {
                verifier_id: row.verifier_id,
                layer: row.layer,
                query: row.query,
            });
        }
    }
    Ok(())
}

fn checked_mul_add_index(
    field: &'static str,
    base: u32,
    multiplier: u32,
    addend: u32,
) -> Result<u32, FriMerkleError> {
    let value = base
        .checked_mul(multiplier)
        .and_then(|value| value.checked_add(addend))
        .ok_or(FriMerkleError::ArithmeticOverflow { field })?;
    canonical_index(field, value)
}

fn checked_shift_add_index(
    field: &'static str,
    base: u32,
    shift: u32,
    addend: u32,
) -> Result<u32, FriMerkleError> {
    let factor = 1_u32
        .checked_shl(shift)
        .ok_or(FriMerkleError::ArithmeticOverflow { field })?;
    let value = base
        .checked_mul(factor)
        .and_then(|value| value.checked_add(addend))
        .ok_or(FriMerkleError::ArithmeticOverflow { field })?;
    canonical_index(field, value)
}

fn canonical_index(field: &'static str, value: u32) -> Result<u32, FriMerkleError> {
    M31Word::try_from(value)
        .map(M31Word::as_u32)
        .map_err(|_| FriMerkleError::IndexNotCanonical { field, value })
}

fn insert_local_node(
    nodes: &mut BTreeMap<LocalNodeKey, [u32; DIGEST_WORDS]>,
    key: LocalNodeKey,
    digest: [u32; DIGEST_WORDS],
) -> Result<(), FriMerkleError> {
    if nodes.insert(key, digest).is_some() {
        return Err(FriMerkleError::DuplicateLocalNode {
            verifier_id: key.verifier_id,
            layer: key.layer,
            query: key.query,
            depth: key.depth,
            index: key.index,
        });
    }
    Ok(())
}

fn get_local_node(
    nodes: &BTreeMap<LocalNodeKey, [u32; DIGEST_WORDS]>,
    key: LocalNodeKey,
) -> Result<[u32; DIGEST_WORDS], FriMerkleError> {
    nodes
        .get(&key)
        .copied()
        .ok_or(FriMerkleError::LocalNodeMissing {
            verifier_id: key.verifier_id,
            layer: key.layer,
            query: key.query,
            depth: key.depth,
            index: key.index,
        })
}

fn transpose_array<T, E, const N: usize>(values: [Result<T, E>; N]) -> Result<[T; N], E> {
    let values = values.into_iter().collect::<Result<Vec<_>, _>>()?;
    Ok(values
        .try_into()
        .unwrap_or_else(|_| unreachable!("array collection preserves its fixed length")))
}

/// Invalid fixed FRI Merkle geometry or witness data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriMerkleError {
    SchemaMismatch {
        profile: &'static str,
        expected: VerifierSchema,
        actual: VerifierSchema,
    },
    Pcs(PcsParameterError),
    VmShape(ProofShapeError),
    RecursionShape(ProofShapeError),
    TreeNamespace(MerkleRootError),
    QueryPosition(QueryPositionError),
    PackedSubtreeHeightMismatch {
        profile: &'static str,
        layer: usize,
        tree_height: u32,
        path_depth: u32,
        subtree_height: u32,
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
    QueryPreprocessedCountMismatch {
        profile: &'static str,
        expected: usize,
        actual: usize,
    },
    RawQueryCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    LayerCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    LayerWidthMismatch {
        verifier_id: u32,
        layer: usize,
        expected: u32,
        actual: u32,
    },
    LayerQueryCountMismatch {
        verifier_id: u32,
        layer: usize,
        expected: usize,
        actual: usize,
    },
    QueryValueCountMismatch {
        verifier_id: u32,
        layer: usize,
        query: usize,
        expected: usize,
        actual: usize,
    },
    PathDepthMismatch {
        verifier_id: u32,
        layer: usize,
        query: usize,
        expected: usize,
        actual: usize,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    LayerMissing {
        verifier_id: u32,
        layer: u32,
    },
    QueryOpeningMissing {
        verifier_id: u32,
        layer: u32,
        query: u32,
    },
    RawQueryMissing {
        verifier_id: u32,
        query: u32,
    },
    FriMerkleOffsetNotZero {
        verifier_id: u32,
        layer: u32,
        query: u32,
        offset: u32,
    },
    QueryValueMissing {
        verifier_id: u32,
        layer: u32,
        query: u32,
        offset: u32,
        word: u32,
    },
    LocalNodeMissing {
        verifier_id: u32,
        layer: u32,
        query: u32,
        depth: u32,
        index: u32,
    },
    DuplicateLocalNode {
        verifier_id: u32,
        layer: u32,
        query: u32,
        depth: u32,
        index: u32,
    },
    PathRootMismatch {
        verifier_id: u32,
        layer: u32,
        query: u32,
    },
}

impl fmt::Display for FriMerkleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FriMerkleError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::{
        Poseidon2M31Channel, Poseidon2M31Hash, Poseidon2M31MerkleHasher,
    };
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;
    use crate::merkle_path;
    use crate::v2::kernel::VerifierProgramSpec;
    use crate::v2::protocol::{OptionalM31Word, PcsParameters, ValidatedPcsParameters};

    const TABLE_COUNT: usize = 1;
    const TREE_COUNT: usize = 4;
    const FRI_LAYER_COUNT: usize = 2;
    const QUERY_COUNT: usize = 2;

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
            queried_value_count: M31Word::from(QUERY_COUNT as u16),
            trace_path_count: M31Word::from((TREE_COUNT * QUERY_COUNT) as u16),
            raw_query_count: M31Word::from(QUERY_COUNT as u16),
            last_layer_coefficient_count: M31Word::from(1_u16),
            table_log_sizes: [M31Word::from(7_u16)],
            tree_heights: [6_u16, 8, 8, 8].map(M31Word::from),
            fri_layer_fold_widths: [16_u16, 8].map(M31Word::from),
            fri_layer_tree_heights: [6_u16, 2].map(M31Word::from),
        }
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 1, 1, 1, 1)
            .expect("fixture verifier program is valid");
        VerifierControlPlan::new(spec, pcs_parameters(), &shape())
            .expect("fixture verifier plan is valid")
    }

    fn preprocessing() -> (FriMerklePreprocessed, QueryPositionPreprocessed) {
        let vm = plan(VerifierSchema::Vm);
        let recursion = plan(VerifierSchema::Recursion);
        let fri = FriMerklePreprocessed::new(&vm, &shape(), &recursion, &shape())
            .expect("fixture FRI Merkle geometry is valid");
        let query = QueryPositionPreprocessed::new(pcs(), &shape(), pcs(), &shape())
            .expect("fixture query geometry is valid");
        (fri, query)
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new(core::array::from_fn(|word| {
            M31Word::from(seed + word as u16)
        }))
    }

    fn secure_value(seed: u16) -> Qm31Wire {
        Qm31Wire::new(core::array::from_fn(|word| {
            M31Word::from(seed + word as u16)
        }))
    }

    fn hash_leaf(values: &[Qm31Wire]) -> Poseidon2M31Hash {
        let words = values
            .iter()
            .flat_map(|value| value.words())
            .map(|word| BaseField::from(word.as_u32()))
            .collect::<Vec<_>>();
        let mut hasher = Poseidon2M31MerkleHasher::default();
        hasher.update_leaf(&words);
        hasher.finalize()
    }

    fn hash_local_subtree(values: &[Qm31Wire], leaf_size: usize) -> Poseidon2M31Hash {
        let mut level = values
            .chunks_exact(leaf_size)
            .map(hash_leaf)
            .collect::<Vec<_>>();
        while level.len() > 1 {
            level = level
                .chunks_exact(2)
                .map(|children| Poseidon2M31MerkleHasher::hash_children((children[0], children[1])))
                .collect();
        }
        level[0]
    }

    fn opening_set(
        preprocessing: &FriMerklePreprocessed,
        query_preprocessing: &QueryPositionPreprocessed,
        verifier_id: u32,
        seed: u16,
        raw: M31Word,
    ) -> FriMerkleOpeningSet {
        let geometry = match verifier_id {
            SEGMENT_VERIFIER_ID => &preprocessing.vm_layers,
            LEFT_RECURSION_VERIFIER_ID | RIGHT_RECURSION_VERIFIER_ID => {
                &preprocessing.recursion_layers
            }
            _ => unreachable!("fixture verifier id is fixed"),
        };
        let layers = geometry
            .iter()
            .copied()
            .enumerate()
            .map(|(layer, geometry)| {
                let values = (0..geometry.width)
                    .map(|offset| secure_value(seed + layer as u16 * 100 + offset as u16 * 4))
                    .collect::<Vec<_>>();
                let mut child = hash_local_subtree(&values, geometry.leaf_size as usize);
                let (position, offset) = query_preprocessing
                    .evaluate_route(
                        verifier_id,
                        QueryPositionKind::FriMerkle,
                        layer as u32,
                        0,
                        raw,
                    )
                    .expect("fixture query route exists");
                let position = (offset == 0)
                    .then_some(position)
                    .expect("FRI Merkle routes have no fold offset");
                let mut path = Vec::new();
                for level in 0..geometry.path_depth {
                    let sibling = digest(seed + 500 + layer as u16 * 100 + level as u16 * 10);
                    let sibling_hash = Poseidon2M31Hash(sibling.words().map(M31Word::as_u32));
                    child = if (position >> level) & 1 == 0 {
                        Poseidon2M31MerkleHasher::hash_children((child, sibling_hash))
                    } else {
                        Poseidon2M31MerkleHasher::hash_children((sibling_hash, child))
                    };
                    path.push(sibling);
                }
                let commitment =
                    Digest8::try_from(child.0).expect("Poseidon2 output words are canonical M31");
                let query = FriMerkleQueryOpening { values, path };
                FriMerkleLayerOpening {
                    active_width: geometry.width,
                    commitment,
                    queries: vec![query; QUERY_COUNT],
                }
            })
            .collect();
        FriMerkleOpeningSet {
            raw_queries: vec![raw; QUERY_COUNT],
            layers,
        }
    }

    struct Materialized {
        preprocessing: FriMerklePreprocessed,
        query_preprocessing: QueryPositionPreprocessed,
        leaf: FriMerkleLeafTable,
        node: FriMerkleNodeTable,
        anchor: FriMerkleAnchorTable,
        path: MerklePathTable,
        poseidon2: Poseidon2Table,
        vm: FriMerkleOpeningSet,
    }

    fn materialize(kind: ProofKind) -> Materialized {
        let (preprocessing, query_preprocessing) = preprocessing();
        let vm = opening_set(
            &preprocessing,
            &query_preprocessing,
            SEGMENT_VERIFIER_ID,
            10,
            M31Word::from(183_u16),
        );
        let left = opening_set(
            &preprocessing,
            &query_preprocessing,
            LEFT_RECURSION_VERIFIER_ID,
            1_000,
            M31Word::from(77_u16),
        );
        let right = opening_set(
            &preprocessing,
            &query_preprocessing,
            RIGHT_RECURSION_VERIFIER_ID,
            2_000,
            M31Word::from(99_u16),
        );
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalFriMerkleWitness::Segment(&vm),
            ProofKind::BinaryNode => UniversalFriMerkleWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalFriMerkleWitness::Empty,
        };
        let mut leaf = FriMerkleLeafTable::new();
        let mut node = FriMerkleNodeTable::new();
        let mut anchor = FriMerkleAnchorTable::new();
        let mut path = MerklePathTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        push_fri_merkle_authentication(
            &mut leaf,
            &mut node,
            &mut anchor,
            &mut path,
            &mut poseidon2,
            &preprocessing,
            &query_preprocessing,
            witness,
        )
        .expect("fixture FRI Merkle openings authenticate");
        Materialized {
            preprocessing,
            query_preprocessing,
            leaf,
            node,
            anchor,
            path,
            poseidon2,
            vm,
        }
    }

    fn assert_leaf_constraints(kind: ProofKind) {
        let materialized = materialize(kind);
        let vm_relations = Relations::dummy();
        let fri_relations = FriMerkleRelations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let preprocessed = materialized.preprocessing.gen_leaf_columns();
        let trace = materialized.leaf.into_witness();
        let (interaction, claimed_sum) = gen_leaf_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &fri_relations,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = LeafEval {
            log_size: materialized.preprocessing.leaf_log_size(),
            proof_kind: kind,
            vm_relations,
            fri_relations,
            recursion_relations,
        };
        assert_constraints_on_polys(
            &polys,
            CanonicCoset::new(materialized.preprocessing.leaf_log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn assert_node_constraints(kind: ProofKind) {
        let materialized = materialize(kind);
        let vm_relations = Relations::dummy();
        let fri_relations = FriMerkleRelations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let preprocessed = materialized.preprocessing.gen_node_columns();
        let trace = materialized.node.into_witness();
        let (interaction, claimed_sum) = gen_node_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &fri_relations,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = NodeEval {
            log_size: materialized.preprocessing.node_log_size(),
            proof_kind: kind,
            vm_relations,
            fri_relations,
            recursion_relations,
        };
        assert_constraints_on_polys(
            &polys,
            CanonicCoset::new(materialized.preprocessing.node_log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn assert_anchor_constraints(kind: ProofKind) {
        let materialized = materialize(kind);
        let control_relations = ControlRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let fri_relations = FriMerkleRelations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let preprocessed = materialized.preprocessing.gen_anchor_columns();
        let trace = materialized.anchor.into_witness();
        let (interaction, claimed_sum) = gen_anchor_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &control_relations,
            &query_relations,
            &fri_relations,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = AnchorEval {
            log_size: materialized.preprocessing.anchor_log_size(),
            proof_kind: kind,
            control_relations,
            query_relations,
            fri_relations,
            recursion_relations,
        };
        assert_constraints_on_polys(
            &polys,
            CanonicCoset::new(materialized.preprocessing.anchor_log_size()),
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
    fn every_universal_mode_satisfies_fri_leaf_constraints(#[case] kind: ProofKind) {
        assert_leaf_constraints(kind);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_fri_node_constraints(#[case] kind: ProofKind) {
        assert_node_constraints(kind);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_fri_anchor_constraints(#[case] kind: ProofKind) {
        assert_anchor_constraints(kind);
    }

    fn single_layer_pcs(fold_step: u32) -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: M31Word::from(1_u16),
            fri_n_queries: M31Word::from(QUERY_COUNT as u16),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: M31Word::try_from(fold_step).expect("supported fold step is canonical"),
            lifting_log_size: OptionalM31Word::None,
        }
    }

    fn single_layer_shape(fold_step: u32) -> FixedProofShape<1, 4, 1> {
        let lifting_log_size = fold_step + 1;
        let packed_log_size = if fold_step > 1 { 2 } else { 0 };
        FixedProofShape {
            claimed_sum_count: M31Word::from(1_u16),
            sampled_value_count: M31Word::from(1_u16),
            queried_value_count: M31Word::from(QUERY_COUNT as u16),
            trace_path_count: M31Word::from((4 * QUERY_COUNT) as u16),
            raw_query_count: M31Word::from(QUERY_COUNT as u16),
            last_layer_coefficient_count: M31Word::from(1_u16),
            table_log_sizes: [
                M31Word::try_from(fold_step).expect("supported fold step is canonical")
            ],
            tree_heights: [M31Word::try_from(lifting_log_size)
                .expect("fixture lifting size is canonical"); 4],
            fri_layer_fold_widths: [
                M31Word::try_from(1_u32 << fold_step).expect("supported fold width is canonical")
            ],
            fri_layer_tree_heights: [M31Word::try_from(lifting_log_size - packed_log_size)
                .expect("fixture tree height is canonical")],
        }
    }

    #[rstest]
    #[case::width_2(1)]
    #[case::width_4(2)]
    #[case::width_8(3)]
    #[case::width_16(4)]
    fn fri_leaf_digests_match_native_stwo_packing(#[case] fold_step: u32) {
        let shape = single_layer_shape(fold_step);
        let parameters = single_layer_pcs(fold_step);
        let validated = parameters
            .validate()
            .expect("single-layer PCS parameters are valid");
        let vm_spec = VerifierProgramSpec::new(VerifierSchema::Vm, 1, 1, 1, 1)
            .expect("fixture VM verifier program is valid");
        let recursion_spec = VerifierProgramSpec::new(VerifierSchema::Recursion, 1, 1, 1, 1)
            .expect("fixture recursion verifier program is valid");
        let vm_plan = VerifierControlPlan::new(vm_spec, parameters, &shape)
            .expect("fixture VM verifier plan is valid");
        let recursion_plan = VerifierControlPlan::new(recursion_spec, parameters, &shape)
            .expect("fixture recursion verifier plan is valid");
        let preprocessing = FriMerklePreprocessed::new(&vm_plan, &shape, &recursion_plan, &shape)
            .expect("single-layer FRI Merkle geometry is valid");
        let query_preprocessing =
            QueryPositionPreprocessed::new(validated, &shape, validated, &shape)
                .expect("single-layer query geometry is valid");
        let opening = opening_set(
            &preprocessing,
            &query_preprocessing,
            SEGMENT_VERIFIER_ID,
            10,
            M31Word::from(3_u16),
        );
        let mut leaf = FriMerkleLeafTable::new();
        push_fri_merkle_authentication(
            &mut leaf,
            &mut FriMerkleNodeTable::new(),
            &mut FriMerkleAnchorTable::new(),
            &mut MerklePathTable::new(),
            &mut Poseidon2Table::new(),
            &preprocessing,
            &query_preprocessing,
            UniversalFriMerkleWitness::Segment(&opening),
        )
        .expect("single-layer FRI opening authenticates");
        let actual = preprocessing
            .leaf_rows
            .iter()
            .enumerate()
            .filter(|(_, row)| row.segment_mask == 1 && row.last)
            .map(|(row, _)| {
                Poseidon2M31Hash([
                    leaf.output_0[row],
                    leaf.output_1[row],
                    leaf.output_2[row],
                    leaf.output_3[row],
                    leaf.output_4[row],
                    leaf.output_5[row],
                    leaf.output_6[row],
                    leaf.output_7[row],
                ])
            })
            .collect::<Vec<_>>();
        let leaf_size = preprocessing.vm_layers[0].leaf_size as usize;
        let expected = (0..QUERY_COUNT)
            .flat_map(|_| opening.layers[0].queries[0].values.chunks_exact(leaf_size))
            .map(hash_leaf)
            .collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[derive(Clone, Copy)]
    enum OpeningTamper {
        Value,
        Path,
        Commitment,
    }

    #[rstest]
    #[case::value(OpeningTamper::Value)]
    #[case::path(OpeningTamper::Path)]
    #[case::commitment(OpeningTamper::Commitment)]
    fn changed_fri_opening_cannot_reach_the_committed_root(#[case] tamper: OpeningTamper) {
        let (preprocessing, query_preprocessing) = preprocessing();
        let mut vm = opening_set(
            &preprocessing,
            &query_preprocessing,
            SEGMENT_VERIFIER_ID,
            10,
            M31Word::from(183_u16),
        );
        match tamper {
            OpeningTamper::Value => vm.layers[0].queries[0].values[0] = secure_value(9_000),
            OpeningTamper::Path => vm.layers[0].queries[0].path[0] = digest(9_000),
            OpeningTamper::Commitment => vm.layers[0].commitment = digest(9_000),
        }
        let result = push_fri_merkle_authentication(
            &mut FriMerkleLeafTable::new(),
            &mut FriMerkleNodeTable::new(),
            &mut FriMerkleAnchorTable::new(),
            &mut MerklePathTable::new(),
            &mut Poseidon2Table::new(),
            &preprocessing,
            &query_preprocessing,
            UniversalFriMerkleWitness::Segment(&vm),
        );
        assert!(matches!(
            result,
            Err(FriMerkleError::PathRootMismatch { .. })
        ));
    }

    #[derive(Clone, Copy)]
    enum ShapeTamper {
        RawQueries,
        Layers,
        Width,
        Values,
        Path,
    }

    #[rstest]
    #[case::raw_queries(ShapeTamper::RawQueries)]
    #[case::layers(ShapeTamper::Layers)]
    #[case::width(ShapeTamper::Width)]
    #[case::values(ShapeTamper::Values)]
    #[case::path(ShapeTamper::Path)]
    fn malformed_fri_opening_is_rejected_before_hashing(#[case] tamper: ShapeTamper) {
        let (preprocessing, query_preprocessing) = preprocessing();
        let mut vm = opening_set(
            &preprocessing,
            &query_preprocessing,
            SEGMENT_VERIFIER_ID,
            10,
            M31Word::from(183_u16),
        );
        match tamper {
            ShapeTamper::RawQueries => {
                vm.raw_queries.pop();
            }
            ShapeTamper::Layers => {
                vm.layers.pop();
            }
            ShapeTamper::Width => vm.layers[0].active_width = 8,
            ShapeTamper::Values => {
                vm.layers[0].queries[0].values.pop();
            }
            ShapeTamper::Path => {
                vm.layers[0].queries[0].path.pop();
            }
        }
        let result = push_fri_merkle_authentication(
            &mut FriMerkleLeafTable::new(),
            &mut FriMerkleNodeTable::new(),
            &mut FriMerkleAnchorTable::new(),
            &mut MerklePathTable::new(),
            &mut Poseidon2Table::new(),
            &preprocessing,
            &query_preprocessing,
            UniversalFriMerkleWitness::Segment(&vm),
        );
        let expected = match tamper {
            ShapeTamper::RawQueries => {
                matches!(result, Err(FriMerkleError::RawQueryCountMismatch { .. }))
            }
            ShapeTamper::Layers => {
                matches!(result, Err(FriMerkleError::LayerCountMismatch { .. }))
            }
            ShapeTamper::Width => {
                matches!(result, Err(FriMerkleError::LayerWidthMismatch { .. }))
            }
            ShapeTamper::Values => {
                matches!(result, Err(FriMerkleError::QueryValueCountMismatch { .. }))
            }
            ShapeTamper::Path => {
                matches!(result, Err(FriMerkleError::PathDepthMismatch { .. }))
            }
        };
        assert!(expected);
    }

    #[derive(Clone, Copy)]
    enum LookupTamper {
        LeafRoute,
        AnchorDigest,
    }

    #[rstest]
    #[case::leaf_route(LookupTamper::LeafRoute)]
    #[case::anchor_digest(LookupTamper::AnchorDigest)]
    fn routed_subtree_lookup_rejects_boundary_tampering(#[case] tamper: LookupTamper) {
        let mut materialized = materialize(ProofKind::SegmentLeaf);
        match tamper {
            LookupTamper::LeafRoute => {
                let row = materialized
                    .preprocessing
                    .leaf_rows
                    .iter()
                    .position(|row| row.segment_mask == 1 && row.last)
                    .expect("fixture has an active final leaf row");
                materialized.leaf.position[row] += 1;
            }
            LookupTamper::AnchorDigest => materialized.anchor.digest_0[0] += 1,
        }
        assert!(!relation_sum(materialized).is_zero());
    }

    #[test]
    fn fri_merkle_relations_close_exactly() {
        assert!(relation_sum(materialize(ProofKind::SegmentLeaf)).is_zero());
    }

    fn relation_sum(materialized: Materialized) -> QM31 {
        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let control_relations = ControlRelations::draw(&mut channel);
        let query_relations = QueryPositionRelations::draw(&mut channel);
        let fri_relations = FriMerkleRelations::draw(&mut channel);
        let recursion_relations = RecursionRelations::draw(&mut channel);
        let (_, leaf_sum) = gen_leaf_interaction_trace(
            &materialized.leaf.into_witness(),
            &materialized.preprocessing.gen_leaf_columns(),
            ProofKind::SegmentLeaf,
            &vm_relations,
            &fri_relations,
            &recursion_relations,
        );
        let (_, node_sum) = gen_node_interaction_trace(
            &materialized.node.into_witness(),
            &materialized.preprocessing.gen_node_columns(),
            ProofKind::SegmentLeaf,
            &vm_relations,
            &fri_relations,
            &recursion_relations,
        );
        let (_, anchor_sum) = gen_anchor_interaction_trace(
            &materialized.anchor.into_witness(),
            &materialized.preprocessing.gen_anchor_columns(),
            ProofKind::SegmentLeaf,
            &control_relations,
            &query_relations,
            &fri_relations,
            &recursion_relations,
        );
        let (_, path_sum) = merkle_path::gen_interaction_trace(
            &materialized.path.into_witness(),
            &vm_relations,
            &recursion_relations,
        );
        let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
            &materialized.poseidon2.into_witness(),
            &vm_relations,
        );
        let external = external_relation_sum(
            &materialized.preprocessing,
            &materialized.query_preprocessing,
            &materialized.vm,
            &control_relations,
            &query_relations,
            &fri_relations,
            &recursion_relations,
        );
        leaf_sum + node_sum + anchor_sum + path_sum + poseidon_sum + external
    }

    #[allow(clippy::too_many_arguments)]
    fn external_relation_sum(
        preprocessing: &FriMerklePreprocessed,
        query_preprocessing: &QueryPositionPreprocessed,
        opening: &FriMerkleOpeningSet,
        control_relations: &ControlRelations,
        query_relations: &QueryPositionRelations,
        fri_relations: &FriMerkleRelations,
        recursion_relations: &RecursionRelations,
    ) -> QM31 {
        let values =
            opening
                .layers
                .iter()
                .enumerate()
                .fold(QM31::zero(), |sum, (layer, opening)| {
                    opening
                        .queries
                        .iter()
                        .enumerate()
                        .fold(sum, |sum, (query, opening)| {
                            opening
                                .values
                                .iter()
                                .enumerate()
                                .fold(sum, |sum, (offset, value)| {
                                    value.words().iter().enumerate().fold(
                                        sum,
                                        |sum, (word, value)| {
                                            let denominator: QM31 =
                                                fri_relations.value_word.combine(&[
                                                    M31::from(SEGMENT_VERIFIER_ID),
                                                    M31::from(layer as u32),
                                                    M31::from(query as u32),
                                                    M31::from(offset as u32),
                                                    M31::from(word as u32),
                                                    M31::from(value.as_u32()),
                                                ]);
                                            sum - denominator.inverse()
                                        },
                                    )
                                })
                        })
                });
        preprocessing
            .anchor_rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(values, |sum, row| {
                let raw = opening.raw_queries[row.query as usize];
                let (position, offset) = query_preprocessing
                    .evaluate_route(
                        row.verifier_id,
                        QueryPositionKind::FriMerkle,
                        row.layer,
                        row.query,
                        raw,
                    )
                    .expect("fixture route exists");
                let query_denominator: QM31 = query_relations.position.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(QueryPositionKind::FriMerkle.as_u32()),
                    M31::from(row.layer),
                    M31::from(row.query),
                    M31::from(position),
                    M31::from(offset),
                ]);
                let control_denominator: QM31 = control_relations.step.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(row.control_sequence),
                    M31::from(row.control_tag),
                    M31::from(row.control_args[0]),
                    M31::from(row.control_args[1]),
                    M31::from(row.control_args[2]),
                    M31::from(row.control_args[3]),
                ]);
                let commitment = opening.layers[row.layer as usize].commitment;
                let mut root_tuple = vec![M31::from(row.tree_id), M31::from(0), M31::from(0)];
                root_tuple.extend(commitment.words().map(|word| M31::from(word.as_u32())));
                let root_denominator: QM31 = recursion_relations.merkle_node.combine(&root_tuple);
                sum + query_denominator.inverse()
                    + control_denominator.inverse()
                    + root_denominator.inverse()
            })
    }
}
