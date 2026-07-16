//! Canonical raw-query decomposition and fixed PCS position routing.
//!
//! One row per transcript query consumes the typed raw M31 word and proves its
//! unique 31-bit representation. A second fixed table reuses those bits for
//! every verifier obligation: trace openings, DEEP evaluation, each FRI fold,
//! each FRI subtree opening, and the last-layer check. Position weights are
//! preprocessing, so a proof cannot change a domain shift, the special
//! preprocessed-tree remapping, or the number of downstream uses.

use core::fmt;

use air::digest::M31Word;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::QM31;
use stwo::core::poly::circle::CanonicCoset;
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
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::protocol::{FixedProofShape, ProofShapeError, ValidatedPcsParameters};
use super::verifier_randomness_air::{VerifierRandomnessKind, VerifierRandomnessRelations};
use super::wire::ProofKind;

const M31_BITS: usize = 31;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const RAW_ROW_MASK_COLUMN: usize = 0;
const RAW_SEGMENT_MASK_COLUMN: usize = 1;
const RAW_BINARY_MASK_COLUMN: usize = 2;
const RAW_VERIFIER_ID_COLUMN: usize = 3;
const RAW_QUERY_COLUMN: usize = 4;
const RAW_USE_COUNT_COLUMN: usize = 5;
const RAW_PREPROCESSED_COLUMN_COUNT: usize = 6;

const MAPPING_ROW_MASK_COLUMN: usize = 0;
const MAPPING_SEGMENT_MASK_COLUMN: usize = 1;
const MAPPING_BINARY_MASK_COLUMN: usize = 2;
const MAPPING_VERIFIER_ID_COLUMN: usize = 3;
const MAPPING_KIND_COLUMN: usize = 4;
const MAPPING_ITEM_COLUMN: usize = 5;
const MAPPING_QUERY_COLUMN: usize = 6;
const POSITION_WEIGHT_START_COLUMN: usize = 7;
const OFFSET_WEIGHT_START_COLUMN: usize = POSITION_WEIGHT_START_COLUMN + M31_BITS;
const MAPPING_PREPROCESSED_COLUMN_COUNT: usize = OFFSET_WEIGHT_START_COLUMN + M31_BITS;

const RAW_PREPROCESSED_COLUMN_IDS: [&str; RAW_PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_query_raw_row_mask",
    "recursion_v2_query_raw_segment_mask",
    "recursion_v2_query_raw_binary_mask",
    "recursion_v2_query_raw_verifier_id",
    "recursion_v2_query_raw_query",
    "recursion_v2_query_raw_use_count",
];

define_component_tables! {
    query_bits: {
        committed: {
            word, canonical_inverse,
            bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7,
            bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15,
            bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23,
            bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30,
        },
        constraints: {},
    },
    query_mapping: {
        committed: {
            position, offset,
            bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7,
            bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15,
            bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23,
            bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30,
        },
        constraints: {},
    },
}

use prover_columns::{QueryBitsColumns, QueryMappingColumns};

// Canonical query bits: verifier, raw-query index, and all 31 bits.
relation!(QueryBitsRelation, 33);
// Routed position: verifier, purpose, item, raw query, position, and fold offset.
relation!(QueryPositionRelation, 6);

/// Relations connecting transcript draws to every PCS query consumer.
#[derive(Clone)]
pub struct QueryPositionRelations {
    pub bits: QueryBitsRelation,
    pub position: QueryPositionRelation,
}

impl QueryPositionRelations {
    pub fn dummy() -> Self {
        Self {
            bits: QueryBitsRelation::dummy(),
            position: QueryPositionRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            bits: QueryBitsRelation::draw(channel),
            position: QueryPositionRelation::draw(channel),
        }
    }
}

/// Non-interchangeable uses of one transcript-derived query position.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum QueryPositionKind {
    TraceTree = 1,
    Deep = 2,
    FriFold = 3,
    FriMerkle = 4,
    LastLayer = 5,
}

impl QueryPositionKind {
    pub const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RawRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    query: u32,
    use_count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MappingRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    kind: QueryPositionKind,
    item: u32,
    query: u32,
    position_weights: [u32; M31_BITS],
    offset_weights: [u32; M31_BITS],
}

impl MappingRow {
    fn evaluate(&self, word: M31Word) -> Result<(u32, u32), QueryPositionError> {
        Ok((
            apply_weights(word, &self.position_weights)?,
            apply_weights(word, &self.offset_weights)?,
        ))
    }
}

/// Trusted raw-query and semantic-mapping layouts for all verifier lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QueryPositionPreprocessed {
    raw_log_size: u32,
    mapping_log_size: u32,
    raw_rows: Vec<RawRow>,
    mapping_rows: Vec<MappingRow>,
    vm_query_count: usize,
    recursion_query_count: usize,
}

impl QueryPositionPreprocessed {
    #[allow(clippy::too_many_arguments)]
    pub fn new<
        const VM_TABLES: usize,
        const VM_TREES: usize,
        const VM_FRI_LAYERS: usize,
        const RECURSION_TABLES: usize,
        const RECURSION_TREES: usize,
        const RECURSION_FRI_LAYERS: usize,
    >(
        vm_pcs: ValidatedPcsParameters,
        vm_shape: &FixedProofShape<VM_TABLES, VM_TREES, VM_FRI_LAYERS>,
        recursion_pcs: ValidatedPcsParameters,
        recursion_shape: &FixedProofShape<RECURSION_TABLES, RECURSION_TREES, RECURSION_FRI_LAYERS>,
    ) -> Result<Self, QueryPositionError> {
        let vm_validated = vm_shape
            .validate(vm_pcs)
            .map_err(QueryPositionError::VmShape)?;
        let recursion_validated = recursion_shape
            .validate(recursion_pcs)
            .map_err(QueryPositionError::RecursionShape)?;
        let vm_query_count = vm_pcs.config().fri_config.n_queries;
        let recursion_query_count = recursion_pcs.config().fri_config.n_queries;

        let mut raw_rows = Vec::new();
        let mut mapping_rows = Vec::new();
        append_profile_rows(
            &mut raw_rows,
            &mut mapping_rows,
            SEGMENT_VERIFIER_ID,
            1,
            0,
            vm_query_count,
            vm_validated.lifting_log_size(),
            &vm_shape.tree_heights.map(M31Word::as_u32),
            &vm_shape.fri_layer_fold_widths.map(M31Word::as_u32),
        )?;
        for verifier_id in [LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID] {
            append_profile_rows(
                &mut raw_rows,
                &mut mapping_rows,
                verifier_id,
                0,
                1,
                recursion_query_count,
                recursion_validated.lifting_log_size(),
                &recursion_shape.tree_heights.map(M31Word::as_u32),
                &recursion_shape.fri_layer_fold_widths.map(M31Word::as_u32),
            )?;
        }

        Ok(Self {
            raw_log_size: padded_log_size("raw query rows", raw_rows.len())?,
            mapping_log_size: padded_log_size("query mapping rows", mapping_rows.len())?,
            raw_rows,
            mapping_rows,
            vm_query_count,
            recursion_query_count,
        })
    }

    pub const fn raw_log_size(&self) -> u32 {
        self.raw_log_size
    }

    pub const fn mapping_log_size(&self) -> u32 {
        self.mapping_log_size
    }

    pub const fn vm_query_count(&self) -> usize {
        self.vm_query_count
    }

    pub const fn recursion_query_count(&self) -> usize {
        self.recursion_query_count
    }

    /// Evaluates one trusted semantic route for witness materialization.
    pub fn evaluate_route(
        &self,
        verifier_id: u32,
        kind: QueryPositionKind,
        item: u32,
        query: u32,
        word: M31Word,
    ) -> Result<(u32, u32), QueryPositionError> {
        self.mapping_rows
            .iter()
            .find(|row| {
                row.verifier_id == verifier_id
                    && row.kind == kind
                    && row.item == item
                    && row.query == query
            })
            .ok_or(QueryPositionError::RouteMissing {
                verifier_id,
                kind,
                item,
                query,
            })?
            .evaluate(word)
    }

    pub fn raw_column_ids() -> Vec<PreProcessedColumnId> {
        RAW_PREPROCESSED_COLUMN_IDS
            .iter()
            .map(|id| PreProcessedColumnId { id: (*id).into() })
            .collect()
    }

    pub fn mapping_column_ids() -> Vec<PreProcessedColumnId> {
        let mut ids = [
            "recursion_v2_query_mapping_row_mask",
            "recursion_v2_query_mapping_segment_mask",
            "recursion_v2_query_mapping_binary_mask",
            "recursion_v2_query_mapping_verifier_id",
            "recursion_v2_query_mapping_kind",
            "recursion_v2_query_mapping_item",
            "recursion_v2_query_mapping_query",
        ]
        .into_iter()
        .map(|id| PreProcessedColumnId { id: id.into() })
        .collect::<Vec<_>>();
        ids.extend((0..M31_BITS).map(|bit| PreProcessedColumnId {
            id: format!("recursion_v2_query_mapping_position_weight_{bit}"),
        }));
        ids.extend((0..M31_BITS).map(|bit| PreProcessedColumnId {
            id: format!("recursion_v2_query_mapping_offset_weight_{bit}"),
        }));
        ids
    }

    pub fn gen_raw_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.raw_log_size;
        let mut columns = zero_columns(RAW_PREPROCESSED_COLUMN_COUNT, size);
        for (index, row) in self.raw_rows.iter().copied().enumerate() {
            columns[RAW_ROW_MASK_COLUMN][index] = 1;
            columns[RAW_SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[RAW_BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[RAW_VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[RAW_QUERY_COLUMN][index] = row.query;
            columns[RAW_USE_COUNT_COLUMN][index] = row.use_count;
        }
        into_evaluations(columns, self.raw_log_size)
    }

    pub fn gen_mapping_columns(
        &self,
    ) -> ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>> {
        let size = 1_usize << self.mapping_log_size;
        let mut columns = zero_columns(MAPPING_PREPROCESSED_COLUMN_COUNT, size);
        for (index, row) in self.mapping_rows.iter().copied().enumerate() {
            columns[MAPPING_ROW_MASK_COLUMN][index] = 1;
            columns[MAPPING_SEGMENT_MASK_COLUMN][index] = row.segment_mask;
            columns[MAPPING_BINARY_MASK_COLUMN][index] = row.binary_mask;
            columns[MAPPING_VERIFIER_ID_COLUMN][index] = row.verifier_id;
            columns[MAPPING_KIND_COLUMN][index] = row.kind.as_u32();
            columns[MAPPING_ITEM_COLUMN][index] = row.item;
            columns[MAPPING_QUERY_COLUMN][index] = row.query;
            for bit in 0..M31_BITS {
                columns[POSITION_WEIGHT_START_COLUMN + bit][index] = row.position_weights[bit];
                columns[OFFSET_WEIGHT_START_COLUMN + bit][index] = row.offset_weights[bit];
            }
        }
        into_evaluations(columns, self.mapping_log_size)
    }
}

fn append_profile_rows<const N_TREES: usize, const N_FRI_LAYERS: usize>(
    raw_rows: &mut Vec<RawRow>,
    mapping_rows: &mut Vec<MappingRow>,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
    query_count: usize,
    lifting_log_size: u32,
    tree_heights: &[u32; N_TREES],
    fri_fold_widths: &[u32; N_FRI_LAYERS],
) -> Result<(), QueryPositionError> {
    let mapping_count = N_TREES
        .checked_add(
            N_FRI_LAYERS
                .checked_mul(2)
                .ok_or(QueryPositionError::RowCountOverflow)?,
        )
        .and_then(|count| count.checked_add(2))
        .ok_or(QueryPositionError::RowCountOverflow)?;
    let use_count = canonical_u32("query mapping use count", mapping_count)?;
    for query in 0..query_count {
        let query = canonical_u32("raw query index", query)?;
        raw_rows.push(RawRow {
            segment_mask,
            binary_mask,
            verifier_id,
            query,
            use_count,
        });

        for (tree, height) in tree_heights.iter().copied().enumerate() {
            let position_weights = if tree == 0 {
                preprocessed_tree_weights(lifting_log_size, height)?
            } else {
                shifted_weights(0, height)?
            };
            mapping_rows.push(MappingRow {
                segment_mask,
                binary_mask,
                verifier_id,
                kind: QueryPositionKind::TraceTree,
                item: canonical_u32("commitment tree", tree)?,
                query,
                position_weights,
                offset_weights: [0; M31_BITS],
            });
        }
        mapping_rows.push(MappingRow {
            segment_mask,
            binary_mask,
            verifier_id,
            kind: QueryPositionKind::Deep,
            item: 0,
            query,
            position_weights: shifted_weights(0, lifting_log_size)?,
            offset_weights: [0; M31_BITS],
        });

        let mut folded_bits = 0_u32;
        for (layer, width) in fri_fold_widths.iter().copied().enumerate() {
            if width < 2 || !width.is_power_of_two() {
                return Err(QueryPositionError::InvalidFriFoldWidth { layer, width });
            }
            let fold_step = width.ilog2();
            let remaining = lifting_log_size.checked_sub(folded_bits).ok_or(
                QueryPositionError::FriFoldExceedsDomain {
                    layer,
                    folded_bits,
                    fold_step,
                    lifting_log_size,
                },
            )?;
            if fold_step > remaining {
                return Err(QueryPositionError::FriFoldExceedsDomain {
                    layer,
                    folded_bits,
                    fold_step,
                    lifting_log_size,
                });
            }
            mapping_rows.push(MappingRow {
                segment_mask,
                binary_mask,
                verifier_id,
                kind: QueryPositionKind::FriFold,
                item: canonical_u32("FRI layer", layer)?,
                query,
                position_weights: shifted_weights(folded_bits, remaining)?,
                offset_weights: shifted_weights(folded_bits, fold_step)?,
            });
            folded_bits = folded_bits
                .checked_add(fold_step)
                .ok_or(QueryPositionError::BitShiftOverflow)?;
            mapping_rows.push(MappingRow {
                segment_mask,
                binary_mask,
                verifier_id,
                kind: QueryPositionKind::FriMerkle,
                item: canonical_u32("FRI layer", layer)?,
                query,
                position_weights: shifted_weights(folded_bits, lifting_log_size - folded_bits)?,
                offset_weights: [0; M31_BITS],
            });
        }
        mapping_rows.push(MappingRow {
            segment_mask,
            binary_mask,
            verifier_id,
            kind: QueryPositionKind::LastLayer,
            item: 0,
            query,
            position_weights: shifted_weights(folded_bits, lifting_log_size - folded_bits)?,
            offset_weights: [0; M31_BITS],
        });
    }
    Ok(())
}

fn shifted_weights(start: u32, count: u32) -> Result<[u32; M31_BITS], QueryPositionError> {
    let end = start
        .checked_add(count)
        .ok_or(QueryPositionError::BitShiftOverflow)?;
    if end > M31_BITS as u32 {
        return Err(QueryPositionError::BitRangeOutOfBounds { start, count });
    }
    let mut weights = [0_u32; M31_BITS];
    for source in start..end {
        weights[source as usize] = 1_u32
            .checked_shl(source - start)
            .ok_or(QueryPositionError::BitShiftOverflow)?;
    }
    Ok(weights)
}

fn preprocessed_tree_weights(
    lifting_log_size: u32,
    tree_height: u32,
) -> Result<[u32; M31_BITS], QueryPositionError> {
    if tree_height == 0 {
        return Ok([0; M31_BITS]);
    }
    let mut weights = [0_u32; M31_BITS];
    weights[0] = 1;
    if lifting_log_size < tree_height {
        for source in 1..lifting_log_size {
            let target = source + tree_height - lifting_log_size;
            weights[source as usize] = 1_u32
                .checked_shl(target)
                .ok_or(QueryPositionError::BitShiftOverflow)?;
        }
    } else {
        let source_start = lifting_log_size - tree_height + 1;
        for source in source_start..lifting_log_size {
            let target = source - lifting_log_size + tree_height;
            weights[source as usize] = 1_u32
                .checked_shl(target)
                .ok_or(QueryPositionError::BitShiftOverflow)?;
        }
    }
    Ok(weights)
}

fn apply_weights(word: M31Word, weights: &[u32; M31_BITS]) -> Result<u32, QueryPositionError> {
    weights
        .iter()
        .copied()
        .enumerate()
        .try_fold(0_u32, |value, (bit, weight)| {
            value
                .checked_add(((word.as_u32() >> bit) & 1) * weight)
                .ok_or(QueryPositionError::PositionOverflow)
        })
        .and_then(|value| {
            M31Word::try_from(value)
                .map(M31Word::as_u32)
                .map_err(|_| QueryPositionError::PositionNotCanonical { value })
        })
}

fn padded_log_size(field: &'static str, rows: usize) -> Result<u32, QueryPositionError> {
    let padded = rows
        .checked_next_power_of_two()
        .ok_or(QueryPositionError::RowCountOverflow)?
        .max(1 << MIN_LOG_SIZE);
    let log_size = padded.ilog2();
    if log_size > MAX_LOG_SIZE {
        Err(QueryPositionError::LogSizeOutOfRange { field, log_size })
    } else {
        Ok(log_size)
    }
}

fn canonical_u32(field: &'static str, value: usize) -> Result<u32, QueryPositionError> {
    let value =
        u32::try_from(value).map_err(|_| QueryPositionError::IndexOutOfRange { field, value })?;
    M31Word::try_from(value)
        .map(M31Word::as_u32)
        .map_err(|_| QueryPositionError::IndexNotCanonical { field, value })
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

pub type BitsComponent = FrameworkComponent<BitsEval>;
pub type MappingComponent = FrameworkComponent<MappingEval>;

/// Consumes raw transcript words and exports their canonical bit tuples.
#[derive(Clone)]
pub struct BitsEval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub randomness_relations: VerifierRandomnessRelations,
    pub query_relations: QueryPositionRelations,
}

impl FrameworkEval for BitsEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = QueryBitsColumns::from_eval(&mut eval);
        let ids = QueryPositionPreprocessed::raw_column_ids();
        let row_mask = eval.get_preprocessed_column(ids[RAW_ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[RAW_SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[RAW_BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[RAW_VERIFIER_ID_COLUMN].clone());
        let query = eval.get_preprocessed_column(ids[RAW_QUERY_COLUMN].clone());
        let use_count = eval.get_preprocessed_column(ids[RAW_USE_COUNT_COLUMN].clone());
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        let bits = query_bits(&cols);

        eval.add_constraint(cols.enabler.clone() - active.clone());
        eval.add_constraint((one.clone() - active.clone()) * cols.word.clone());
        eval.add_constraint((one.clone() - active.clone()) * cols.canonical_inverse.clone());
        let mut reconstructed = E::F::from(BaseField::from(0));
        let mut bit_sum = E::F::from(BaseField::from(0));
        for (bit, value) in bits.iter().enumerate() {
            eval.add_constraint(value.clone() * (one.clone() - value.clone()));
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
            reconstructed += value.clone()
                * E::F::from(BaseField::from(
                    1_u32
                        .checked_shl(bit as u32)
                        .expect("M31 bit weights fit u32"),
                ));
            bit_sum += value.clone();
        }
        eval.add_constraint(cols.word.clone() - reconstructed);
        let zero_count = active.clone() * E::F::from(BaseField::from(M31_BITS as u32)) - bit_sum;
        eval.add_constraint(zero_count * cols.canonical_inverse.clone() - active.clone());

        eval.add_to_relation(RelationEntry::new(
            &self.randomness_relations.word,
            -E::EF::from(active.clone()),
            &[
                verifier_id.clone(),
                E::F::from(BaseField::from(VerifierRandomnessKind::RawQuery.as_u32())),
                query.clone(),
                E::F::from(BaseField::from(0)),
                cols.word.clone(),
            ],
        ));
        let mut tuple = vec![verifier_id, query];
        tuple.extend(bits);
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.bits,
            E::EF::from(active * use_count),
            &tuple,
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Consumes canonical bits and emits one typed position per fixed obligation.
#[derive(Clone)]
pub struct MappingEval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub query_relations: QueryPositionRelations,
}

impl FrameworkEval for MappingEval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = QueryMappingColumns::from_eval(&mut eval);
        let ids = QueryPositionPreprocessed::mapping_column_ids();
        let row_mask = eval.get_preprocessed_column(ids[MAPPING_ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[MAPPING_SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[MAPPING_BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[MAPPING_VERIFIER_ID_COLUMN].clone());
        let kind = eval.get_preprocessed_column(ids[MAPPING_KIND_COLUMN].clone());
        let item = eval.get_preprocessed_column(ids[MAPPING_ITEM_COLUMN].clone());
        let query = eval.get_preprocessed_column(ids[MAPPING_QUERY_COLUMN].clone());
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        let bits = mapping_bits(&cols);
        let position_weights = core::array::from_fn::<_, M31_BITS, _>(|bit| {
            eval.get_preprocessed_column(ids[POSITION_WEIGHT_START_COLUMN + bit].clone())
        });
        let offset_weights = core::array::from_fn::<_, M31_BITS, _>(|bit| {
            eval.get_preprocessed_column(ids[OFFSET_WEIGHT_START_COLUMN + bit].clone())
        });

        eval.add_constraint(cols.enabler.clone() - active.clone());
        eval.add_constraint((one.clone() - active.clone()) * cols.position.clone());
        eval.add_constraint((one.clone() - active.clone()) * cols.offset.clone());
        let mut position = E::F::from(BaseField::from(0));
        let mut offset = E::F::from(BaseField::from(0));
        for (bit, value) in bits.iter().enumerate() {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
            position += value.clone() * position_weights[bit].clone();
            offset += value.clone() * offset_weights[bit].clone();
        }
        eval.add_constraint(cols.position.clone() - position);
        eval.add_constraint(cols.offset.clone() - offset);

        let mut bits_tuple = vec![verifier_id.clone(), query.clone()];
        bits_tuple.extend(bits);
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.bits,
            -E::EF::from(active.clone()),
            &bits_tuple,
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.query_relations.position,
            E::EF::from(active),
            &[
                verifier_id,
                kind,
                item,
                query,
                cols.position.clone(),
                cols.offset.clone(),
            ],
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn query_bits<F: Clone>(cols: &QueryBitsColumns<F>) -> [F; M31_BITS] {
    [
        cols.bit_0.clone(),
        cols.bit_1.clone(),
        cols.bit_2.clone(),
        cols.bit_3.clone(),
        cols.bit_4.clone(),
        cols.bit_5.clone(),
        cols.bit_6.clone(),
        cols.bit_7.clone(),
        cols.bit_8.clone(),
        cols.bit_9.clone(),
        cols.bit_10.clone(),
        cols.bit_11.clone(),
        cols.bit_12.clone(),
        cols.bit_13.clone(),
        cols.bit_14.clone(),
        cols.bit_15.clone(),
        cols.bit_16.clone(),
        cols.bit_17.clone(),
        cols.bit_18.clone(),
        cols.bit_19.clone(),
        cols.bit_20.clone(),
        cols.bit_21.clone(),
        cols.bit_22.clone(),
        cols.bit_23.clone(),
        cols.bit_24.clone(),
        cols.bit_25.clone(),
        cols.bit_26.clone(),
        cols.bit_27.clone(),
        cols.bit_28.clone(),
        cols.bit_29.clone(),
        cols.bit_30.clone(),
    ]
}

fn mapping_bits<F: Clone>(cols: &QueryMappingColumns<F>) -> [F; M31_BITS] {
    [
        cols.bit_0.clone(),
        cols.bit_1.clone(),
        cols.bit_2.clone(),
        cols.bit_3.clone(),
        cols.bit_4.clone(),
        cols.bit_5.clone(),
        cols.bit_6.clone(),
        cols.bit_7.clone(),
        cols.bit_8.clone(),
        cols.bit_9.clone(),
        cols.bit_10.clone(),
        cols.bit_11.clone(),
        cols.bit_12.clone(),
        cols.bit_13.clone(),
        cols.bit_14.clone(),
        cols.bit_15.clone(),
        cols.bit_16.clone(),
        cols.bit_17.clone(),
        cols.bit_18.clone(),
        cols.bit_19.clone(),
        cols.bit_20.clone(),
        cols.bit_21.clone(),
        cols.bit_22.clone(),
        cols.bit_23.clone(),
        cols.bit_24.clone(),
        cols.bit_25.clone(),
        cols.bit_26.clone(),
        cols.bit_27.clone(),
        cols.bit_28.clone(),
        cols.bit_29.clone(),
        cols.bit_30.clone(),
    ]
}

/// Raw query words selected by the public universal proof kind.
#[derive(Clone, Copy)]
pub enum UniversalRawQueryWitness<'a> {
    Segment(&'a [M31Word]),
    Binary {
        left: &'a [M31Word],
        right: &'a [M31Word],
    },
    Empty,
}

/// Materializes canonical bits and every fixed semantic query mapping.
pub fn push_query_positions(
    bits_table: &mut QueryBitsTable,
    mapping_table: &mut QueryMappingTable,
    preprocessed: &QueryPositionPreprocessed,
    witness: UniversalRawQueryWitness<'_>,
) -> Result<(), QueryPositionError> {
    validate_witness_counts(preprocessed, witness)?;
    for row in &preprocessed.raw_rows {
        let word = query_word(witness, row.verifier_id, row.query)?;
        if let Some(word) = word {
            let raw = word.as_u32();
            let bits = core::array::from_fn(|bit| (raw >> bit) & 1);
            let zero_count = M31_BITS as u32 - raw.count_ones();
            let inverse = BaseField::from(zero_count).inverse().0;
            push_bits_row(bits_table, true, raw, inverse, bits);
        } else {
            push_bits_row(bits_table, false, 0, 0, [0; M31_BITS]);
        }
    }
    for row in &preprocessed.mapping_rows {
        let word = query_word(witness, row.verifier_id, row.query)?;
        if let Some(word) = word {
            let raw = word.as_u32();
            let bits = core::array::from_fn(|bit| (raw >> bit) & 1);
            let (position, offset) = row.evaluate(word)?;
            push_mapping_row(mapping_table, true, position, offset, bits);
        } else {
            push_mapping_row(mapping_table, false, 0, 0, [0; M31_BITS]);
        }
    }
    Ok(())
}

fn validate_witness_counts(
    preprocessed: &QueryPositionPreprocessed,
    witness: UniversalRawQueryWitness<'_>,
) -> Result<(), QueryPositionError> {
    match witness {
        UniversalRawQueryWitness::Segment(queries) => validate_query_count(
            SEGMENT_VERIFIER_ID,
            preprocessed.vm_query_count,
            queries.len(),
        ),
        UniversalRawQueryWitness::Binary { left, right } => {
            validate_query_count(
                LEFT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_query_count,
                left.len(),
            )?;
            validate_query_count(
                RIGHT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_query_count,
                right.len(),
            )
        }
        UniversalRawQueryWitness::Empty => Ok(()),
    }
}

fn validate_query_count(
    verifier_id: u32,
    expected: usize,
    actual: usize,
) -> Result<(), QueryPositionError> {
    if expected == actual {
        Ok(())
    } else {
        Err(QueryPositionError::QueryCountMismatch {
            verifier_id,
            expected,
            actual,
        })
    }
}

fn query_word(
    witness: UniversalRawQueryWitness<'_>,
    verifier_id: u32,
    query: u32,
) -> Result<Option<M31Word>, QueryPositionError> {
    let queries = match (witness, verifier_id) {
        (UniversalRawQueryWitness::Segment(queries), SEGMENT_VERIFIER_ID) => Some(queries),
        (UniversalRawQueryWitness::Binary { left, .. }, LEFT_RECURSION_VERIFIER_ID) => Some(left),
        (UniversalRawQueryWitness::Binary { right, .. }, RIGHT_RECURSION_VERIFIER_ID) => {
            Some(right)
        }
        (UniversalRawQueryWitness::Empty, SEGMENT_VERIFIER_ID)
        | (UniversalRawQueryWitness::Empty, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalRawQueryWitness::Empty, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalRawQueryWitness::Segment(_), LEFT_RECURSION_VERIFIER_ID)
        | (UniversalRawQueryWitness::Segment(_), RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalRawQueryWitness::Binary { .. }, SEGMENT_VERIFIER_ID) => None,
        (_, verifier_id) => {
            return Err(QueryPositionError::UnknownVerifierId { verifier_id });
        }
    };
    queries
        .map(|queries| {
            queries
                .get(query as usize)
                .copied()
                .ok_or(QueryPositionError::QueryMissing { verifier_id, query })
        })
        .transpose()
}

fn push_bits_row(
    table: &mut QueryBitsTable,
    active: bool,
    word: u32,
    canonical_inverse: u32,
    bits: [u32; M31_BITS],
) {
    let mut row = Vec::with_capacity(1 + 2 + M31_BITS);
    row.extend([u32::from(active), word, canonical_inverse]);
    row.extend(bits);
    table.push_row(&row);
}

fn push_mapping_row(
    table: &mut QueryMappingTable,
    active: bool,
    position: u32,
    offset: u32,
    bits: [u32; M31_BITS],
) {
    let mut row = Vec::with_capacity(1 + 2 + M31_BITS);
    row.extend([u32::from(active), position, offset]);
    row.extend(bits);
    table.push_row(&row);
}

/// Generates the raw-word consumer and canonical-bit producer interaction trace.
pub fn gen_bits_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = QueryBitsColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let bits = query_bits(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[RAW_ROW_MASK_COLUMN][row]
                    * (pp[RAW_SEGMENT_MASK_COLUMN][row] * segment
                        + pp[RAW_BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let randomness_denominator = (0..size)
        .map(|row| {
            randomness_relations.word.combine(&[
                pp[RAW_VERIFIER_ID_COLUMN][row],
                PackedM31::broadcast(BaseField::from(VerifierRandomnessKind::RawQuery.as_u32())),
                pp[RAW_QUERY_COLUMN][row],
                PackedM31::broadcast(BaseField::from(0)),
                cols.word[row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let bits_numerator = (0..size)
        .map(|row| active[row] * pp[RAW_USE_COUNT_COLUMN][row])
        .collect::<Vec<_>>();
    let bits_denominator = (0..size)
        .map(|row| {
            let mut tuple = vec![pp[RAW_VERIFIER_ID_COLUMN][row], pp[RAW_QUERY_COLUMN][row]];
            tuple.extend(bits.iter().map(|column| column[row]));
            query_relations.bits.combine(&tuple)
        })
        .collect::<Vec<PackedQM31>>();
    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &randomness_denominator,
        &bits_numerator,
        &bits_denominator,
        logup
    );
    logup.finalize_last()
}

/// Generates canonical-bit consumers and typed-position producers.
pub fn gen_mapping_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    query_relations: &QueryPositionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = QueryMappingColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let bits = mapping_bits(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[MAPPING_ROW_MASK_COLUMN][row]
                    * (pp[MAPPING_SEGMENT_MASK_COLUMN][row] * segment
                        + pp[MAPPING_BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let bits_denominator = (0..size)
        .map(|row| {
            let mut tuple = vec![
                pp[MAPPING_VERIFIER_ID_COLUMN][row],
                pp[MAPPING_QUERY_COLUMN][row],
            ];
            tuple.extend(bits.iter().map(|column| column[row]));
            query_relations.bits.combine(&tuple)
        })
        .collect::<Vec<PackedQM31>>();
    let position_denominator = (0..size)
        .map(|row| {
            query_relations.position.combine(&[
                pp[MAPPING_VERIFIER_ID_COLUMN][row],
                pp[MAPPING_KIND_COLUMN][row],
                pp[MAPPING_ITEM_COLUMN][row],
                pp[MAPPING_QUERY_COLUMN][row],
                cols.position[row],
                cols.offset[row],
            ])
        })
        .collect::<Vec<PackedQM31>>();
    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &bits_denominator,
        &active,
        &position_denominator,
        logup
    );
    logup.finalize_last()
}

/// Invalid profile geometry, universal witness, or canonical position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryPositionError {
    VmShape(ProofShapeError),
    RecursionShape(ProofShapeError),
    RowCountOverflow,
    LogSizeOutOfRange {
        field: &'static str,
        log_size: u32,
    },
    IndexOutOfRange {
        field: &'static str,
        value: usize,
    },
    IndexNotCanonical {
        field: &'static str,
        value: u32,
    },
    InvalidFriFoldWidth {
        layer: usize,
        width: u32,
    },
    FriFoldExceedsDomain {
        layer: usize,
        folded_bits: u32,
        fold_step: u32,
        lifting_log_size: u32,
    },
    BitShiftOverflow,
    BitRangeOutOfBounds {
        start: u32,
        count: u32,
    },
    PositionOverflow,
    PositionNotCanonical {
        value: u32,
    },
    QueryCountMismatch {
        verifier_id: u32,
        expected: usize,
        actual: usize,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    QueryMissing {
        verifier_id: u32,
        query: u32,
    },
    RouteMissing {
        verifier_id: u32,
        kind: QueryPositionKind,
        item: u32,
        query: u32,
    },
}

impl fmt::Display for QueryPositionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for QueryPositionError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo::core::pcs::utils::prepare_preprocessed_query_positions;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;
    use crate::v2::protocol::{OptionalM31Word, PcsParameters};

    const TABLE_COUNT: usize = 1;
    const TREE_COUNT: usize = 4;
    const FRI_LAYER_COUNT: usize = 2;

    fn pcs() -> ValidatedPcsParameters {
        PcsParameters {
            interaction_pow_bits: M31Word::ZERO,
            pow_bits: M31Word::ZERO,
            fri_log_blowup_factor: M31Word::from(1_u16),
            fri_n_queries: M31Word::from(2_u16),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: M31Word::from(4_u16),
            lifting_log_size: OptionalM31Word::None,
        }
        .validate()
        .expect("fixture PCS parameters are valid")
    }

    fn shape() -> FixedProofShape<TABLE_COUNT, TREE_COUNT, FRI_LAYER_COUNT> {
        FixedProofShape {
            claimed_sum_count: M31Word::from(1_u16),
            sampled_value_count: M31Word::from(1_u16),
            queried_value_count: M31Word::from(2_u16),
            trace_path_count: M31Word::from(8_u16),
            raw_query_count: M31Word::from(2_u16),
            last_layer_coefficient_count: M31Word::from(1_u16),
            table_log_sizes: [M31Word::from(7_u16)],
            tree_heights: [6_u16, 8, 8, 8].map(M31Word::from),
            fri_layer_fold_widths: [16_u16, 8].map(M31Word::from),
            fri_layer_tree_heights: [6_u16, 2].map(M31Word::from),
        }
    }

    fn preprocessing() -> QueryPositionPreprocessed {
        QueryPositionPreprocessed::new(pcs(), &shape(), pcs(), &shape())
            .expect("fixture query geometry is valid")
    }

    fn queries() -> ([M31Word; 2], [M31Word; 2], [M31Word; 2]) {
        (
            [M31Word::from(183_u16), M31Word::from(42_u16)],
            [M31Word::from(77_u16), M31Word::from(88_u16)],
            [M31Word::from(99_u16), M31Word::from(100_u16)],
        )
    }

    fn materialize(
        kind: ProofKind,
    ) -> (QueryPositionPreprocessed, QueryBitsTable, QueryMappingTable) {
        let preprocessing = preprocessing();
        let mut bits = QueryBitsTable::new();
        let mut mappings = QueryMappingTable::new();
        let (vm, left, right) = queries();
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalRawQueryWitness::Segment(&vm),
            ProofKind::BinaryNode => UniversalRawQueryWitness::Binary {
                left: &left,
                right: &right,
            },
            ProofKind::EmptyLeaf => UniversalRawQueryWitness::Empty,
        };
        push_query_positions(&mut bits, &mut mappings, &preprocessing, witness)
            .expect("fixture raw queries materialize");
        (preprocessing, bits, mappings)
    }

    fn assert_bits_constraints(
        kind: ProofKind,
        preprocessing: &QueryPositionPreprocessed,
        table: QueryBitsTable,
    ) {
        let randomness_relations = VerifierRandomnessRelations::dummy();
        let query_relations = QueryPositionRelations::dummy();
        let preprocessed = preprocessing.gen_raw_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_bits_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &randomness_relations,
            &query_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = BitsEval {
            log_size: preprocessing.raw_log_size(),
            proof_kind: kind,
            randomness_relations,
            query_relations,
        };
        assert_constraints_on_polys(
            &polys,
            CanonicCoset::new(preprocessing.raw_log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn assert_mapping_constraints(
        kind: ProofKind,
        preprocessing: &QueryPositionPreprocessed,
        table: QueryMappingTable,
    ) {
        let query_relations = QueryPositionRelations::dummy();
        let preprocessed = preprocessing.gen_mapping_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) =
            gen_mapping_interaction_trace(&trace, &preprocessed, kind, &query_relations);
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = MappingEval {
            log_size: preprocessing.mapping_log_size(),
            proof_kind: kind,
            query_relations,
        };
        assert_constraints_on_polys(
            &polys,
            CanonicCoset::new(preprocessing.mapping_log_size()),
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
    fn every_universal_mode_satisfies_query_bit_constraints(#[case] kind: ProofKind) {
        let (preprocessing, bits, _) = materialize(kind);
        assert_bits_constraints(kind, &preprocessing, bits);
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_query_mapping_constraints(#[case] kind: ProofKind) {
        let (preprocessing, _, mappings) = materialize(kind);
        assert_mapping_constraints(kind, &preprocessing, mappings);
    }

    #[rstest]
    #[case::preprocessed_larger(6, 8, 183)]
    #[case::equal_domains(8, 8, 439)]
    #[case::preprocessed_smaller(8, 6, 439)]
    fn preprocessed_tree_mapping_matches_stwo(
        #[case] lifting_log_size: u32,
        #[case] tree_height: u32,
        #[case] raw_word: u32,
    ) {
        let word = M31Word::try_from(raw_word).expect("fixture word is canonical");
        let weights = preprocessed_tree_weights(lifting_log_size, tree_height)
            .expect("fixture query geometry is valid");
        let position = raw_word & ((1_u32 << lifting_log_size) - 1);
        let expected = prepare_preprocessed_query_positions(
            &[position as usize],
            lifting_log_size,
            tree_height,
        )[0] as u32;
        assert_eq!(apply_weights(word, &weights), Ok(expected));
    }

    #[test]
    fn query_routes_match_stwo_preprocessing_and_fri_shifts() {
        let preprocessing = preprocessing();
        let word = M31Word::from(183_u16);
        let actual = preprocessing
            .mapping_rows
            .iter()
            .filter(|row| row.verifier_id == SEGMENT_VERIFIER_ID && row.query == 0)
            .map(|row| {
                let (position, offset) = row.evaluate(word).unwrap();
                (row.kind, row.item, position, offset)
            })
            .collect::<Vec<_>>();
        let preprocessed = prepare_preprocessed_query_positions(&[183], 8, 6)[0] as u32;
        assert_eq!(
            actual,
            vec![
                (QueryPositionKind::TraceTree, 0, preprocessed, 0),
                (QueryPositionKind::TraceTree, 1, 183, 0),
                (QueryPositionKind::TraceTree, 2, 183, 0),
                (QueryPositionKind::TraceTree, 3, 183, 0),
                (QueryPositionKind::Deep, 0, 183, 0),
                (QueryPositionKind::FriFold, 0, 183, 7),
                (QueryPositionKind::FriMerkle, 0, 11, 0),
                (QueryPositionKind::FriFold, 1, 11, 3),
                (QueryPositionKind::FriMerkle, 1, 1, 0),
                (QueryPositionKind::LastLayer, 0, 1, 0),
            ]
        );
    }

    #[test]
    #[should_panic]
    fn m31_zero_cannot_use_the_all_ones_bit_alias() {
        let (preprocessing, mut bits, _) = materialize(ProofKind::SegmentLeaf);
        bits.word[0] = 0;
        bits.canonical_inverse[0] = 0;
        bits.bit_0[0] = 1;
        bits.bit_1[0] = 1;
        bits.bit_2[0] = 1;
        bits.bit_3[0] = 1;
        bits.bit_4[0] = 1;
        bits.bit_5[0] = 1;
        bits.bit_6[0] = 1;
        bits.bit_7[0] = 1;
        bits.bit_8[0] = 1;
        bits.bit_9[0] = 1;
        bits.bit_10[0] = 1;
        bits.bit_11[0] = 1;
        bits.bit_12[0] = 1;
        bits.bit_13[0] = 1;
        bits.bit_14[0] = 1;
        bits.bit_15[0] = 1;
        bits.bit_16[0] = 1;
        bits.bit_17[0] = 1;
        bits.bit_18[0] = 1;
        bits.bit_19[0] = 1;
        bits.bit_20[0] = 1;
        bits.bit_21[0] = 1;
        bits.bit_22[0] = 1;
        bits.bit_23[0] = 1;
        bits.bit_24[0] = 1;
        bits.bit_25[0] = 1;
        bits.bit_26[0] = 1;
        bits.bit_27[0] = 1;
        bits.bit_28[0] = 1;
        bits.bit_29[0] = 1;
        bits.bit_30[0] = 1;
        assert_bits_constraints(ProofKind::SegmentLeaf, &preprocessing, bits);
    }

    #[test]
    fn raw_draws_bits_and_typed_positions_close_exactly() {
        let preprocessing = preprocessing();
        let (vm, _, _) = queries();
        let mut bits = QueryBitsTable::new();
        let mut mappings = QueryMappingTable::new();
        push_query_positions(
            &mut bits,
            &mut mappings,
            &preprocessing,
            UniversalRawQueryWitness::Segment(&vm),
        )
        .expect("fixture raw queries materialize");
        let mut channel = Poseidon2M31Channel::default();
        let randomness_relations = VerifierRandomnessRelations::draw(&mut channel);
        let query_relations = QueryPositionRelations::draw(&mut channel);
        let (_, bits_sum) = gen_bits_interaction_trace(
            &bits.into_witness(),
            &preprocessing.gen_raw_columns(),
            ProofKind::SegmentLeaf,
            &randomness_relations,
            &query_relations,
        );
        let (_, mappings_sum) = gen_mapping_interaction_trace(
            &mappings.into_witness(),
            &preprocessing.gen_mapping_columns(),
            ProofKind::SegmentLeaf,
            &query_relations,
        );
        let raw_sources = preprocessing
            .raw_rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let word = vm[row.query as usize];
                let denominator: QM31 = randomness_relations.word.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(VerifierRandomnessKind::RawQuery.as_u32()),
                    M31::from(row.query),
                    M31::from(0),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            });
        let position_consumers = preprocessing
            .mapping_rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let word = vm[row.query as usize];
                let (position, offset) = row.evaluate(word).unwrap();
                let denominator: QM31 = query_relations.position.combine(&[
                    M31::from(row.verifier_id),
                    M31::from(row.kind.as_u32()),
                    M31::from(row.item),
                    M31::from(row.query),
                    M31::from(position),
                    M31::from(offset),
                ]);
                sum - denominator.inverse()
            });
        assert!((bits_sum + mappings_sum + raw_sources + position_consumers).is_zero());
    }
}
