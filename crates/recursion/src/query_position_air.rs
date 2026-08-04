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
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::relation;

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

// Canonical query bits: verifier, raw-query index, and all 31 bits.
relation!(QueryBitsRelation, 33);
// Individually typed canonical bits consumed by arithmetic verifier circuits.
relation!(QueryBitValueRelation, 4);
// Routed position: verifier, purpose, item, raw query, position, and fold offset.
relation!(QueryPositionRelation, 6);

/// Relations connecting transcript draws to every PCS query consumer.
#[derive(Clone)]
pub struct QueryPositionRelations {
    pub bits: QueryBitsRelation,
    pub bit_value: QueryBitValueRelation,
    pub position: QueryPositionRelation,
}

impl QueryPositionRelations {
    pub fn dummy() -> Self {
        Self {
            bits: QueryBitsRelation::dummy(),
            bit_value: QueryBitValueRelation::dummy(),
            position: QueryPositionRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl stwo::core::channel::Channel) -> Self {
        Self {
            bits: QueryBitsRelation::draw(channel),
            bit_value: QueryBitValueRelation::draw(channel),
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
        query_bits_dsl::preprocessed_column_ids()
    }

    pub fn mapping_column_ids() -> Vec<PreProcessedColumnId> {
        query_mapping_dsl::preprocessed_column_ids()
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

/// Relations used by the macro-generated raw-query decomposition component.
#[derive(Clone)]
pub struct QueryBitsComponentRelations {
    pub randomness_word: super::verifier_randomness_air::VerifierRandomnessWordRelation,
    pub bits: QueryBitsRelation,
    pub bit_value: QueryBitValueRelation,
}

impl QueryBitsComponentRelations {
    /// Combine the typed transcript source with both canonical-bit relations.
    pub fn new(
        randomness_relations: &VerifierRandomnessRelations,
        query_relations: &QueryPositionRelations,
    ) -> Self {
        Self {
            randomness_word: randomness_relations.word.clone(),
            bits: query_relations.bits.clone(),
            bit_value: query_relations.bit_value.clone(),
        }
    }
}

mod query_bits_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_enabler_boolean: false,
        embedded_relations: crate::query_position_air::QueryBitsComponentRelations,
        logup_batch: 2,
        embedded_preprocessed: {
            row_mask: "recursion_query_raw_row_mask",
            segment_mask: "recursion_query_raw_segment_mask",
            binary_mask: "recursion_query_raw_binary_mask",
            verifier_id: "recursion_query_raw_verifier_id",
            query: "recursion_query_raw_query",
            use_count: "recursion_query_raw_use_count",
        },
        embedded_params: [segment_active, binary_active, raw_query_kind],

        relation randomness_word(5);
        relation bits(33);
        relation bit_value(4);

        fn query_bits(
            word, canonical_inverse,
            bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7, bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15, bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23, bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30,
            row_mask, segment_mask, binary_mask, verifier_id, query, use_count,
            segment_active, binary_active, raw_query_kind,
        ) {
            // Trusted lane masks are disjoint subsets of the row mask.
            let active = segment_mask * segment_active + binary_mask * binary_active;

            constrain enabler - active;
            constrain (1 - active) * word;
            constrain (1 - active) * canonical_inverse;
            constrain bit_0 * (1 - bit_0);
            constrain (1 - active) * bit_0;
            constrain bit_1 * (1 - bit_1);
            constrain (1 - active) * bit_1;
            constrain bit_2 * (1 - bit_2);
            constrain (1 - active) * bit_2;
            constrain bit_3 * (1 - bit_3);
            constrain (1 - active) * bit_3;
            constrain bit_4 * (1 - bit_4);
            constrain (1 - active) * bit_4;
            constrain bit_5 * (1 - bit_5);
            constrain (1 - active) * bit_5;
            constrain bit_6 * (1 - bit_6);
            constrain (1 - active) * bit_6;
            constrain bit_7 * (1 - bit_7);
            constrain (1 - active) * bit_7;
            constrain bit_8 * (1 - bit_8);
            constrain (1 - active) * bit_8;
            constrain bit_9 * (1 - bit_9);
            constrain (1 - active) * bit_9;
            constrain bit_10 * (1 - bit_10);
            constrain (1 - active) * bit_10;
            constrain bit_11 * (1 - bit_11);
            constrain (1 - active) * bit_11;
            constrain bit_12 * (1 - bit_12);
            constrain (1 - active) * bit_12;
            constrain bit_13 * (1 - bit_13);
            constrain (1 - active) * bit_13;
            constrain bit_14 * (1 - bit_14);
            constrain (1 - active) * bit_14;
            constrain bit_15 * (1 - bit_15);
            constrain (1 - active) * bit_15;
            constrain bit_16 * (1 - bit_16);
            constrain (1 - active) * bit_16;
            constrain bit_17 * (1 - bit_17);
            constrain (1 - active) * bit_17;
            constrain bit_18 * (1 - bit_18);
            constrain (1 - active) * bit_18;
            constrain bit_19 * (1 - bit_19);
            constrain (1 - active) * bit_19;
            constrain bit_20 * (1 - bit_20);
            constrain (1 - active) * bit_20;
            constrain bit_21 * (1 - bit_21);
            constrain (1 - active) * bit_21;
            constrain bit_22 * (1 - bit_22);
            constrain (1 - active) * bit_22;
            constrain bit_23 * (1 - bit_23);
            constrain (1 - active) * bit_23;
            constrain bit_24 * (1 - bit_24);
            constrain (1 - active) * bit_24;
            constrain bit_25 * (1 - bit_25);
            constrain (1 - active) * bit_25;
            constrain bit_26 * (1 - bit_26);
            constrain (1 - active) * bit_26;
            constrain bit_27 * (1 - bit_27);
            constrain (1 - active) * bit_27;
            constrain bit_28 * (1 - bit_28);
            constrain (1 - active) * bit_28;
            constrain bit_29 * (1 - bit_29);
            constrain (1 - active) * bit_29;
            constrain bit_30 * (1 - bit_30);
            constrain (1 - active) * bit_30;
            constrain word - (1 * bit_0 + 2 * bit_1 + 4 * bit_2 + 8 * bit_3 + 16 * bit_4 + 32 * bit_5 + 64 * bit_6 + 128 * bit_7 + 256 * bit_8 + 512 * bit_9 + 1024 * bit_10 + 2048 * bit_11 + 4096 * bit_12 + 8192 * bit_13 + 16384 * bit_14 + 32768 * bit_15 + 65536 * bit_16 + 131072 * bit_17 + 262144 * bit_18 + 524288 * bit_19 + 1048576 * bit_20 + 2097152 * bit_21 + 4194304 * bit_22 + 8388608 * bit_23 + 16777216 * bit_24 + 33554432 * bit_25 + 67108864 * bit_26 + 134217728 * bit_27 + 268435456 * bit_28 + 536870912 * bit_29 + 1073741824 * bit_30);
            constrain (active * 31 - (bit_0 + bit_1 + bit_2 + bit_3 + bit_4 + bit_5 + bit_6 + bit_7 + bit_8 + bit_9 + bit_10 + bit_11 + bit_12 + bit_13 + bit_14 + bit_15 + bit_16 + bit_17 + bit_18 + bit_19 + bit_20 + bit_21 + bit_22 + bit_23 + bit_24 + bit_25 + bit_26 + bit_27 + bit_28 + bit_29 + bit_30)) * canonical_inverse - active;

            consume(active) randomness_word(verifier_id, raw_query_kind, query, 0, word);
            emit(active * use_count) bits(verifier_id, query, bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7, bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15, bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23, bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30);
        emit(active) bit_value(verifier_id, query, 0, bit_0);
        emit(active) bit_value(verifier_id, query, 1, bit_1);
        emit(active) bit_value(verifier_id, query, 2, bit_2);
        emit(active) bit_value(verifier_id, query, 3, bit_3);
        emit(active) bit_value(verifier_id, query, 4, bit_4);
        emit(active) bit_value(verifier_id, query, 5, bit_5);
        emit(active) bit_value(verifier_id, query, 6, bit_6);
        emit(active) bit_value(verifier_id, query, 7, bit_7);
        emit(active) bit_value(verifier_id, query, 8, bit_8);
        emit(active) bit_value(verifier_id, query, 9, bit_9);
        emit(active) bit_value(verifier_id, query, 10, bit_10);
        emit(active) bit_value(verifier_id, query, 11, bit_11);
        emit(active) bit_value(verifier_id, query, 12, bit_12);
        emit(active) bit_value(verifier_id, query, 13, bit_13);
        emit(active) bit_value(verifier_id, query, 14, bit_14);
        emit(active) bit_value(verifier_id, query, 15, bit_15);
        emit(active) bit_value(verifier_id, query, 16, bit_16);
        emit(active) bit_value(verifier_id, query, 17, bit_17);
        emit(active) bit_value(verifier_id, query, 18, bit_18);
        emit(active) bit_value(verifier_id, query, 19, bit_19);
        emit(active) bit_value(verifier_id, query, 20, bit_20);
        emit(active) bit_value(verifier_id, query, 21, bit_21);
        emit(active) bit_value(verifier_id, query, 22, bit_22);
        emit(active) bit_value(verifier_id, query, 23, bit_23);
        emit(active) bit_value(verifier_id, query, 24, bit_24);
        emit(active) bit_value(verifier_id, query, 25, bit_25);
        emit(active) bit_value(verifier_id, query, 26, bit_26);
        emit(active) bit_value(verifier_id, query, 27, bit_27);
        emit(active) bit_value(verifier_id, query, 28, bit_28);
        emit(active) bit_value(verifier_id, query, 29, bit_29);
        emit(active) bit_value(verifier_id, query, 30, bit_30);

            return word;
        }
    }
}

mod query_mapping_dsl {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_enabler_boolean: false,
        embedded_relations: crate::query_position_air::QueryPositionRelations,
        logup_batch: 2,
        embedded_preprocessed: {
        row_mask: "recursion_query_mapping_row_mask",
        segment_mask: "recursion_query_mapping_segment_mask",
        binary_mask: "recursion_query_mapping_binary_mask",
        verifier_id: "recursion_query_mapping_verifier_id",
        kind: "recursion_query_mapping_kind",
        item: "recursion_query_mapping_item",
        query: "recursion_query_mapping_query",
        position_weight_0: "recursion_query_mapping_position_weight_0",
        position_weight_1: "recursion_query_mapping_position_weight_1",
        position_weight_2: "recursion_query_mapping_position_weight_2",
        position_weight_3: "recursion_query_mapping_position_weight_3",
        position_weight_4: "recursion_query_mapping_position_weight_4",
        position_weight_5: "recursion_query_mapping_position_weight_5",
        position_weight_6: "recursion_query_mapping_position_weight_6",
        position_weight_7: "recursion_query_mapping_position_weight_7",
        position_weight_8: "recursion_query_mapping_position_weight_8",
        position_weight_9: "recursion_query_mapping_position_weight_9",
        position_weight_10: "recursion_query_mapping_position_weight_10",
        position_weight_11: "recursion_query_mapping_position_weight_11",
        position_weight_12: "recursion_query_mapping_position_weight_12",
        position_weight_13: "recursion_query_mapping_position_weight_13",
        position_weight_14: "recursion_query_mapping_position_weight_14",
        position_weight_15: "recursion_query_mapping_position_weight_15",
        position_weight_16: "recursion_query_mapping_position_weight_16",
        position_weight_17: "recursion_query_mapping_position_weight_17",
        position_weight_18: "recursion_query_mapping_position_weight_18",
        position_weight_19: "recursion_query_mapping_position_weight_19",
        position_weight_20: "recursion_query_mapping_position_weight_20",
        position_weight_21: "recursion_query_mapping_position_weight_21",
        position_weight_22: "recursion_query_mapping_position_weight_22",
        position_weight_23: "recursion_query_mapping_position_weight_23",
        position_weight_24: "recursion_query_mapping_position_weight_24",
        position_weight_25: "recursion_query_mapping_position_weight_25",
        position_weight_26: "recursion_query_mapping_position_weight_26",
        position_weight_27: "recursion_query_mapping_position_weight_27",
        position_weight_28: "recursion_query_mapping_position_weight_28",
        position_weight_29: "recursion_query_mapping_position_weight_29",
        position_weight_30: "recursion_query_mapping_position_weight_30",
        offset_weight_0: "recursion_query_mapping_offset_weight_0",
        offset_weight_1: "recursion_query_mapping_offset_weight_1",
        offset_weight_2: "recursion_query_mapping_offset_weight_2",
        offset_weight_3: "recursion_query_mapping_offset_weight_3",
        offset_weight_4: "recursion_query_mapping_offset_weight_4",
        offset_weight_5: "recursion_query_mapping_offset_weight_5",
        offset_weight_6: "recursion_query_mapping_offset_weight_6",
        offset_weight_7: "recursion_query_mapping_offset_weight_7",
        offset_weight_8: "recursion_query_mapping_offset_weight_8",
        offset_weight_9: "recursion_query_mapping_offset_weight_9",
        offset_weight_10: "recursion_query_mapping_offset_weight_10",
        offset_weight_11: "recursion_query_mapping_offset_weight_11",
        offset_weight_12: "recursion_query_mapping_offset_weight_12",
        offset_weight_13: "recursion_query_mapping_offset_weight_13",
        offset_weight_14: "recursion_query_mapping_offset_weight_14",
        offset_weight_15: "recursion_query_mapping_offset_weight_15",
        offset_weight_16: "recursion_query_mapping_offset_weight_16",
        offset_weight_17: "recursion_query_mapping_offset_weight_17",
        offset_weight_18: "recursion_query_mapping_offset_weight_18",
        offset_weight_19: "recursion_query_mapping_offset_weight_19",
        offset_weight_20: "recursion_query_mapping_offset_weight_20",
        offset_weight_21: "recursion_query_mapping_offset_weight_21",
        offset_weight_22: "recursion_query_mapping_offset_weight_22",
        offset_weight_23: "recursion_query_mapping_offset_weight_23",
        offset_weight_24: "recursion_query_mapping_offset_weight_24",
        offset_weight_25: "recursion_query_mapping_offset_weight_25",
        offset_weight_26: "recursion_query_mapping_offset_weight_26",
        offset_weight_27: "recursion_query_mapping_offset_weight_27",
        offset_weight_28: "recursion_query_mapping_offset_weight_28",
        offset_weight_29: "recursion_query_mapping_offset_weight_29",
        offset_weight_30: "recursion_query_mapping_offset_weight_30",
        },
        embedded_params: [segment_active, binary_active],

        relation bits(33);
        relation position(6);

        fn query_mapping(
            position, offset,
            bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7, bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15, bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23, bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30,
            row_mask, segment_mask, binary_mask, verifier_id, kind, item, query,
            position_weight_0, position_weight_1, position_weight_2, position_weight_3, position_weight_4, position_weight_5, position_weight_6, position_weight_7, position_weight_8, position_weight_9, position_weight_10, position_weight_11, position_weight_12, position_weight_13, position_weight_14, position_weight_15, position_weight_16, position_weight_17, position_weight_18, position_weight_19, position_weight_20, position_weight_21, position_weight_22, position_weight_23, position_weight_24, position_weight_25, position_weight_26, position_weight_27, position_weight_28, position_weight_29, position_weight_30,
            offset_weight_0, offset_weight_1, offset_weight_2, offset_weight_3, offset_weight_4, offset_weight_5, offset_weight_6, offset_weight_7, offset_weight_8, offset_weight_9, offset_weight_10, offset_weight_11, offset_weight_12, offset_weight_13, offset_weight_14, offset_weight_15, offset_weight_16, offset_weight_17, offset_weight_18, offset_weight_19, offset_weight_20, offset_weight_21, offset_weight_22, offset_weight_23, offset_weight_24, offset_weight_25, offset_weight_26, offset_weight_27, offset_weight_28, offset_weight_29, offset_weight_30,
            segment_active, binary_active,
        ) {
            // Trusted lane masks are disjoint subsets of the row mask.
            let active = segment_mask * segment_active + binary_mask * binary_active;

            constrain enabler - active;
            constrain (1 - active) * position;
            constrain (1 - active) * offset;
        constrain (1 - active) * bit_0;
        constrain (1 - active) * bit_1;
        constrain (1 - active) * bit_2;
        constrain (1 - active) * bit_3;
        constrain (1 - active) * bit_4;
        constrain (1 - active) * bit_5;
        constrain (1 - active) * bit_6;
        constrain (1 - active) * bit_7;
        constrain (1 - active) * bit_8;
        constrain (1 - active) * bit_9;
        constrain (1 - active) * bit_10;
        constrain (1 - active) * bit_11;
        constrain (1 - active) * bit_12;
        constrain (1 - active) * bit_13;
        constrain (1 - active) * bit_14;
        constrain (1 - active) * bit_15;
        constrain (1 - active) * bit_16;
        constrain (1 - active) * bit_17;
        constrain (1 - active) * bit_18;
        constrain (1 - active) * bit_19;
        constrain (1 - active) * bit_20;
        constrain (1 - active) * bit_21;
        constrain (1 - active) * bit_22;
        constrain (1 - active) * bit_23;
        constrain (1 - active) * bit_24;
        constrain (1 - active) * bit_25;
        constrain (1 - active) * bit_26;
        constrain (1 - active) * bit_27;
        constrain (1 - active) * bit_28;
        constrain (1 - active) * bit_29;
        constrain (1 - active) * bit_30;
            constrain position - (bit_0 * position_weight_0 + bit_1 * position_weight_1 + bit_2 * position_weight_2 + bit_3 * position_weight_3 + bit_4 * position_weight_4 + bit_5 * position_weight_5 + bit_6 * position_weight_6 + bit_7 * position_weight_7 + bit_8 * position_weight_8 + bit_9 * position_weight_9 + bit_10 * position_weight_10 + bit_11 * position_weight_11 + bit_12 * position_weight_12 + bit_13 * position_weight_13 + bit_14 * position_weight_14 + bit_15 * position_weight_15 + bit_16 * position_weight_16 + bit_17 * position_weight_17 + bit_18 * position_weight_18 + bit_19 * position_weight_19 + bit_20 * position_weight_20 + bit_21 * position_weight_21 + bit_22 * position_weight_22 + bit_23 * position_weight_23 + bit_24 * position_weight_24 + bit_25 * position_weight_25 + bit_26 * position_weight_26 + bit_27 * position_weight_27 + bit_28 * position_weight_28 + bit_29 * position_weight_29 + bit_30 * position_weight_30);
            constrain offset - (bit_0 * offset_weight_0 + bit_1 * offset_weight_1 + bit_2 * offset_weight_2 + bit_3 * offset_weight_3 + bit_4 * offset_weight_4 + bit_5 * offset_weight_5 + bit_6 * offset_weight_6 + bit_7 * offset_weight_7 + bit_8 * offset_weight_8 + bit_9 * offset_weight_9 + bit_10 * offset_weight_10 + bit_11 * offset_weight_11 + bit_12 * offset_weight_12 + bit_13 * offset_weight_13 + bit_14 * offset_weight_14 + bit_15 * offset_weight_15 + bit_16 * offset_weight_16 + bit_17 * offset_weight_17 + bit_18 * offset_weight_18 + bit_19 * offset_weight_19 + bit_20 * offset_weight_20 + bit_21 * offset_weight_21 + bit_22 * offset_weight_22 + bit_23 * offset_weight_23 + bit_24 * offset_weight_24 + bit_25 * offset_weight_25 + bit_26 * offset_weight_26 + bit_27 * offset_weight_27 + bit_28 * offset_weight_28 + bit_29 * offset_weight_29 + bit_30 * offset_weight_30);

            consume(active) bits(verifier_id, query, bit_0, bit_1, bit_2, bit_3, bit_4, bit_5, bit_6, bit_7, bit_8, bit_9, bit_10, bit_11, bit_12, bit_13, bit_14, bit_15, bit_16, bit_17, bit_18, bit_19, bit_20, bit_21, bit_22, bit_23, bit_24, bit_25, bit_26, bit_27, bit_28, bit_29, bit_30);
            emit(active) position(verifier_id, kind, item, query, position, offset);

            return (position, offset);
        }
    }
}

pub use query_bits_dsl::QueryBitsTable;
pub use query_bits_dsl::component::air::{Component as BitsComponent, Eval as BitsEval};
pub use query_mapping_dsl::QueryMappingTable;
pub use query_mapping_dsl::component::air::{Component as MappingComponent, Eval as MappingEval};

/// Construct the raw-query evaluator for the selected proof kind.
pub fn bits_eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    randomness_relations: &VerifierRandomnessRelations,
    query_relations: &QueryPositionRelations,
) -> BitsEval {
    BitsEval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        raw_query_kind: BaseField::from(VerifierRandomnessKind::RawQuery.as_u32()),
        relations: QueryBitsComponentRelations::new(randomness_relations, query_relations),
    }
}

/// Construct the query-route evaluator for the selected proof kind.
pub fn mapping_eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    query_relations: &QueryPositionRelations,
) -> MappingEval {
    MappingEval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        binary_active: BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        relations: query_relations.clone(),
    }
}

/// Evaluates the canonical M31 bit-pattern constraint used by the macro AIR.
#[cfg(test)]
fn canonical_inverse_constraint<F>(active: F, bit_sum: F, inverse: F) -> F
where
    F: Clone + From<BaseField> + core::ops::Mul<Output = F> + core::ops::Sub<Output = F>,
{
    (active.clone() * F::from(BaseField::from(M31_BITS as u32)) - bit_sum) * inverse - active
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

/// Generate the raw-word consumer and canonical-bit producer interactions.
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
    query_bits_dsl::component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        BaseField::from(VerifierRandomnessKind::RawQuery.as_u32()),
        &QueryBitsComponentRelations::new(randomness_relations, query_relations),
    )
}

/// Generate canonical-bit consumers and typed-position producers.
pub fn gen_mapping_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    query_relations: &QueryPositionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    query_mapping_dsl::component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode)),
        query_relations,
    )
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
    use stwo_constraint_framework::{FrameworkEval, Relation, assert_constraints_on_polys};

    use super::*;
    use crate::protocol::{OptionalM31Word, PcsParameters};

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
        let eval = bits_eval_for_proof_kind(
            preprocessing.raw_log_size(),
            kind,
            &randomness_relations,
            &query_relations,
        );
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
        let eval =
            mapping_eval_for_proof_kind(preprocessing.mapping_log_size(), kind, &query_relations);
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
    fn m31_zero_cannot_use_the_all_ones_bit_alias() {
        let canonical_constraint = canonical_inverse_constraint(
            BaseField::from(1),
            BaseField::from(M31_BITS as u32),
            BaseField::zero(),
        );
        assert!(!canonical_constraint.is_zero());
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
        let bit_value_consumers = preprocessing
            .raw_rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .fold(QM31::zero(), |sum, row| {
                let word = vm[row.query as usize].as_u32();
                (0..M31_BITS).fold(sum, |sum, bit| {
                    let denominator: QM31 = query_relations.bit_value.combine(&[
                        M31::from(row.verifier_id),
                        M31::from(row.query),
                        M31::from(bit),
                        M31::from((word >> bit) & 1),
                    ]);
                    sum - denominator.inverse()
                })
            });
        assert!(
            (bits_sum + mappings_sum + raw_sources + position_consumers + bit_value_consumers)
                .is_zero()
        );
    }
}
