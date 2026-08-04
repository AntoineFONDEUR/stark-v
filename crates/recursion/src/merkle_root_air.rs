//! Transcript-owned Merkle roots for every fixed PCS authentication path.
//!
//! Each active commitment digest is consumed exactly once from the typed
//! transcript payload relation and expanded into one root-node claim per raw
//! query. Tree identifiers separate verifier lanes and trace versus FRI trees,
//! so no path can terminate at another child or another commitment class.

use core::fmt;

use air::digest::{Digest8, M31Word};
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
};
use stwo_macros::define_component_tables;

use super::control_air::{
    LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID, SEGMENT_VERIFIER_ID,
};
use super::protocol::{FixedProofShape, ProofShapeError, ValidatedPcsParameters};
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::wire::ProofKind;
use crate::relations::RecursionRelations;

const DIGEST_WORDS: usize = 8;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

// The two 15-bit item spaces remain disjoint inside each 16-bit verifier lane.
const VERIFIER_TREE_STRIDE: u32 = 1 << 16;
const FRI_TREE_OFFSET: u32 = 1 << 15;
const TREE_INDEX_LIMIT: usize = FRI_TREE_OFFSET as usize;

const ROW_MASK_COLUMN: usize = 0;
const SEGMENT_MASK_COLUMN: usize = 1;
const BINARY_MASK_COLUMN: usize = 2;
const VERIFIER_ID_COLUMN: usize = 3;
const INPUT_KIND_COLUMN: usize = 4;
const ITEM_COLUMN: usize = 5;
const TREE_ID_COLUMN: usize = 6;
const PATH_COUNT_COLUMN: usize = 7;
const PREPROCESSED_COLUMN_COUNT: usize = 8;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_merkle_root_row_mask",
    "recursion_merkle_root_segment_mask",
    "recursion_merkle_root_binary_mask",
    "recursion_merkle_root_verifier_id",
    "recursion_merkle_root_input_kind",
    "recursion_merkle_root_item",
    "recursion_merkle_root_tree_id",
    "recursion_merkle_root_path_count",
];

define_component_tables! {
    merkle_root: {
        committed: {
            digest_0, digest_1, digest_2, digest_3,
            digest_4, digest_5, digest_6, digest_7,
        },
        constraints: {},
    },
}

use prover_columns::MerkleRootColumns;

/// Transcript commitment class backing one Merkle root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootSource {
    Trace,
    Fri,
}

impl RootSource {
    const fn input_kind(self) -> VerifierInputKind {
        match self {
            Self::Trace => VerifierInputKind::Commitment,
            Self::Fri => VerifierInputKind::FriCommitment,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    segment_mask: u32,
    binary_mask: u32,
    verifier_id: u32,
    source: RootSource,
    item: u32,
    tree_id: u32,
    path_count: u32,
}

/// Trusted root layout for the VM lane and both recursion-verifier lanes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleRootPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
    vm_tree_count: usize,
    vm_fri_layer_count: usize,
    recursion_tree_count: usize,
    recursion_fri_layer_count: usize,
}

impl MerkleRootPreprocessed {
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
    ) -> Result<Self, MerkleRootError> {
        vm_shape
            .validate(vm_pcs)
            .map_err(MerkleRootError::VmShape)?;
        recursion_shape
            .validate(recursion_pcs)
            .map_err(MerkleRootError::RecursionShape)?;
        validate_item_capacity("VM commitment trees", VM_TREES)?;
        validate_item_capacity("VM FRI layers", VM_FRI_LAYERS)?;
        validate_item_capacity("recursion commitment trees", RECURSION_TREES)?;
        validate_item_capacity("recursion FRI layers", RECURSION_FRI_LAYERS)?;

        let mut rows = Vec::new();
        append_lane_rows::<VM_TREES, VM_FRI_LAYERS>(
            &mut rows,
            SEGMENT_VERIFIER_ID,
            1,
            0,
            vm_pcs.config().fri_config.n_queries,
        )?;
        for verifier_id in [LEFT_RECURSION_VERIFIER_ID, RIGHT_RECURSION_VERIFIER_ID] {
            append_lane_rows::<RECURSION_TREES, RECURSION_FRI_LAYERS>(
                &mut rows,
                verifier_id,
                0,
                1,
                recursion_pcs.config().fri_config.n_queries,
            )?;
        }
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(MerkleRootError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(MerkleRootError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            log_size,
            rows,
            vm_tree_count: VM_TREES,
            vm_fri_layer_count: VM_FRI_LAYERS,
            recursion_tree_count: RECURSION_TREES,
            recursion_fri_layer_count: RECURSION_FRI_LAYERS,
        })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
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
            columns[INPUT_KIND_COLUMN][index] = row.source.input_kind().as_u32();
            columns[ITEM_COLUMN][index] = row.item;
            columns[TREE_ID_COLUMN][index] = row.tree_id;
            columns[PATH_COUNT_COLUMN][index] = row.path_count;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

fn validate_item_capacity(field: &'static str, count: usize) -> Result<(), MerkleRootError> {
    if count <= TREE_INDEX_LIMIT {
        Ok(())
    } else {
        Err(MerkleRootError::TreeItemCapacityExceeded { field, count })
    }
}

fn append_lane_rows<const N_TREES: usize, const N_FRI_LAYERS: usize>(
    rows: &mut Vec<PreprocessedRow>,
    verifier_id: u32,
    segment_mask: u32,
    binary_mask: u32,
    path_count: usize,
) -> Result<(), MerkleRootError> {
    let path_count = canonical_usize("Merkle path multiplicity", path_count)?;
    for tree in 0..N_TREES {
        rows.push(PreprocessedRow {
            segment_mask,
            binary_mask,
            verifier_id,
            source: RootSource::Trace,
            item: canonical_usize("commitment tree", tree)?,
            tree_id: trace_tree_id(verifier_id, tree)?,
            path_count,
        });
    }
    for layer in 0..N_FRI_LAYERS {
        rows.push(PreprocessedRow {
            segment_mask,
            binary_mask,
            verifier_id,
            source: RootSource::Fri,
            item: canonical_usize("FRI layer", layer)?,
            tree_id: fri_tree_id(verifier_id, layer)?,
            path_count,
        });
    }
    Ok(())
}

/// Namespaces one trace tree inside its verifier lane.
pub fn trace_tree_id(verifier_id: u32, tree: usize) -> Result<u32, MerkleRootError> {
    namespaced_tree_id(verifier_id, tree, 0, "commitment tree")
}

/// Namespaces one FRI tree inside its verifier lane.
pub fn fri_tree_id(verifier_id: u32, layer: usize) -> Result<u32, MerkleRootError> {
    namespaced_tree_id(verifier_id, layer, FRI_TREE_OFFSET, "FRI layer")
}

fn namespaced_tree_id(
    verifier_id: u32,
    item: usize,
    offset: u32,
    field: &'static str,
) -> Result<u32, MerkleRootError> {
    if item >= TREE_INDEX_LIMIT {
        return Err(MerkleRootError::TreeItemCapacityExceeded {
            field,
            count: item + 1,
        });
    }
    let item = u32::try_from(item).map_err(|_| MerkleRootError::IndexOutOfRange { field, item })?;
    let tree_id = verifier_id
        .checked_mul(VERIFIER_TREE_STRIDE)
        .and_then(|base| base.checked_add(offset))
        .and_then(|base| base.checked_add(item))
        .ok_or(MerkleRootError::TreeIdOverflow)?;
    M31Word::try_from(tree_id)
        .map(M31Word::as_u32)
        .map_err(|_| MerkleRootError::TreeIdNotCanonical { tree_id })
}

fn canonical_usize(field: &'static str, item: usize) -> Result<u32, MerkleRootError> {
    let value =
        u32::try_from(item).map_err(|_| MerkleRootError::IndexOutOfRange { field, item })?;
    M31Word::try_from(value)
        .map(M31Word::as_u32)
        .map_err(|_| MerkleRootError::IndexNotCanonical { field, value })
}

pub type Component = FrameworkComponent<Eval>;

/// Consumes transcript roots and emits one root node per fixed query path.
#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub verifier_input_relations: VerifierInputRelations,
    pub recursion_relations: RecursionRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = MerkleRootColumns::from_eval(&mut eval);
        let ids = MerkleRootPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let segment_mask = eval.get_preprocessed_column(ids[SEGMENT_MASK_COLUMN].clone());
        let binary_mask = eval.get_preprocessed_column(ids[BINARY_MASK_COLUMN].clone());
        let verifier_id = eval.get_preprocessed_column(ids[VERIFIER_ID_COLUMN].clone());
        let input_kind = eval.get_preprocessed_column(ids[INPUT_KIND_COLUMN].clone());
        let item = eval.get_preprocessed_column(ids[ITEM_COLUMN].clone());
        let tree_id = eval.get_preprocessed_column(ids[TREE_ID_COLUMN].clone());
        let path_count = eval.get_preprocessed_column(ids[PATH_COUNT_COLUMN].clone());
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let binary = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::BinaryNode,
        )));
        let active = row_mask * (segment_mask * segment + binary_mask * binary);
        let one = E::F::from(BaseField::from(1));
        let digest = digest_columns(&cols);

        eval.add_constraint(cols.enabler.clone() - active.clone());
        for word in &digest {
            eval.add_constraint((one.clone() - active.clone()) * word.clone());
        }
        for (limb, word) in digest.iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.verifier_input_relations.input_word,
                -E::EF::from(active.clone()),
                &[
                    verifier_id.clone(),
                    input_kind.clone(),
                    item.clone(),
                    E::F::from(BaseField::from(
                        u32::try_from(limb).expect("digest limb fits u32"),
                    )),
                    word.clone(),
                ],
            ));
        }
        let mut node_tuple = vec![
            tree_id,
            E::F::from(BaseField::from(0)),
            E::F::from(BaseField::from(0)),
        ];
        node_tuple.extend(digest);
        eval.add_to_relation(RelationEntry::new(
            &self.recursion_relations.merkle_node,
            E::EF::from(active * path_count),
            &node_tuple,
        ));
        eval.finalize_logup_in_pairs();
        eval
    }
}

fn digest_columns<F: Clone>(cols: &MerkleRootColumns<F>) -> [F; DIGEST_WORDS] {
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

/// Trace and FRI roots carried by one fixed inner proof.
#[derive(Clone, Copy)]
pub struct MerkleRootSet<'a> {
    pub trace: &'a [Digest8],
    pub fri: &'a [Digest8],
}

/// Root witnesses selected by the public universal proof kind.
#[derive(Clone, Copy)]
pub enum UniversalMerkleRootWitness<'a> {
    Segment(MerkleRootSet<'a>),
    Binary {
        left: MerkleRootSet<'a>,
        right: MerkleRootSet<'a>,
    },
    Empty,
}

/// Pushes every active root digest and canonical zeros for inactive lanes.
pub fn push_merkle_roots(
    table: &mut MerkleRootTable,
    preprocessed: &MerkleRootPreprocessed,
    witness: UniversalMerkleRootWitness<'_>,
) -> Result<(), MerkleRootError> {
    validate_witness(preprocessed, witness)?;
    for row in &preprocessed.rows {
        let digest = select_digest(witness, *row)?;
        let mut values = Vec::with_capacity(1 + DIGEST_WORDS);
        values.push(u32::from(digest.is_some()));
        values.extend(digest.unwrap_or(Digest8::ZERO).words().map(M31Word::as_u32));
        table.push_row(&values);
    }
    Ok(())
}

fn validate_witness(
    preprocessed: &MerkleRootPreprocessed,
    witness: UniversalMerkleRootWitness<'_>,
) -> Result<(), MerkleRootError> {
    match witness {
        UniversalMerkleRootWitness::Segment(roots) => validate_root_set(
            SEGMENT_VERIFIER_ID,
            preprocessed.vm_tree_count,
            preprocessed.vm_fri_layer_count,
            roots,
        ),
        UniversalMerkleRootWitness::Binary { left, right } => {
            validate_root_set(
                LEFT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_tree_count,
                preprocessed.recursion_fri_layer_count,
                left,
            )?;
            validate_root_set(
                RIGHT_RECURSION_VERIFIER_ID,
                preprocessed.recursion_tree_count,
                preprocessed.recursion_fri_layer_count,
                right,
            )
        }
        UniversalMerkleRootWitness::Empty => Ok(()),
    }
}

fn validate_root_set(
    verifier_id: u32,
    expected_trace: usize,
    expected_fri: usize,
    roots: MerkleRootSet<'_>,
) -> Result<(), MerkleRootError> {
    validate_root_count(
        verifier_id,
        RootSource::Trace,
        expected_trace,
        roots.trace.len(),
    )?;
    validate_root_count(verifier_id, RootSource::Fri, expected_fri, roots.fri.len())
}

fn validate_root_count(
    verifier_id: u32,
    source: RootSource,
    expected: usize,
    actual: usize,
) -> Result<(), MerkleRootError> {
    if expected == actual {
        Ok(())
    } else {
        Err(MerkleRootError::RootCountMismatch {
            verifier_id,
            source,
            expected,
            actual,
        })
    }
}

fn select_digest(
    witness: UniversalMerkleRootWitness<'_>,
    row: PreprocessedRow,
) -> Result<Option<Digest8>, MerkleRootError> {
    let roots = match (witness, row.verifier_id) {
        (UniversalMerkleRootWitness::Segment(roots), SEGMENT_VERIFIER_ID) => Some(roots),
        (UniversalMerkleRootWitness::Binary { left, .. }, LEFT_RECURSION_VERIFIER_ID) => Some(left),
        (UniversalMerkleRootWitness::Binary { right, .. }, RIGHT_RECURSION_VERIFIER_ID) => {
            Some(right)
        }
        (UniversalMerkleRootWitness::Empty, SEGMENT_VERIFIER_ID)
        | (UniversalMerkleRootWitness::Empty, LEFT_RECURSION_VERIFIER_ID)
        | (UniversalMerkleRootWitness::Empty, RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalMerkleRootWitness::Segment(_), LEFT_RECURSION_VERIFIER_ID)
        | (UniversalMerkleRootWitness::Segment(_), RIGHT_RECURSION_VERIFIER_ID)
        | (UniversalMerkleRootWitness::Binary { .. }, SEGMENT_VERIFIER_ID) => None,
        (_, verifier_id) => return Err(MerkleRootError::UnknownVerifierId { verifier_id }),
    };
    roots
        .map(|roots| {
            let items = match row.source {
                RootSource::Trace => roots.trace,
                RootSource::Fri => roots.fri,
            };
            items
                .get(row.item as usize)
                .copied()
                .ok_or(MerkleRootError::RootMissing {
                    verifier_id: row.verifier_id,
                    source: row.source,
                    item: row.item,
                })
        })
        .transpose()
}

/// Generates transcript-root consumers and multiplicity-weighted path roots.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    verifier_input_relations: &VerifierInputRelations,
    recursion_relations: &RecursionRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = MerkleRootColumns::from_iter(trace.iter().map(|column| &column.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let digest = digest_columns(&cols);
    let size = cols.enabler.len();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let binary = BaseField::from(u32::from(proof_kind == ProofKind::BinaryNode));
    let active = (0..size)
        .map(|row| {
            PackedQM31::from(
                pp[ROW_MASK_COLUMN][row]
                    * (pp[SEGMENT_MASK_COLUMN][row] * segment
                        + pp[BINARY_MASK_COLUMN][row] * binary),
            )
        })
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let input_denominators = (0..DIGEST_WORDS)
        .map(|limb_index| {
            let limb = PackedM31::broadcast(BaseField::from(
                u32::try_from(limb_index).expect("digest limb fits u32"),
            ));
            (0..size)
                .map(|row| {
                    verifier_input_relations.input_word.combine(&[
                        pp[VERIFIER_ID_COLUMN][row],
                        pp[INPUT_KIND_COLUMN][row],
                        pp[ITEM_COLUMN][row],
                        limb,
                        digest[limb_index][row],
                    ])
                })
                .collect::<Vec<PackedQM31>>()
        })
        .collect::<Vec<_>>();
    let zero = PackedM31::broadcast(BaseField::from(0));
    let node_denominator = (0..size)
        .map(|row| {
            recursion_relations.merkle_node.combine(&[
                pp[TREE_ID_COLUMN][row],
                zero,
                zero,
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
    let node_numerator = (0..size)
        .map(|row| active[row] * pp[PATH_COUNT_COLUMN][row])
        .collect::<Vec<_>>();

    let mut logup = LogupTraceGenerator::new(trace[0].domain.log_size());
    write_pair!(
        &negative_active,
        &input_denominators[0],
        &negative_active,
        &input_denominators[1],
        logup
    );
    write_pair!(
        &negative_active,
        &input_denominators[2],
        &negative_active,
        &input_denominators[3],
        logup
    );
    write_pair!(
        &negative_active,
        &input_denominators[4],
        &negative_active,
        &input_denominators[5],
        logup
    );
    write_pair!(
        &negative_active,
        &input_denominators[6],
        &negative_active,
        &input_denominators[7],
        logup
    );
    write_col!(&node_numerator, &node_denominator, logup);
    logup.finalize_last()
}

/// Invalid root geometry, namespace, or universal witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MerkleRootError {
    VmShape(ProofShapeError),
    RecursionShape(ProofShapeError),
    RowCountOverflow,
    LogSizeOutOfRange {
        log_size: u32,
    },
    TreeItemCapacityExceeded {
        field: &'static str,
        count: usize,
    },
    IndexOutOfRange {
        field: &'static str,
        item: usize,
    },
    IndexNotCanonical {
        field: &'static str,
        value: u32,
    },
    TreeIdOverflow,
    TreeIdNotCanonical {
        tree_id: u32,
    },
    RootCountMismatch {
        verifier_id: u32,
        source: RootSource,
        expected: usize,
        actual: usize,
    },
    UnknownVerifierId {
        verifier_id: u32,
    },
    RootMissing {
        verifier_id: u32,
        source: RootSource,
        item: u32,
    },
}

impl fmt::Display for MerkleRootError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for MerkleRootError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::assert_constraints_on_polys;

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

    fn preprocessing() -> MerkleRootPreprocessed {
        MerkleRootPreprocessed::new(pcs(), &shape(), pcs(), &shape())
            .expect("fixture Merkle root geometry is valid")
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new(core::array::from_fn(|index| {
            M31Word::from(seed + index as u16)
        }))
    }

    fn roots(seed: u16) -> ([Digest8; TREE_COUNT], [Digest8; FRI_LAYER_COUNT]) {
        (
            core::array::from_fn(|index| digest(seed + index as u16 * 10)),
            core::array::from_fn(|index| digest(seed + 100 + index as u16 * 10)),
        )
    }

    fn materialize(kind: ProofKind) -> (MerkleRootPreprocessed, MerkleRootTable) {
        let preprocessing = preprocessing();
        let (vm_trace, vm_fri) = roots(10);
        let (left_trace, left_fri) = roots(300);
        let (right_trace, right_fri) = roots(600);
        let witness = match kind {
            ProofKind::SegmentLeaf => UniversalMerkleRootWitness::Segment(MerkleRootSet {
                trace: &vm_trace,
                fri: &vm_fri,
            }),
            ProofKind::BinaryNode => UniversalMerkleRootWitness::Binary {
                left: MerkleRootSet {
                    trace: &left_trace,
                    fri: &left_fri,
                },
                right: MerkleRootSet {
                    trace: &right_trace,
                    fri: &right_fri,
                },
            },
            ProofKind::EmptyLeaf => UniversalMerkleRootWitness::Empty,
        };
        let mut table = MerkleRootTable::new();
        push_merkle_roots(&mut table, &preprocessing, witness).expect("fixture roots materialize");
        (preprocessing, table)
    }

    fn assert_constraints(kind: ProofKind, tamper_inactive: bool) {
        let (preprocessing, mut table) = materialize(kind);
        if tamper_inactive {
            table.digest_0[0] = 1;
        }
        let verifier_input_relations = VerifierInputRelations::dummy();
        let recursion_relations = RecursionRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &verifier_input_relations,
            &recursion_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            verifier_input_relations,
            recursion_relations,
        };
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
    fn every_universal_mode_satisfies_merkle_root_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, false);
    }

    #[test]
    #[should_panic]
    fn inactive_merkle_roots_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, true);
    }

    #[test]
    fn all_root_tree_namespaces_are_distinct() {
        let preprocessing = preprocessing();
        let distinct = preprocessing
            .rows
            .iter()
            .map(|row| row.tree_id)
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(distinct.len(), preprocessing.rows.len());
    }

    #[test]
    fn transcript_roots_and_path_consumers_close_exactly() {
        let (preprocessing, table) = materialize(ProofKind::SegmentLeaf);
        let trace = table.into_witness();
        let mut channel = Poseidon2M31Channel::default();
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let recursion_relations = RecursionRelations::draw(&mut channel);
        let (_, root_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &verifier_input_relations,
            &recursion_relations,
        );
        let external = preprocessing
            .rows
            .iter()
            .filter(|row| row.segment_mask == 1)
            .enumerate()
            .fold(QM31::zero(), |sum, (index, row)| {
                let digest = [
                    trace[1].values.at(index),
                    trace[2].values.at(index),
                    trace[3].values.at(index),
                    trace[4].values.at(index),
                    trace[5].values.at(index),
                    trace[6].values.at(index),
                    trace[7].values.at(index),
                    trace[8].values.at(index),
                ];
                let inputs = digest
                    .iter()
                    .enumerate()
                    .fold(QM31::zero(), |sum, (limb, word)| {
                        let denominator: QM31 = verifier_input_relations.input_word.combine(&[
                            M31::from(row.verifier_id),
                            M31::from(row.source.input_kind().as_u32()),
                            M31::from(row.item),
                            M31::from(u32::try_from(limb).expect("digest limb fits u32")),
                            *word,
                        ]);
                        sum + denominator.inverse()
                    });
                let denominator: QM31 = recursion_relations.merkle_node.combine(&[
                    M31::from(row.tree_id),
                    M31::from(0),
                    M31::from(0),
                    digest[0],
                    digest[1],
                    digest[2],
                    digest[3],
                    digest[4],
                    digest[5],
                    digest[6],
                    digest[7],
                ]);
                sum + inputs - denominator.inverse() * M31::from(row.path_count)
            });
        assert!((root_sum + external).is_zero());
    }
}
