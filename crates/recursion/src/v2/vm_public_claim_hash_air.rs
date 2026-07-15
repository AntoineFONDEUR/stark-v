//! Poseidon2 proof of the fixed words behind the VM public-claim digest.
//!
//! Each trusted row consumes eight indexed claim words or canonical padding,
//! chains the full permutation state, and binds the atomic permutation tuple
//! to the standard Poseidon2 component. The first capacity state contains the
//! claim domain, and the last rate state consumes the exact digest absorbed by
//! the segment verifier transcript.

use core::fmt;

use air::digest::M31Word;
use air::poseidon2::{T, poseidon2_traced_state};
use air::trace::Poseidon2Table;
use num_traits::One;
use prover::public_data::PublicData;
use prover::relations::Relations;
use simd::AlignedVec;
use stwo::core::ColumnVec;
use stwo::core::channel::Channel;
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
    EvalAtRow, FrameworkComponent, FrameworkEval, LogupTraceGenerator, RelationEntry, relation,
};
use stwo_macros::define_component_tables;

use super::control_air::SEGMENT_VERIFIER_ID;
use super::transcript_payload_air::{VerifierInputKind, VerifierInputRelations};
use super::vm_public_claim::{
    VmPublicClaimError, VmPublicClaimShape, canonical_vm_public_claim_words, vm_public_claim_digest,
};
use super::vm_public_claim_input_air::{VM_CLAIM_HASH_SCOPE, VmPublicClaimInputRelations};
use super::wire::ProofKind;

const RATE: usize = T / 2;
const VM_PUBLIC_CLAIM_HASH_DOMAIN: u32 = 0x5643;
const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const STEP_COLUMN: usize = 1;
const FIRST_MASK_COLUMN: usize = 2;
const LAST_MASK_COLUMN: usize = 3;
const CHUNK_COLUMNS_START: usize = 4;
const CHUNK_COLUMNS_PER_WORD: usize = 3;
const PREPROCESSED_COLUMN_COUNT: usize = CHUNK_COLUMNS_START + RATE * CHUNK_COLUMNS_PER_WORD;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_v2_vm_claim_hash_row_mask",
    "recursion_v2_vm_claim_hash_step",
    "recursion_v2_vm_claim_hash_first_mask",
    "recursion_v2_vm_claim_hash_last_mask",
    "recursion_v2_vm_claim_hash_chunk_0_source_mask",
    "recursion_v2_vm_claim_hash_chunk_0_word_index",
    "recursion_v2_vm_claim_hash_chunk_0_constant",
    "recursion_v2_vm_claim_hash_chunk_1_source_mask",
    "recursion_v2_vm_claim_hash_chunk_1_word_index",
    "recursion_v2_vm_claim_hash_chunk_1_constant",
    "recursion_v2_vm_claim_hash_chunk_2_source_mask",
    "recursion_v2_vm_claim_hash_chunk_2_word_index",
    "recursion_v2_vm_claim_hash_chunk_2_constant",
    "recursion_v2_vm_claim_hash_chunk_3_source_mask",
    "recursion_v2_vm_claim_hash_chunk_3_word_index",
    "recursion_v2_vm_claim_hash_chunk_3_constant",
    "recursion_v2_vm_claim_hash_chunk_4_source_mask",
    "recursion_v2_vm_claim_hash_chunk_4_word_index",
    "recursion_v2_vm_claim_hash_chunk_4_constant",
    "recursion_v2_vm_claim_hash_chunk_5_source_mask",
    "recursion_v2_vm_claim_hash_chunk_5_word_index",
    "recursion_v2_vm_claim_hash_chunk_5_constant",
    "recursion_v2_vm_claim_hash_chunk_6_source_mask",
    "recursion_v2_vm_claim_hash_chunk_6_word_index",
    "recursion_v2_vm_claim_hash_chunk_6_constant",
    "recursion_v2_vm_claim_hash_chunk_7_source_mask",
    "recursion_v2_vm_claim_hash_chunk_7_word_index",
    "recursion_v2_vm_claim_hash_chunk_7_constant",
];

define_component_tables! {
    vm_public_claim_hash: {
        committed: {
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
}

use prover_columns::VmPublicClaimHashColumns;

// Internal state tuple: fixed step and the complete 16-word state.
relation!(VmPublicClaimHashStateRelation, 17);

/// Relation used only to close consecutive fixed hash rows.
#[derive(Clone)]
pub struct VmPublicClaimHashRelations {
    pub state: VmPublicClaimHashStateRelation,
}

impl VmPublicClaimHashRelations {
    pub fn dummy() -> Self {
        Self {
            state: VmPublicClaimHashStateRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            state: VmPublicClaimHashStateRelation::draw(channel),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChunkSource {
    ClaimWord(u32),
    Constant(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    step: u32,
    first: bool,
    last: bool,
    chunks: [ChunkSource; RATE],
}

/// Fixed sponge schedule derived from the trusted claim shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicClaimHashPreprocessed {
    shape: VmPublicClaimShape,
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmPublicClaimHashPreprocessed {
    pub fn new(shape: VmPublicClaimShape) -> Result<Self, VmPublicClaimHashError> {
        let word_count = shape.claim_word_count();
        let padded_word_count = word_count
            .checked_add(1)
            .ok_or(VmPublicClaimHashError::RowCountOverflow)?;
        let row_count = padded_word_count.div_ceil(RATE);
        let mut rows = Vec::with_capacity(row_count);
        for step in 0..row_count {
            let mut chunks = [ChunkSource::Constant(0); RATE];
            for (slot, source) in chunks.iter_mut().enumerate() {
                let index = step
                    .checked_mul(RATE)
                    .and_then(|start| start.checked_add(slot))
                    .ok_or(VmPublicClaimHashError::RowCountOverflow)?;
                *source = if index < word_count {
                    ChunkSource::ClaimWord(
                        u32::try_from(index)
                            .map_err(|_| VmPublicClaimHashError::WordIndexOutOfRange { index })?,
                    )
                } else if index == word_count {
                    ChunkSource::Constant(1)
                } else {
                    ChunkSource::Constant(0)
                };
            }
            rows.push(PreprocessedRow {
                step: u32::try_from(step)
                    .map_err(|_| VmPublicClaimHashError::StepOutOfRange { step })?,
                first: step == 0,
                last: step + 1 == row_count,
                chunks,
            });
        }
        let padded_rows = row_count
            .checked_next_power_of_two()
            .ok_or(VmPublicClaimHashError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicClaimHashError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            shape,
            log_size,
            rows,
        })
    }

    pub const fn shape(&self) -> VmPublicClaimShape {
        self.shape
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn step_count(&self) -> usize {
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
        let mut columns = (0..PREPROCESSED_COLUMN_COUNT)
            .map(|_| {
                let mut column = AlignedVec::with_capacity(size);
                column.resize(size, 0);
                column
            })
            .collect::<Vec<_>>();
        for (row_index, row) in self.rows.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][row_index] = 1;
            columns[STEP_COLUMN][row_index] = row.step;
            columns[FIRST_MASK_COLUMN][row_index] = u32::from(row.first);
            columns[LAST_MASK_COLUMN][row_index] = u32::from(row.last);
            for (slot, source) in row.chunks.into_iter().enumerate() {
                let start = chunk_column(slot);
                match source {
                    ChunkSource::ClaimWord(index) => {
                        columns[start][row_index] = 1;
                        columns[start + 1][row_index] = index;
                    }
                    ChunkSource::Constant(value) => columns[start + 2][row_index] = value,
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

const fn chunk_column(slot: usize) -> usize {
    CHUNK_COLUMNS_START + slot * CHUNK_COLUMNS_PER_WORD
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub vm_relations: Relations,
    pub claim_input_relations: VmPublicClaimInputRelations,
    pub hash_relations: VmPublicClaimHashRelations,
    pub verifier_input_relations: VerifierInputRelations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = VmPublicClaimHashColumns::from_eval(&mut eval);
        let ids = VmPublicClaimHashPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let step = eval.get_preprocessed_column(ids[STEP_COLUMN].clone());
        let first = eval.get_preprocessed_column(ids[FIRST_MASK_COLUMN].clone());
        let last = eval.get_preprocessed_column(ids[LAST_MASK_COLUMN].clone());
        let chunk_metadata: [(E::F, E::F, E::F); RATE] = core::array::from_fn(|slot| {
            let start = chunk_column(slot);
            (
                eval.get_preprocessed_column(ids[start].clone()),
                eval.get_preprocessed_column(ids[start + 1].clone()),
                eval.get_preprocessed_column(ids[start + 2].clone()),
            )
        });
        let previous = previous_columns(&cols);
        let chunks = chunk_columns(&cols);
        let output = output_columns(&cols);
        let one = E::F::from(BaseField::from(1));
        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let active = row_mask * segment;
        eval.add_constraint(cols.enabler.clone() - active.clone());
        for value in previous.iter().chain(&chunks).chain(&output) {
            eval.add_constraint((one.clone() - active.clone()) * value.clone());
        }

        for (index, value) in previous.iter().enumerate() {
            let initial = if index + 1 == T {
                VM_PUBLIC_CLAIM_HASH_DOMAIN
            } else {
                0
            };
            eval.add_constraint(
                active.clone()
                    * first.clone()
                    * (value.clone() - E::F::from(BaseField::from(initial))),
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
        for (slot, chunk) in chunks.iter().enumerate() {
            let (source_mask, _, constant) = &chunk_metadata[slot];
            eval.add_constraint(
                active.clone()
                    * (one.clone() - source_mask.clone())
                    * (chunk.clone() - constant.clone()),
            );
        }

        eval.add_to_relation(RelationEntry::new(
            &self.vm_relations.poseidon2_io,
            -E::EF::from(active.clone()),
            &poseidon_tuple,
        ));

        for (slot, chunk) in chunks.iter().enumerate() {
            let (source_mask, word_index, _) = &chunk_metadata[slot];
            eval.add_to_relation(RelationEntry::new(
                &self.claim_input_relations.claim_word,
                -E::EF::from(active.clone() * source_mask.clone()),
                &[
                    E::F::from(BaseField::from(VM_CLAIM_HASH_SCOPE)),
                    word_index.clone(),
                    chunk.clone(),
                ],
            ));
        }

        let mut previous_tuple = vec![step.clone()];
        previous_tuple.extend(previous.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.hash_relations.state,
            -E::EF::from(active.clone() * (one.clone() - first)),
            &previous_tuple,
        ));
        let mut output_tuple = vec![step + one.clone()];
        output_tuple.extend(output.iter().cloned());
        eval.add_to_relation(RelationEntry::new(
            &self.hash_relations.state,
            E::EF::from(active.clone() * (one.clone() - last.clone())),
            &output_tuple,
        ));

        for (limb, digest_word) in output[..RATE].iter().enumerate() {
            eval.add_to_relation(RelationEntry::new(
                &self.verifier_input_relations.input_word,
                -E::EF::from(active.clone() * last.clone()),
                &[
                    E::F::from(BaseField::from(SEGMENT_VERIFIER_ID)),
                    E::F::from(BaseField::from(
                        VerifierInputKind::VmPublicClaimDigest.as_u32(),
                    )),
                    E::F::from(BaseField::from(0)),
                    E::F::from(BaseField::from(
                        u32::try_from(limb).expect("digest limb fits u32"),
                    )),
                    digest_word.clone(),
                ],
            ));
        }

        eval.finalize_logup_in_pairs();
        eval
    }
}

fn previous_columns<F: Clone>(cols: &VmPublicClaimHashColumns<F>) -> [F; T] {
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

fn chunk_columns<F: Clone>(cols: &VmPublicClaimHashColumns<F>) -> [F; RATE] {
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

fn output_columns<F: Clone>(cols: &VmPublicClaimHashColumns<F>) -> [F; T] {
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

/// Generates the hash, claim-word, state-chain, and transcript-digest fractions.
#[allow(clippy::too_many_arguments)]
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    vm_relations: &Relations,
    claim_input_relations: &VmPublicClaimInputRelations,
    hash_relations: &VmPublicClaimHashRelations,
    verifier_input_relations: &VerifierInputRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols =
        VmPublicClaimHashColumns::from_iter(trace.iter().map(|evaluation| &evaluation.values.data));
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let simd_size = cols.enabler.len();
    let log_size = trace[0].domain.log_size();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let active = (0..simd_size)
        .map(|row| PackedQM31::from(pp[ROW_MASK_COLUMN][row] * segment))
        .collect::<Vec<_>>();
    let negative_active = active.iter().map(|value| -*value).collect::<Vec<_>>();
    let first = (0..simd_size)
        .map(|row| PackedQM31::from(pp[FIRST_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let last = (0..simd_size)
        .map(|row| PackedQM31::from(pp[LAST_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let not_first = active
        .iter()
        .zip(&first)
        .map(|(active, first)| -*active * (PackedQM31::one() - *first))
        .collect::<Vec<_>>();
    let not_last = active
        .iter()
        .zip(&last)
        .map(|(active, last)| *active * (PackedQM31::one() - *last))
        .collect::<Vec<_>>();
    let digest_multiplicity = active
        .iter()
        .zip(&last)
        .map(|(active, last)| -*active * *last)
        .collect::<Vec<_>>();

    let in_rate = [
        add_columns(cols.previous_0, cols.chunk_0),
        add_columns(cols.previous_1, cols.chunk_1),
        add_columns(cols.previous_2, cols.chunk_2),
        add_columns(cols.previous_3, cols.chunk_3),
        add_columns(cols.previous_4, cols.chunk_4),
        add_columns(cols.previous_5, cols.chunk_5),
        add_columns(cols.previous_6, cols.chunk_6),
        add_columns(cols.previous_7, cols.chunk_7),
    ];
    let poseidon_denom = combine!(
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
            cols.previous_8,
            cols.previous_9,
            cols.previous_10,
            cols.previous_11,
            cols.previous_12,
            cols.previous_13,
            cols.previous_14,
            cols.previous_15,
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7,
            cols.output_8,
            cols.output_9,
            cols.output_10,
            cols.output_11,
            cols.output_12,
            cols.output_13,
            cols.output_14,
            cols.output_15
        ]
    );

    let hash_scope = vec![PackedM31::broadcast(BaseField::from(VM_CLAIM_HASH_SCOPE)); simd_size];
    let chunk_values = [
        cols.chunk_0,
        cols.chunk_1,
        cols.chunk_2,
        cols.chunk_3,
        cols.chunk_4,
        cols.chunk_5,
        cols.chunk_6,
        cols.chunk_7,
    ];
    let chunk_multiplicities = (0..RATE)
        .map(|slot| {
            (0..simd_size)
                .map(|row| -active[row] * PackedQM31::from(pp[chunk_column(slot)][row]))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let chunk_denoms = (0..RATE)
        .map(|slot| {
            combine!(
                claim_input_relations.claim_word,
                [&hash_scope, pp[chunk_column(slot) + 1], chunk_values[slot]]
            )
        })
        .collect::<Vec<_>>();

    let one = PackedM31::broadcast(BaseField::from(1));
    let step_plus_one = (0..simd_size)
        .map(|row| pp[STEP_COLUMN][row] + one)
        .collect::<Vec<_>>();
    let previous_denom = combine!(
        hash_relations.state,
        [
            pp[STEP_COLUMN],
            cols.previous_0,
            cols.previous_1,
            cols.previous_2,
            cols.previous_3,
            cols.previous_4,
            cols.previous_5,
            cols.previous_6,
            cols.previous_7,
            cols.previous_8,
            cols.previous_9,
            cols.previous_10,
            cols.previous_11,
            cols.previous_12,
            cols.previous_13,
            cols.previous_14,
            cols.previous_15
        ]
    );
    let output_denom = combine!(
        hash_relations.state,
        [
            &step_plus_one,
            cols.output_0,
            cols.output_1,
            cols.output_2,
            cols.output_3,
            cols.output_4,
            cols.output_5,
            cols.output_6,
            cols.output_7,
            cols.output_8,
            cols.output_9,
            cols.output_10,
            cols.output_11,
            cols.output_12,
            cols.output_13,
            cols.output_14,
            cols.output_15
        ]
    );

    let verifier_id = vec![PackedM31::broadcast(BaseField::from(SEGMENT_VERIFIER_ID)); simd_size];
    let input_kind = vec![
        PackedM31::broadcast(BaseField::from(
            VerifierInputKind::VmPublicClaimDigest.as_u32(),
        ));
        simd_size
    ];
    let zero = vec![PackedM31::broadcast(BaseField::from(0)); simd_size];
    let digest_values = [
        cols.output_0,
        cols.output_1,
        cols.output_2,
        cols.output_3,
        cols.output_4,
        cols.output_5,
        cols.output_6,
        cols.output_7,
    ];
    let digest_denoms = (0..RATE)
        .map(|limb| {
            let limb_index = vec![
                PackedM31::broadcast(BaseField::from(
                    u32::try_from(limb).expect("digest limb fits u32"),
                ));
                simd_size
            ];
            combine!(
                verifier_input_relations.input_word,
                [
                    &verifier_id,
                    &input_kind,
                    &zero,
                    limb_index,
                    digest_values[limb]
                ]
            )
        })
        .collect::<Vec<_>>();

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(
        &negative_active,
        &poseidon_denom,
        &chunk_multiplicities[0],
        &chunk_denoms[0],
        logup_gen
    );
    write_pair!(
        &chunk_multiplicities[1],
        &chunk_denoms[1],
        &chunk_multiplicities[2],
        &chunk_denoms[2],
        logup_gen
    );
    write_pair!(
        &chunk_multiplicities[3],
        &chunk_denoms[3],
        &chunk_multiplicities[4],
        &chunk_denoms[4],
        logup_gen
    );
    write_pair!(
        &chunk_multiplicities[5],
        &chunk_denoms[5],
        &chunk_multiplicities[6],
        &chunk_denoms[6],
        logup_gen
    );
    write_pair!(
        &chunk_multiplicities[7],
        &chunk_denoms[7],
        &not_first,
        &previous_denom,
        logup_gen
    );
    write_pair!(
        &not_last,
        &output_denom,
        &digest_multiplicity,
        &digest_denoms[0],
        logup_gen
    );
    write_pair!(
        &digest_multiplicity,
        &digest_denoms[1],
        &digest_multiplicity,
        &digest_denoms[2],
        logup_gen
    );
    write_pair!(
        &digest_multiplicity,
        &digest_denoms[3],
        &digest_multiplicity,
        &digest_denoms[4],
        logup_gen
    );
    write_pair!(
        &digest_multiplicity,
        &digest_denoms[5],
        &digest_multiplicity,
        &digest_denoms[6],
        logup_gen
    );
    write_col!(&digest_multiplicity, &digest_denoms[7], logup_gen);
    logup_gen.finalize_last()
}

fn add_columns(lhs: &[PackedM31], rhs: &[PackedM31]) -> Vec<PackedM31> {
    lhs.iter().zip(rhs).map(|(lhs, rhs)| *lhs + *rhs).collect()
}

/// Records the fixed claim sponge and every reused Poseidon2 permutation.
pub fn push_vm_public_claim_hash(
    table: &mut VmPublicClaimHashTable,
    poseidon2: &mut Poseidon2Table,
    preprocessed: &VmPublicClaimHashPreprocessed,
    proof_kind: ProofKind,
    public_data: Option<&PublicData>,
) -> Result<(), VmPublicClaimHashError> {
    let active = proof_kind == ProofKind::SegmentLeaf;
    let words = match (active, public_data) {
        (true, Some(public_data)) => {
            canonical_vm_public_claim_words(public_data, preprocessed.shape)
                .map_err(VmPublicClaimHashError::Claim)?
        }
        (true, None) => return Err(VmPublicClaimHashError::SegmentClaimMissing),
        (false, Some(_)) => return Err(VmPublicClaimHashError::InactiveClaimProvided),
        (false, None) => Vec::new(),
    };
    if !active {
        for _ in &preprocessed.rows {
            table.push_row_values(&[0; 41]);
        }
        return Ok(());
    }

    let mut stream = words.iter().map(|word| word.as_u32()).collect::<Vec<_>>();
    stream.push(1);
    stream.resize(preprocessed.step_count() * RATE, 0);
    let mut state = [0_u32; T];
    state[T - 1] = VM_PUBLIC_CLAIM_HASH_DOMAIN;
    for (row_index, row) in preprocessed.rows.iter().enumerate() {
        let chunk: [u32; RATE] = stream[row_index * RATE..(row_index + 1) * RATE]
            .try_into()
            .expect("trusted chunk width is fixed");
        let mut permutation_input = state;
        for (value, absorbed) in permutation_input.iter_mut().zip(chunk) {
            *value = (u64::from(*value) + u64::from(absorbed))
                .rem_euclid(u64::from(stwo::core::fields::m31::P)) as u32;
        }
        let output = poseidon2_traced_state(poseidon2, permutation_input, false, true);
        let mut values = Vec::with_capacity(41);
        values.push(1);
        values.extend(state);
        values.extend(chunk);
        values.extend(output);
        table.push_row_values(&values);
        state = output;
        debug_assert_eq!(row.step as usize, row_index);
    }
    let expected = vm_public_claim_digest(
        public_data.expect("active claim was checked above"),
        preprocessed.shape,
    )
    .map_err(VmPublicClaimHashError::Claim)?;
    let actual = &state[..RATE];
    if actual != expected.digest().words().map(M31Word::as_u32) {
        return Err(VmPublicClaimHashError::DigestMismatch);
    }
    Ok(())
}

impl VmPublicClaimHashTable {
    fn push_row_values(&mut self, values: &[u32]) {
        self.push_row(values);
    }
}

/// Invalid trusted hash schedule or claim witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimHashError {
    Claim(VmPublicClaimError),
    RowCountOverflow,
    WordIndexOutOfRange { index: usize },
    StepOutOfRange { step: usize },
    LogSizeOutOfRange { log_size: u32 },
    SegmentClaimMissing,
    InactiveClaimProvided,
    DigestMismatch,
}

impl fmt::Display for VmPublicClaimHashError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Claim(error) => write!(formatter, "invalid VM public claim: {error}"),
            Self::RowCountOverflow => write!(formatter, "VM claim hash row count overflowed"),
            Self::WordIndexOutOfRange { index } => {
                write!(formatter, "VM claim hash word index {index} exceeds u32")
            }
            Self::StepOutOfRange { step } => {
                write!(formatter, "VM claim hash step {step} exceeds u32")
            }
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "VM claim hash log size {log_size} exceeds {MAX_LOG_SIZE}"
            ),
            Self::SegmentClaimMissing => write!(formatter, "segment leaf has no VM public claim"),
            Self::InactiveClaimProvided => {
                write!(formatter, "non-segment proof carries a VM public claim")
            }
            Self::DigestMismatch => write!(formatter, "VM claim hash output disagrees with digest"),
        }
    }
}

impl std::error::Error for VmPublicClaimHashError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use rstest::rstest;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{Relation, assert_constraints_on_polys};

    use super::*;
    use crate::v2::vm_public_claim::tests::{public_data, shape};

    #[derive(Clone, Copy)]
    enum HashTamper {
        InitialCapacity,
        EndMarker,
        InactiveState,
    }

    fn assert_constraints(kind: ProofKind, tamper: Option<HashTamper>) {
        let preprocessing =
            VmPublicClaimHashPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let witness = (kind == ProofKind::SegmentLeaf).then_some(&claim);
        let mut table = VmPublicClaimHashTable::new();
        push_vm_public_claim_hash(
            &mut table,
            &mut Poseidon2Table::new(),
            &preprocessing,
            kind,
            witness,
        )
        .expect("fixture claim hash materializes");
        match tamper {
            Some(HashTamper::InitialCapacity) => table.previous_15[0] = 0,
            Some(HashTamper::EndMarker) => {
                let marker_index = preprocessing.shape.claim_word_count();
                let row = marker_index / RATE;
                match marker_index % RATE {
                    0 => table.chunk_0[row] = 0,
                    1 => table.chunk_1[row] = 0,
                    2 => table.chunk_2[row] = 0,
                    3 => table.chunk_3[row] = 0,
                    4 => table.chunk_4[row] = 0,
                    5 => table.chunk_5[row] = 0,
                    6 => table.chunk_6[row] = 0,
                    7 => table.chunk_7[row] = 0,
                    _ => unreachable!("slot is reduced modulo the rate"),
                }
            }
            Some(HashTamper::InactiveState) => table.previous_0[0] = 1,
            None => {}
        }
        let vm_relations = Relations::dummy();
        let claim_input_relations = VmPublicClaimInputRelations::dummy();
        let hash_relations = VmPublicClaimHashRelations::dummy();
        let verifier_input_relations = VerifierInputRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &vm_relations,
            &claim_input_relations,
            &hash_relations,
            &verifier_input_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            vm_relations,
            claim_input_relations,
            hash_relations,
            verifier_input_relations,
        };
        assert_constraints_on_polys(
            &trace_polys,
            CanonicCoset::new(preprocessing.log_size()),
            |row| {
                eval.evaluate(row);
            },
            claimed_sum,
        );
    }

    fn complete_relation_sum(tamper_previous: bool) -> QM31 {
        let shape = shape();
        let preprocessing =
            VmPublicClaimHashPreprocessed::new(shape).expect("fixture shape is supported");
        let claim = public_data();
        let mut table = VmPublicClaimHashTable::new();
        let mut poseidon2 = Poseidon2Table::new();
        push_vm_public_claim_hash(
            &mut table,
            &mut poseidon2,
            &preprocessing,
            ProofKind::SegmentLeaf,
            Some(&claim),
        )
        .expect("fixture claim hash materializes");
        if tamper_previous {
            table.previous_0[1] += 1;
        }

        let mut channel = Poseidon2M31Channel::default();
        let vm_relations = Relations::draw(&mut channel);
        let claim_input_relations = VmPublicClaimInputRelations::draw(&mut channel);
        let hash_relations = VmPublicClaimHashRelations::draw(&mut channel);
        let verifier_input_relations = VerifierInputRelations::draw(&mut channel);
        let trace = table.into_witness();
        let (_, hash_sum) = gen_interaction_trace(
            &trace,
            &preprocessing.gen_columns(),
            ProofKind::SegmentLeaf,
            &vm_relations,
            &claim_input_relations,
            &hash_relations,
            &verifier_input_relations,
        );
        let poseidon_trace = poseidon2.into_witness();
        let (_, poseidon_sum) = air::poseidon2::component::witness::gen_interaction_trace(
            &poseidon_trace,
            &vm_relations,
        );
        hash_sum
            + poseidon_sum
            + claim_hash_source_terms(&claim, shape, &claim_input_relations)
            + digest_source_terms(&claim, shape, &verifier_input_relations)
    }

    fn claim_hash_source_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VmPublicClaimInputRelations,
    ) -> QM31 {
        canonical_vm_public_claim_words(claim, shape)
            .expect("fixture claim is canonical")
            .into_iter()
            .enumerate()
            .fold(QM31::zero(), |sum, (index, word)| {
                let denominator: QM31 = relations.claim_word.combine(&[
                    M31::from(VM_CLAIM_HASH_SCOPE),
                    M31::from(u32::try_from(index).expect("fixture word index fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    fn digest_source_terms(
        claim: &PublicData,
        shape: VmPublicClaimShape,
        relations: &VerifierInputRelations,
    ) -> QM31 {
        vm_public_claim_digest(claim, shape)
            .expect("fixture claim is canonical")
            .digest()
            .words()
            .iter()
            .copied()
            .enumerate()
            .fold(QM31::zero(), |sum, (limb, word)| {
                let denominator: QM31 = relations.input_word.combine(&[
                    M31::from(SEGMENT_VERIFIER_ID),
                    M31::from(VerifierInputKind::VmPublicClaimDigest.as_u32()),
                    M31::from(0),
                    M31::from(u32::try_from(limb).expect("digest limb fits u32")),
                    M31::from(word.as_u32()),
                ]);
                sum + denominator.inverse()
            })
    }

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_claim_hash_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, None);
    }

    #[rstest]
    #[should_panic]
    fn the_initial_capacity_domain_cannot_change() {
        assert_constraints(ProofKind::SegmentLeaf, Some(HashTamper::InitialCapacity));
    }

    #[rstest]
    #[should_panic]
    fn canonical_end_marker_cannot_change() {
        assert_constraints(ProofKind::SegmentLeaf, Some(HashTamper::EndMarker));
    }

    #[rstest]
    #[should_panic]
    fn inactive_hash_state_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, Some(HashTamper::InactiveState));
    }

    #[rstest]
    fn complete_claim_hash_relations_cancel() {
        assert!(complete_relation_sum(false).is_zero());
    }

    #[rstest]
    fn a_disconnected_internal_state_does_not_cancel() {
        assert!(!complete_relation_sum(true).is_zero());
    }
}
