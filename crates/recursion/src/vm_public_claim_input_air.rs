//! Fixed AIR boundary for the canonical VM public-claim words.
//!
//! Verifier preprocessing fixes every word coordinate, tag, capacity, and
//! range class. Segment leaves expose the same canonical words to the claim
//! hash, semantic binding, and public-LogUp circuits through separate scopes.
//! The range-checked bytes are exported independently to the public-LogUp
//! circuit, avoiding a second unconstrained decomposition. Other proof modes
//! carry zero values, so the universal recursion AIR keeps one shape without
//! accepting an unused private claim.

use core::fmt;

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

use super::vm_public_claim::{
    VmPublicClaimError, VmPublicClaimShape, VmPublicClaimWordKind,
    canonical_layout as claim_layout, canonical_vm_public_claim_word_kinds,
    canonical_vm_public_claim_words,
};
use super::wire::ProofKind;
use prover::public_data::PublicData;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;
const U16_BYTE_BASE: u32 = 1 << 8;

const ROW_MASK_COLUMN: usize = 0;
const WORD_INDEX_COLUMN: usize = 1;
const CONSTANT_MASK_COLUMN: usize = 2;
const BOOLEAN_MASK_COLUMN: usize = 3;
const U16_MASK_COLUMN: usize = 4;
const CONSTANT_COLUMN: usize = 5;
const INPUT_IO_MASK_COLUMN: usize = 6;
const INPUT_IO_INDEX_COLUMN: usize = 7;
const OUTPUT_IO_MASK_COLUMN: usize = 8;
const OUTPUT_IO_INDEX_COLUMN: usize = 9;
const PREPROCESSED_COLUMN_COUNT: usize = 10;

const PREPROCESSED_COLUMN_IDS: [&str; PREPROCESSED_COLUMN_COUNT] = [
    "recursion_vm_public_claim_input_row_mask",
    "recursion_vm_public_claim_input_word_index",
    "recursion_vm_public_claim_input_constant_mask",
    "recursion_vm_public_claim_input_boolean_mask",
    "recursion_vm_public_claim_input_u16_mask",
    "recursion_vm_public_claim_input_constant",
    "recursion_vm_public_claim_input_input_io_mask",
    "recursion_vm_public_claim_input_input_io_index",
    "recursion_vm_public_claim_input_output_io_mask",
    "recursion_vm_public_claim_input_output_io_index",
];

/// Scope consumed by the VM claim-to-statement semantic circuit.
pub const VM_CLAIM_SEMANTICS_SCOPE: u32 = 0;
/// Scope consumed by the Poseidon2 claim-word hash.
pub const VM_CLAIM_HASH_SCOPE: u32 = 1;
/// Scope consumed by the VM public-LogUp arithmetic circuit.
pub const VM_PUBLIC_LOGUP_SCOPE: u32 = 2;
/// Public-input digest lane in [`VmPublicIoWordRelation`].
pub const VM_PUBLIC_INPUT_KIND: u32 = 0;
/// Public-output digest lane in [`VmPublicIoWordRelation`].
pub const VM_PUBLIC_OUTPUT_KIND: u32 = 1;

define_component_tables! {
    vm_public_claim_input: {
        committed: { value, low_byte, high_byte },
        constraints: {},
    },
}

use prover_columns::VmPublicClaimInputColumns;

// One fixed claim word, separated by its only permitted consumer.
relation!(VmPublicClaimWordRelation, 3);
// One range-checked byte of a fixed u16 claim word: word, byte index, value.
relation!(VmPublicClaimByteRelation, 3);
// One public-IO hash stream word: input/output kind, stream index, and value.
relation!(VmPublicIoWordRelation, 3);

/// Relations that prevent hash and semantic consumers from sharing one entry.
#[derive(Clone)]
pub struct VmPublicClaimInputRelations {
    pub claim_word: VmPublicClaimWordRelation,
    pub claim_byte: VmPublicClaimByteRelation,
    pub io_word: VmPublicIoWordRelation,
}

impl VmPublicClaimInputRelations {
    pub fn dummy() -> Self {
        Self {
            claim_word: VmPublicClaimWordRelation::dummy(),
            claim_byte: VmPublicClaimByteRelation::dummy(),
            io_word: VmPublicIoWordRelation::dummy(),
        }
    }

    pub fn draw(channel: &mut impl Channel) -> Self {
        Self {
            claim_word: VmPublicClaimWordRelation::draw(channel),
            claim_byte: VmPublicClaimByteRelation::draw(channel),
            io_word: VmPublicIoWordRelation::draw(channel),
        }
    }
}

/// Trusted word layout for one verifier-owned claim capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicClaimInputPreprocessed {
    shape: VmPublicClaimShape,
    log_size: u32,
    kinds: Vec<VmPublicClaimWordKind>,
}

impl VmPublicClaimInputPreprocessed {
    pub fn new(shape: VmPublicClaimShape) -> Result<Self, VmPublicClaimInputError> {
        let kinds = canonical_vm_public_claim_word_kinds(shape);
        let padded_rows = kinds
            .len()
            .checked_next_power_of_two()
            .ok_or(VmPublicClaimInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicClaimInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self {
            shape,
            log_size,
            kinds,
        })
    }

    pub const fn shape(&self) -> VmPublicClaimShape {
        self.shape
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn word_count(&self) -> usize {
        self.kinds.len()
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
        for (index, kind) in self.kinds.iter().copied().enumerate() {
            columns[ROW_MASK_COLUMN][index] = 1;
            columns[WORD_INDEX_COLUMN][index] =
                u32::try_from(index).expect("validated claim word index fits u32");
            match kind {
                VmPublicClaimWordKind::Constant(value) => {
                    columns[CONSTANT_MASK_COLUMN][index] = 1;
                    columns[CONSTANT_COLUMN][index] = value.as_u32();
                }
                VmPublicClaimWordKind::Boolean => columns[BOOLEAN_MASK_COLUMN][index] = 1,
                VmPublicClaimWordKind::U16 => columns[U16_MASK_COLUMN][index] = 1,
                VmPublicClaimWordKind::Field => {}
            }
            if let Some(io_index) = input_io_index(self.shape, index) {
                columns[INPUT_IO_MASK_COLUMN][index] = 1;
                columns[INPUT_IO_INDEX_COLUMN][index] = io_index;
            }
            if let Some(io_index) = output_io_index(self.shape, index) {
                columns[OUTPUT_IO_MASK_COLUMN][index] = 1;
                columns[OUTPUT_IO_INDEX_COLUMN][index] = io_index;
            }
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

pub type Component = FrameworkComponent<Eval>;

#[derive(Clone)]
pub struct Eval {
    pub log_size: u32,
    pub proof_kind: ProofKind,
    pub claim_relations: VmPublicClaimInputRelations,
    pub vm_relations: Relations,
}

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let cols = VmPublicClaimInputColumns::from_eval(&mut eval);
        let ids = VmPublicClaimInputPreprocessed::column_ids();
        let row_mask = eval.get_preprocessed_column(ids[ROW_MASK_COLUMN].clone());
        let word_index = eval.get_preprocessed_column(ids[WORD_INDEX_COLUMN].clone());
        let constant_mask = eval.get_preprocessed_column(ids[CONSTANT_MASK_COLUMN].clone());
        let boolean_mask = eval.get_preprocessed_column(ids[BOOLEAN_MASK_COLUMN].clone());
        let u16_mask = eval.get_preprocessed_column(ids[U16_MASK_COLUMN].clone());
        let constant = eval.get_preprocessed_column(ids[CONSTANT_COLUMN].clone());
        let input_io_mask = eval.get_preprocessed_column(ids[INPUT_IO_MASK_COLUMN].clone());
        let input_io_index = eval.get_preprocessed_column(ids[INPUT_IO_INDEX_COLUMN].clone());
        let output_io_mask = eval.get_preprocessed_column(ids[OUTPUT_IO_MASK_COLUMN].clone());
        let output_io_index = eval.get_preprocessed_column(ids[OUTPUT_IO_INDEX_COLUMN].clone());
        eval.add_constraint(cols.enabler.clone() - row_mask.clone());

        let segment = E::F::from(BaseField::from(u32::from(
            self.proof_kind == ProofKind::SegmentLeaf,
        )));
        let one = E::F::from(BaseField::from(1));
        let active = row_mask * segment;
        let active_u16 = active.clone() * u16_mask;
        eval.add_constraint((one.clone() - active.clone()) * cols.value.clone());
        eval.add_constraint(active.clone() * constant_mask * (cols.value.clone() - constant));
        eval.add_constraint(
            active.clone() * boolean_mask * cols.value.clone() * (one.clone() - cols.value.clone()),
        );
        eval.add_constraint(
            active_u16.clone()
                * (cols.value.clone()
                    - cols.low_byte.clone()
                    - cols.high_byte.clone() * BaseField::from(U16_BYTE_BASE)),
        );
        eval.add_constraint((one.clone() - active_u16.clone()) * cols.low_byte.clone());
        eval.add_constraint((one - active_u16.clone()) * cols.high_byte.clone());

        for scope in [
            VM_CLAIM_SEMANTICS_SCOPE,
            VM_CLAIM_HASH_SCOPE,
            VM_PUBLIC_LOGUP_SCOPE,
        ] {
            eval.add_to_relation(RelationEntry::new(
                &self.claim_relations.claim_word,
                E::EF::from(active.clone()),
                &[
                    E::F::from(BaseField::from(scope)),
                    word_index.clone(),
                    cols.value.clone(),
                ],
            ));
        }
        eval.add_to_relation(RelationEntry::new(
            &self.claim_relations.io_word,
            E::EF::from(active.clone() * input_io_mask),
            &[
                E::F::from(BaseField::from(VM_PUBLIC_INPUT_KIND)),
                input_io_index,
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.claim_relations.io_word,
            E::EF::from(active.clone() * output_io_mask),
            &[
                E::F::from(BaseField::from(VM_PUBLIC_OUTPUT_KIND)),
                output_io_index,
                cols.value.clone(),
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.vm_relations.range_check_8_8,
            -E::EF::from(active_u16.clone()),
            &[cols.low_byte.clone(), cols.high_byte.clone()],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.claim_relations.claim_byte,
            E::EF::from(active_u16.clone()),
            &[
                word_index.clone(),
                E::F::from(BaseField::from(0)),
                cols.low_byte,
            ],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.claim_relations.claim_byte,
            E::EF::from(active_u16),
            &[word_index, E::F::from(BaseField::from(1)), cols.high_byte],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}

/// Generates scoped claim words, public bytes, IO words, and range consumers.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    claim_relations: &VmPublicClaimInputRelations,
    vm_relations: &Relations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    let cols = VmPublicClaimInputColumns::from_iter(
        trace.iter().map(|evaluation| &evaluation.values.data),
    );
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
    let active_u16 = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[U16_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let negative_u16 = active_u16.iter().map(|value| -*value).collect::<Vec<_>>();
    let input_io_active = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[INPUT_IO_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let output_io_active = (0..simd_size)
        .map(|row| active[row] * PackedQM31::from(pp[OUTPUT_IO_MASK_COLUMN][row]))
        .collect::<Vec<_>>();
    let semantics_scope =
        vec![PackedM31::broadcast(BaseField::from(VM_CLAIM_SEMANTICS_SCOPE)); simd_size];
    let hash_scope = vec![PackedM31::broadcast(BaseField::from(VM_CLAIM_HASH_SCOPE)); simd_size];
    let public_logup_scope =
        vec![PackedM31::broadcast(BaseField::from(VM_PUBLIC_LOGUP_SCOPE)); simd_size];
    let semantics_denom = combine!(
        claim_relations.claim_word,
        [semantics_scope, pp[WORD_INDEX_COLUMN], cols.value]
    );
    let hash_denom = combine!(
        claim_relations.claim_word,
        [hash_scope, pp[WORD_INDEX_COLUMN], cols.value]
    );
    let public_logup_denom = combine!(
        claim_relations.claim_word,
        [public_logup_scope, pp[WORD_INDEX_COLUMN], cols.value]
    );
    let range_denom = combine!(
        vm_relations.range_check_8_8,
        [cols.low_byte, cols.high_byte]
    );
    let input_kind = vec![PackedM31::broadcast(BaseField::from(VM_PUBLIC_INPUT_KIND)); simd_size];
    let output_kind = vec![PackedM31::broadcast(BaseField::from(VM_PUBLIC_OUTPUT_KIND)); simd_size];
    let input_io_denom = combine!(
        claim_relations.io_word,
        [input_kind, pp[INPUT_IO_INDEX_COLUMN], cols.value]
    );
    let output_io_denom = combine!(
        claim_relations.io_word,
        [output_kind, pp[OUTPUT_IO_INDEX_COLUMN], cols.value]
    );
    let low_byte_index = vec![PackedM31::broadcast(BaseField::from(0)); simd_size];
    let high_byte_index = vec![PackedM31::broadcast(BaseField::from(1)); simd_size];
    let low_byte_denom = combine!(
        claim_relations.claim_byte,
        [pp[WORD_INDEX_COLUMN], low_byte_index, cols.low_byte]
    );
    let high_byte_denom = combine!(
        claim_relations.claim_byte,
        [pp[WORD_INDEX_COLUMN], high_byte_index, cols.high_byte]
    );

    let mut logup_gen = LogupTraceGenerator::new(log_size);
    write_pair!(&active, &semantics_denom, &active, &hash_denom, logup_gen);
    write_pair!(
        &active,
        &public_logup_denom,
        &input_io_active,
        &input_io_denom,
        logup_gen
    );
    write_pair!(
        &output_io_active,
        &output_io_denom,
        &negative_u16,
        &range_denom,
        logup_gen
    );
    write_pair!(
        &active_u16,
        &low_byte_denom,
        &active_u16,
        &high_byte_denom,
        logup_gen
    );
    logup_gen.finalize_last()
}

fn input_io_index(shape: VmPublicClaimShape, claim_index: usize) -> Option<u32> {
    let mapped = if (claim_layout::INPUT_START_START..claim_layout::INPUT_START_START + 4)
        .contains(&claim_index)
    {
        3 + claim_index - claim_layout::INPUT_START_START
    } else if (claim_layout::INPUT_WORD_COUNT_START..claim_layout::INPUT_WORD_COUNT_START + 2)
        .contains(&claim_index)
    {
        7 + claim_index - claim_layout::INPUT_WORD_COUNT_START
    } else if (claim_layout::INPUT_SLOTS_START
        ..claim_layout::INPUT_SLOTS_START + shape.max_input_words() as usize * 3)
        .contains(&claim_index)
    {
        9 + claim_index - claim_layout::INPUT_SLOTS_START
    } else {
        return None;
    };
    Some(u32::try_from(mapped).expect("validated input IO stream index fits u32"))
}

fn output_io_index(shape: VmPublicClaimShape, claim_index: usize) -> Option<u32> {
    let output_count_start = claim_layout::output_word_count_start(shape);
    let output_slots_start = claim_layout::output_slots_start(shape);
    let mapped = if (claim_layout::OUTPUT_LENGTH_ADDRESS_START
        ..claim_layout::OUTPUT_LENGTH_ADDRESS_START + 6)
        .contains(&claim_index)
    {
        3 + claim_index - claim_layout::OUTPUT_LENGTH_ADDRESS_START
    } else if (output_count_start..output_count_start + 2).contains(&claim_index) {
        9 + claim_index - output_count_start
    } else {
        let slot_offset = claim_index.checked_sub(output_slots_start)?;
        let slot = slot_offset / 7;
        let within_slot = slot_offset % 7;
        if slot >= shape.max_output_words() as usize || within_slot >= 5 {
            return None;
        }
        11 + slot * 5 + within_slot
    };
    Some(u32::try_from(mapped).expect("validated output IO stream index fits u32"))
}

/// Registers claim limb consumers in the shared byte-range table.
pub fn register_range_check_multiplicities(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    counters: &mut prover::relations::Counters,
) {
    let cols = VmPublicClaimInputColumns::from_iter(
        trace.iter().map(|evaluation| &evaluation.values.data),
    );
    let pp = preprocessed
        .iter()
        .map(|column| &column.values.data)
        .collect::<Vec<_>>();
    let segment = BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf));
    let multiplicities = (0..cols.enabler.len())
        .map(|row| -(pp[ROW_MASK_COLUMN][row] * pp[U16_MASK_COLUMN][row] * segment))
        .collect::<Vec<_>>();
    counters.range_check_8_8.register_many(
        &multiplicities,
        &[cols.low_byte.as_slice(), cols.high_byte.as_slice()],
    );
}

/// Pushes the exact fixed claim words, or zeros for non-segment modes.
pub fn push_vm_public_claim_inputs(
    table: &mut VmPublicClaimInputTable,
    preprocessed: &VmPublicClaimInputPreprocessed,
    proof_kind: ProofKind,
    public_data: Option<&PublicData>,
) -> Result<(), VmPublicClaimInputError> {
    let active = proof_kind == ProofKind::SegmentLeaf;
    let words = match (active, public_data) {
        (true, Some(public_data)) => {
            canonical_vm_public_claim_words(public_data, preprocessed.shape)
                .map_err(VmPublicClaimInputError::Claim)?
        }
        (true, None) => return Err(VmPublicClaimInputError::SegmentClaimMissing),
        (false, Some(_)) => return Err(VmPublicClaimInputError::InactiveClaimProvided),
        (false, None) => vec![air::digest::M31Word::ZERO; preprocessed.word_count()],
    };
    if words.len() != preprocessed.word_count() {
        return Err(VmPublicClaimInputError::WordCountMismatch {
            expected: preprocessed.word_count(),
            actual: words.len(),
        });
    }
    for (kind, word) in preprocessed.kinds.iter().zip(words) {
        if let VmPublicClaimWordKind::Constant(expected) = kind {
            if active && *expected != word {
                return Err(VmPublicClaimInputError::ConstantMismatch);
            }
        }
        let (low_byte, high_byte) = if active && *kind == VmPublicClaimWordKind::U16 {
            let value = u16::try_from(word.as_u32()).map_err(|_| {
                VmPublicClaimInputError::IntegerWordOutOfRange {
                    value: word.as_u32(),
                }
            })?;
            let [low, high] = value.to_le_bytes();
            (u32::from(low), u32::from(high))
        } else {
            (0, 0)
        };
        table.push(word.as_u32(), low_byte, high_byte);
    }
    Ok(())
}

/// Invalid trusted layout or claim witness at the AIR boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimInputError {
    Claim(VmPublicClaimError),
    RowCountOverflow,
    LogSizeOutOfRange { log_size: u32 },
    SegmentClaimMissing,
    InactiveClaimProvided,
    WordCountMismatch { expected: usize, actual: usize },
    ConstantMismatch,
    IntegerWordOutOfRange { value: u32 },
}

impl fmt::Display for VmPublicClaimInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Claim(error) => write!(formatter, "invalid VM public claim: {error}"),
            Self::RowCountOverflow => write!(formatter, "VM public-claim row count overflowed"),
            Self::LogSizeOutOfRange { log_size } => write!(
                formatter,
                "VM public-claim input log size {log_size} exceeds {MAX_LOG_SIZE}"
            ),
            Self::SegmentClaimMissing => write!(formatter, "segment leaf has no VM public claim"),
            Self::InactiveClaimProvided => {
                write!(formatter, "non-segment proof carries a VM public claim")
            }
            Self::WordCountMismatch { expected, actual } => write!(
                formatter,
                "VM public claim has {actual} words, expected {expected}"
            ),
            Self::ConstantMismatch => write!(formatter, "VM public-claim constant changed"),
            Self::IntegerWordOutOfRange { value } => {
                write!(formatter, "VM public-claim limb {value} exceeds u16")
            }
        }
    }
}

impl std::error::Error for VmPublicClaimInputError {}

#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use rstest::rstest;
    use stwo::core::fields::m31::M31;
    use stwo::core::pcs::TreeVec;
    use stwo::prover::backend::Column;
    use stwo_constraint_framework::assert_constraints_on_polys;

    use super::*;
    use crate::vm_public_claim::tests::{public_data, shape};

    fn assert_constraints(kind: ProofKind, tamper: Option<(usize, u32)>) {
        let preprocessing =
            VmPublicClaimInputPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let witness = (kind == ProofKind::SegmentLeaf).then_some(&claim);
        let mut table = VmPublicClaimInputTable::new();
        push_vm_public_claim_inputs(&mut table, &preprocessing, kind, witness)
            .expect("fixture claim input materializes");
        if let Some((row, value)) = tamper {
            table.value[row] = value;
        }
        let claim_relations = VmPublicClaimInputRelations::dummy();
        let vm_relations = Relations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) =
            gen_interaction_trace(&trace, &preprocessed, kind, &claim_relations, &vm_relations);
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = Eval {
            log_size: preprocessing.log_size(),
            proof_kind: kind,
            claim_relations,
            vm_relations,
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

    #[rstest]
    #[case::segment(ProofKind::SegmentLeaf)]
    #[case::binary(ProofKind::BinaryNode)]
    #[case::empty(ProofKind::EmptyLeaf)]
    fn every_universal_mode_satisfies_claim_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, None);
    }

    #[rstest]
    #[should_panic]
    fn a_fixed_claim_tag_cannot_change() {
        assert_constraints(ProofKind::SegmentLeaf, Some((0, 2)));
    }

    #[rstest]
    #[should_panic]
    fn a_presence_flag_must_be_boolean() {
        let row = super::super::vm_public_claim::canonical_layout::PROGRAM_ROOT_PRESENT;
        assert_constraints(ProofKind::SegmentLeaf, Some((row, 2)));
    }

    #[rstest]
    #[should_panic]
    fn an_inactive_claim_word_must_be_zero() {
        assert_constraints(ProofKind::BinaryNode, Some((0, 1)));
    }

    #[rstest]
    fn non_segment_witness_rejects_private_claim_data() {
        let preprocessing =
            VmPublicClaimInputPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let result = push_vm_public_claim_inputs(
            &mut VmPublicClaimInputTable::new(),
            &preprocessing,
            ProofKind::EmptyLeaf,
            Some(&claim),
        );
        assert_eq!(result, Err(VmPublicClaimInputError::InactiveClaimProvided));
    }

    #[rstest]
    fn every_u16_claim_word_registers_one_range_lookup() {
        let preprocessing =
            VmPublicClaimInputPreprocessed::new(shape()).expect("fixture shape is supported");
        let claim = public_data();
        let mut table = VmPublicClaimInputTable::new();
        push_vm_public_claim_inputs(
            &mut table,
            &preprocessing,
            ProofKind::SegmentLeaf,
            Some(&claim),
        )
        .expect("fixture claim input materializes");
        let trace = table.into_witness();
        let preprocessed = preprocessing.gen_columns();
        let mut counters = prover::relations::Counters::new();
        register_range_check_multiplicities(
            &trace,
            &preprocessed,
            ProofKind::SegmentLeaf,
            &mut counters,
        );
        let registered = counters.range_check_8_8.into_trace()[0]
            .values
            .to_cpu()
            .into_iter()
            .fold(M31::zero(), |sum, value| sum + value);
        let expected = preprocessing
            .kinds
            .iter()
            .filter(|kind| **kind == VmPublicClaimWordKind::U16)
            .count();
        assert_eq!(
            registered,
            -M31::from(u32::try_from(expected).expect("fixture range count fits u32"))
        );
    }
}
