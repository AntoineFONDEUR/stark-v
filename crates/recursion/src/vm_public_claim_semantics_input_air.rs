//! AIR ownership for VM claim-to-statement arithmetic circuit inputs.
//!
//! Claim and statement inputs consume their separately scoped transcript-bound
//! words only in segment mode. Private decomposition bits are zero outside that
//! mode, the public selector equals the proof kind, and every input emits its
//! exact circuit-wire use count under verifier-owned preprocessing.

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

use crate::circuit::use_counts_for_outputs;
use crate::relations::RecursionRelations;

use super::statement_input_air::{StatementInputRelations, VM_CLAIM_STATEMENT_SCOPE};
use super::vm_public_claim_input_air::{VM_CLAIM_SEMANTICS_SCOPE, VmPublicClaimInputRelations};
use super::vm_public_claim_semantics_circuit::{
    VmClaimCircuitInputSource, VmPublicClaimSemanticsCircuit,
};
use super::vm_public_io_hash_air::VmPublicIoHashRelations;
use super::wire::ProofKind;

const MIN_LOG_SIZE: u32 = 4;
const MAX_LOG_SIZE: u32 = 30;

const ROW_MASK_COLUMN: usize = 0;
const CLAIM_MASK_COLUMN: usize = 1;
const STATEMENT_MASK_COLUMN: usize = 2;
const SELECTOR_MASK_COLUMN: usize = 3;
const PRIVATE_MASK_COLUMN: usize = 4;
const IO_DIGEST_MASK_COLUMN: usize = 5;
const IO_KIND_COLUMN: usize = 6;
const CIRCUIT_ID_COLUMN: usize = 7;
const NODE_ID_COLUMN: usize = 8;
const USE_COUNT_COLUMN: usize = 9;
const WORD_INDEX_COLUMN: usize = 10;
const PREPROCESSED_COLUMN_COUNT: usize = 11;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum InputSource {
    Claim,
    Statement,
    Selector,
    Private,
    IoDigest,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PreprocessedRow {
    source: InputSource,
    circuit_id: u32,
    node_id: u32,
    use_count: u32,
    word_index: u32,
    io_kind: u32,
}

/// Trusted input-node ownership for one fixed semantic circuit id.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VmPublicClaimSemanticsInputPreprocessed {
    log_size: u32,
    rows: Vec<PreprocessedRow>,
}

impl VmPublicClaimSemanticsInputPreprocessed {
    pub fn new(
        reference: &VmPublicClaimSemanticsCircuit,
        circuit_id: u32,
    ) -> Result<Self, VmPublicClaimSemanticsInputError> {
        M31Word::try_from(circuit_id)
            .map_err(|_| VmPublicClaimSemanticsInputError::CircuitIdNotCanonical { circuit_id })?;
        let arena = reference.circuit().arena();
        let uses = use_counts_for_outputs(&arena, reference.circuit().outputs());
        let mut rows = Vec::with_capacity(reference.input_bindings().len());
        for binding in reference.input_bindings() {
            let node_id = usize::try_from(binding.node_id).map_err(|_| {
                VmPublicClaimSemanticsInputError::NodeIdDoesNotFitUsize {
                    node_id: binding.node_id,
                }
            })?;
            let use_count =
                *uses
                    .get(node_id)
                    .ok_or(VmPublicClaimSemanticsInputError::NodeMissing {
                        node_id: binding.node_id,
                    })?;
            M31Word::try_from(use_count).map_err(|_| {
                VmPublicClaimSemanticsInputError::UseCountNotCanonical {
                    node_id: binding.node_id,
                    use_count,
                }
            })?;
            let (source, word_index, io_kind) = match binding.source {
                VmClaimCircuitInputSource::ClaimWord { index } => (InputSource::Claim, index, 0),
                VmClaimCircuitInputSource::StatementWord { index } => {
                    (InputSource::Statement, index, 0)
                }
                VmClaimCircuitInputSource::IoDigestWord { io_kind, limb } => {
                    if io_kind > 1 {
                        return Err(VmPublicClaimSemanticsInputError::UnknownIoKind { io_kind });
                    }
                    if limb >= 8 {
                        return Err(VmPublicClaimSemanticsInputError::IoDigestLimbOutOfRange {
                            limb,
                        });
                    }
                    (InputSource::IoDigest, limb, io_kind)
                }
                VmClaimCircuitInputSource::SegmentSelector => (InputSource::Selector, 0, 0),
                VmClaimCircuitInputSource::PrivateWitness => (InputSource::Private, 0, 0),
            };
            rows.push(PreprocessedRow {
                source,
                circuit_id,
                node_id: binding.node_id,
                use_count,
                word_index,
                io_kind,
            });
        }
        drop(arena);
        let padded_rows = rows
            .len()
            .checked_next_power_of_two()
            .ok_or(VmPublicClaimSemanticsInputError::RowCountOverflow)?
            .max(1 << MIN_LOG_SIZE);
        let log_size = padded_rows.ilog2();
        if log_size > MAX_LOG_SIZE {
            return Err(VmPublicClaimSemanticsInputError::LogSizeOutOfRange { log_size });
        }
        Ok(Self { log_size, rows })
    }

    pub const fn log_size(&self) -> u32 {
        self.log_size
    }

    pub fn input_count(&self) -> usize {
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
            columns[CLAIM_MASK_COLUMN][index] = u32::from(row.source == InputSource::Claim);
            columns[STATEMENT_MASK_COLUMN][index] = u32::from(row.source == InputSource::Statement);
            columns[SELECTOR_MASK_COLUMN][index] = u32::from(row.source == InputSource::Selector);
            columns[PRIVATE_MASK_COLUMN][index] = u32::from(row.source == InputSource::Private);
            columns[IO_DIGEST_MASK_COLUMN][index] = u32::from(row.source == InputSource::IoDigest);
            columns[IO_KIND_COLUMN][index] = row.io_kind;
            columns[CIRCUIT_ID_COLUMN][index] = row.circuit_id;
            columns[NODE_ID_COLUMN][index] = row.node_id;
            columns[USE_COUNT_COLUMN][index] = row.use_count;
            columns[WORD_INDEX_COLUMN][index] = row.word_index;
        }
        let domain = CanonicCoset::new(self.log_size).circle_domain();
        columns
            .into_iter()
            .map(|column| CircleEvaluation::new(domain, BaseColumn::from(column)))
            .collect()
    }
}

/// Relations used by the macro-generated semantic-circuit input component.
#[derive(Clone)]
pub struct VmPublicClaimSemanticsInputComponentRelations {
    pub claim_word: super::vm_public_claim_input_air::VmPublicClaimWordRelation,
    pub statement_word: super::statement_input_air::StatementWordRelation,
    pub digest: super::vm_public_io_hash_air::VmPublicIoDigestRelation,
    pub wire: crate::relations::WireRelation,
}

impl VmPublicClaimSemanticsInputComponentRelations {
    /// Combine each input owner with the shared arithmetic wire relation.
    pub fn new(
        claim_relations: &VmPublicClaimInputRelations,
        statement_relations: &StatementInputRelations,
        circuit_relations: &RecursionRelations,
        io_hash_relations: &VmPublicIoHashRelations,
    ) -> Self {
        Self {
            claim_word: claim_relations.claim_word.clone(),
            statement_word: statement_relations.statement_word.clone(),
            digest: io_hash_relations.digest.clone(),
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
        crate::vm_public_claim_semantics_input_air::VmPublicClaimSemanticsInputComponentRelations,
    logup_batch: 2,
    embedded_preprocessed: {
        row_mask: "recursion_vm_claim_semantics_input_row_mask",
        claim_mask: "recursion_vm_claim_semantics_input_claim_mask",
        statement_mask: "recursion_vm_claim_semantics_input_statement_mask",
        selector_mask: "recursion_vm_claim_semantics_input_selector_mask",
        private_mask: "recursion_vm_claim_semantics_input_private_mask",
        io_digest_mask: "recursion_vm_claim_semantics_input_io_digest_mask",
        io_kind: "recursion_vm_claim_semantics_input_io_kind",
        circuit_id: "recursion_vm_claim_semantics_input_circuit_id",
        node_id: "recursion_vm_claim_semantics_input_node_id",
        use_count: "recursion_vm_claim_semantics_input_use_count",
        word_index: "recursion_vm_claim_semantics_input_word_index",
    },
    embedded_params: [segment_active, claim_scope, statement_scope],

    relation claim_word(3);
    relation statement_word(3);
    relation digest(3);
    relation wire(6);

    fn vm_public_claim_semantics_input(
        value,
        row_mask, claim_mask, statement_mask, selector_mask, private_mask,
        io_digest_mask, io_kind, circuit_id, node_id, use_count, word_index,
        segment_active, claim_scope, statement_scope,
    ) {
        let witness_mask = claim_mask + statement_mask + private_mask + io_digest_mask;

        constrain enabler - row_mask;
        constrain witness_mask * (1 - segment_active) * value;
        constrain selector_mask * (value - segment_active);

        consume(segment_active * claim_mask) claim_word(claim_scope, word_index, value);
        consume(segment_active * statement_mask) statement_word(
            statement_scope, word_index, value,
        );
        consume(segment_active * io_digest_mask) digest(io_kind, word_index, value);
        emit(row_mask * use_count) wire(circuit_id, node_id, value, 0, 0, 0);

        return value;
    }
}

pub use component::air::{Component, Eval};

/// Construct the generated evaluator for the selected universal proof kind.
pub fn eval_for_proof_kind(
    log_size: u32,
    proof_kind: ProofKind,
    claim_relations: &VmPublicClaimInputRelations,
    statement_relations: &StatementInputRelations,
    circuit_relations: &RecursionRelations,
    io_hash_relations: &VmPublicIoHashRelations,
) -> Eval {
    Eval {
        log_size,
        segment_active: BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        claim_scope: BaseField::from(VM_CLAIM_SEMANTICS_SCOPE),
        statement_scope: BaseField::from(VM_CLAIM_STATEMENT_SCOPE),
        relations: VmPublicClaimSemanticsInputComponentRelations::new(
            claim_relations,
            statement_relations,
            circuit_relations,
            io_hash_relations,
        ),
    }
}

/// Generate claim, statement, digest, and circuit-wire interaction fractions.
pub fn gen_interaction_trace(
    trace: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    preprocessed: &[CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>],
    proof_kind: ProofKind,
    claim_relations: &VmPublicClaimInputRelations,
    statement_relations: &StatementInputRelations,
    circuit_relations: &RecursionRelations,
    io_hash_relations: &VmPublicIoHashRelations,
) -> (
    ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>,
    QM31,
) {
    component::witness::gen_interaction_trace(
        trace,
        preprocessed,
        BaseField::from(u32::from(proof_kind == ProofKind::SegmentLeaf)),
        BaseField::from(VM_CLAIM_SEMANTICS_SCOPE),
        BaseField::from(VM_CLAIM_STATEMENT_SCOPE),
        &VmPublicClaimSemanticsInputComponentRelations::new(
            claim_relations,
            statement_relations,
            circuit_relations,
            io_hash_relations,
        ),
    )
}

/// Materializes input-node values after verifying the reference structure.
pub fn push_vm_public_claim_semantics_inputs(
    table: &mut VmPublicClaimSemanticsInputTable,
    preprocessed: &VmPublicClaimSemanticsInputPreprocessed,
    reference: &VmPublicClaimSemanticsCircuit,
    witness: &VmPublicClaimSemanticsCircuit,
    proof_kind: ProofKind,
) -> Result<(), VmPublicClaimSemanticsInputError> {
    if reference.input_bindings() != witness.input_bindings() {
        return Err(VmPublicClaimSemanticsInputError::InputLayoutMismatch);
    }
    if reference.input_bindings().len() != preprocessed.rows.len() {
        return Err(VmPublicClaimSemanticsInputError::InputCountMismatch {
            expected: preprocessed.rows.len(),
            actual: reference.input_bindings().len(),
        });
    }
    let arena = witness.circuit().arena();
    for (row, binding) in preprocessed.rows.iter().zip(witness.input_bindings()) {
        if row.node_id != binding.node_id
            || row.source != source_kind(binding.source)
            || row.word_index != source_index(binding.source)
            || row.io_kind != source_io_kind(binding.source)
        {
            return Err(VmPublicClaimSemanticsInputError::InputCoordinateMismatch {
                node_id: binding.node_id,
            });
        }
        let node_id = usize::try_from(binding.node_id).map_err(|_| {
            VmPublicClaimSemanticsInputError::NodeIdDoesNotFitUsize {
                node_id: binding.node_id,
            }
        })?;
        let value = arena
            .nodes
            .get(node_id)
            .ok_or(VmPublicClaimSemanticsInputError::NodeMissing {
                node_id: binding.node_id,
            })?
            .value
            .to_m31_array();
        if value[1..].iter().any(|limb| limb.0 != 0) {
            return Err(VmPublicClaimSemanticsInputError::InputIsNotBaseField {
                node_id: binding.node_id,
            });
        }
        let active = proof_kind == ProofKind::SegmentLeaf;
        let expected = match binding.source {
            VmClaimCircuitInputSource::SegmentSelector => u32::from(active),
            VmClaimCircuitInputSource::ClaimWord { .. }
            | VmClaimCircuitInputSource::StatementWord { .. }
            | VmClaimCircuitInputSource::IoDigestWord { .. }
            | VmClaimCircuitInputSource::PrivateWitness => {
                if active {
                    value[0].0
                } else {
                    0
                }
            }
        };
        if value[0].0 != expected {
            return Err(VmPublicClaimSemanticsInputError::InactiveInputIsNonZero {
                node_id: binding.node_id,
            });
        }
        table.push(expected);
    }
    Ok(())
}

const fn source_kind(source: VmClaimCircuitInputSource) -> InputSource {
    match source {
        VmClaimCircuitInputSource::ClaimWord { .. } => InputSource::Claim,
        VmClaimCircuitInputSource::StatementWord { .. } => InputSource::Statement,
        VmClaimCircuitInputSource::SegmentSelector => InputSource::Selector,
        VmClaimCircuitInputSource::PrivateWitness => InputSource::Private,
        VmClaimCircuitInputSource::IoDigestWord { .. } => InputSource::IoDigest,
    }
}

const fn source_index(source: VmClaimCircuitInputSource) -> u32 {
    match source {
        VmClaimCircuitInputSource::ClaimWord { index }
        | VmClaimCircuitInputSource::StatementWord { index } => index,
        VmClaimCircuitInputSource::IoDigestWord { limb, .. } => limb,
        VmClaimCircuitInputSource::SegmentSelector | VmClaimCircuitInputSource::PrivateWitness => 0,
    }
}

const fn source_io_kind(source: VmClaimCircuitInputSource) -> u32 {
    match source {
        VmClaimCircuitInputSource::IoDigestWord { io_kind, .. } => io_kind,
        VmClaimCircuitInputSource::ClaimWord { .. }
        | VmClaimCircuitInputSource::StatementWord { .. }
        | VmClaimCircuitInputSource::SegmentSelector
        | VmClaimCircuitInputSource::PrivateWitness => 0,
    }
}

/// Invalid fixed input layout or witness value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimSemanticsInputError {
    CircuitIdNotCanonical { circuit_id: u32 },
    RowCountOverflow,
    LogSizeOutOfRange { log_size: u32 },
    NodeIdDoesNotFitUsize { node_id: u32 },
    NodeMissing { node_id: u32 },
    UseCountNotCanonical { node_id: u32, use_count: u32 },
    InputCountMismatch { expected: usize, actual: usize },
    InputLayoutMismatch,
    InputCoordinateMismatch { node_id: u32 },
    InputIsNotBaseField { node_id: u32 },
    InactiveInputIsNonZero { node_id: u32 },
    UnknownIoKind { io_kind: u32 },
    IoDigestLimbOutOfRange { limb: u32 },
}

impl fmt::Display for VmPublicClaimSemanticsInputError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmPublicClaimSemanticsInputError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    use super::*;
    use crate::statement::SPAN_STATEMENT_CANONICAL_WORDS;
    use crate::statement_semantics_circuit::StatementWords;
    use crate::vm_public_claim::tests::shape;
    use crate::vm_public_claim_semantics_circuit::tests::{valid_digests, valid_words};
    use crate::vm_public_claim_semantics_circuit::{
        VmPublicClaimSemanticsWitness, build_vm_public_claim_semantics_circuit,
    };

    fn circuits(kind: ProofKind) -> (VmPublicClaimSemanticsCircuit, VmPublicClaimSemanticsCircuit) {
        let shape = shape();
        let (claim, statement) = valid_words();
        let zero_claim = vec![M31Word::ZERO; claim.len()];
        let zero_statement: StatementWords = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
        let zero_digest = [M31Word::ZERO; 8];
        let (input_digest, output_digest) = valid_digests();
        let reference = build_vm_public_claim_semantics_circuit(
            shape,
            VmPublicClaimSemanticsWitness {
                segment_selector: false,
                claim_words: &zero_claim,
                statement_words: &zero_statement,
                input_digest: &zero_digest,
                output_digest: &zero_digest,
            },
        )
        .expect("fixture reference widths are fixed");
        let active = kind == ProofKind::SegmentLeaf;
        let witness = build_vm_public_claim_semantics_circuit(
            shape,
            VmPublicClaimSemanticsWitness {
                segment_selector: active,
                claim_words: if active { &claim } else { &zero_claim },
                statement_words: if active { &statement } else { &zero_statement },
                input_digest: if active { &input_digest } else { &zero_digest },
                output_digest: if active { &output_digest } else { &zero_digest },
            },
        )
        .expect("fixture witness widths are fixed");
        (reference, witness)
    }

    fn assert_constraints(kind: ProofKind, tamper: bool) {
        let (reference, witness) = circuits(kind);
        let preprocessing = VmPublicClaimSemanticsInputPreprocessed::new(&reference, 17)
            .expect("fixture circuit input layout is canonical");
        let mut table = VmPublicClaimSemanticsInputTable::new();
        push_vm_public_claim_semantics_inputs(
            &mut table,
            &preprocessing,
            &reference,
            &witness,
            kind,
        )
        .expect("fixture semantic inputs materialize");
        if tamper {
            table.value[1] += 1;
        }
        let claim_relations = VmPublicClaimInputRelations::dummy();
        let statement_relations = StatementInputRelations::dummy();
        let circuit_relations = RecursionRelations::dummy();
        let io_hash_relations = VmPublicIoHashRelations::dummy();
        let preprocessed = preprocessing.gen_columns();
        let trace = table.into_witness();
        let (interaction, claimed_sum) = gen_interaction_trace(
            &trace,
            &preprocessed,
            kind,
            &claim_relations,
            &statement_relations,
            &circuit_relations,
            &io_hash_relations,
        );
        let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
        let trace_polys = traces.map_cols(|column| column.interpolate());
        let eval = eval_for_proof_kind(
            preprocessing.log_size(),
            kind,
            &claim_relations,
            &statement_relations,
            &circuit_relations,
            &io_hash_relations,
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
    fn every_universal_mode_satisfies_semantic_input_constraints(#[case] kind: ProofKind) {
        assert_constraints(kind, false);
    }

    #[rstest]
    #[should_panic]
    fn inactive_semantic_input_must_be_zero() {
        assert_constraints(ProofKind::EmptyLeaf, true);
    }

    #[rstest]
    fn preprocessing_owns_every_circuit_input_once() {
        let (reference, _) = circuits(ProofKind::SegmentLeaf);
        let preprocessing = VmPublicClaimSemanticsInputPreprocessed::new(&reference, 17)
            .expect("fixture circuit input layout is canonical");
        assert_eq!(
            preprocessing.input_count(),
            reference.input_bindings().len()
        );
    }
}
