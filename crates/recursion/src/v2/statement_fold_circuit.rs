//! Exact binary statement fold compiled into the recursion arithmetic circuit.
//!
//! Child statement words are range-bound before entering this circuit. The
//! circuit enforces the complete [`SpanStatement::fold`] transformation over
//! canonical 16-bit limbs: common job identity, binary slot geometry, body
//! case selection, integer additions without overflow, execution continuity,
//! and edge ownership. Every equation remains a distinct zero output so one
//! failing invariant cannot cancel another.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;

use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

use super::protocol::{CanonicalTag, CanonicalWords};
use super::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement, canonical_layout as layout};
use super::statement_input_air::{
    LEFT_STATEMENT_SCOPE, PARENT_STATEMENT_SCOPE, RIGHT_STATEMENT_SCOPE,
};

const U16_BASE: u32 = 1 << 16;

pub type StatementWords = [M31Word; SPAN_STATEMENT_CANONICAL_WORDS];

/// Source of one input node in the fixed fold circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldCircuitInputSource {
    StatementWord { scope: u32, index: u32 },
    BinarySelector,
    PrivateWitness,
}

/// Node binding needed to connect circuit inputs to AIR relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FoldCircuitInputBinding {
    pub node_id: u32,
    pub source: FoldCircuitInputSource,
}

/// Fixed circuit plus the ownership of every input node.
#[derive(Debug)]
pub struct StatementFoldCircuit {
    circuit: ConstraintCircuit,
    input_bindings: Vec<FoldCircuitInputBinding>,
}

impl StatementFoldCircuit {
    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[FoldCircuitInputBinding] {
        &self.input_bindings
    }

    pub fn nonzero_output_count(&self) -> usize {
        let arena = self.circuit.arena();
        self.circuit
            .outputs()
            .iter()
            .filter(|output| !arena.nodes[**output].value.is_zero())
            .count()
    }
}

/// Values for one universal fold-circuit instance.
#[derive(Clone, Copy)]
pub struct StatementFoldCircuitWitness<'a> {
    pub binary_selector: bool,
    pub left: &'a StatementWords,
    pub right: &'a StatementWords,
    pub parent: &'a StatementWords,
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<FoldCircuitInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: FoldCircuitInputSource, value: u32) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value)));
        self.bindings.push(FoldCircuitInputBinding {
            node_id: u32::try_from(node_id).expect("circuit input node count fits u32"),
            source,
        });
        value
    }

    fn private(&mut self, value: u32) -> Rec {
        self.input(FoldCircuitInputSource::PrivateWitness, value)
    }

    fn constrain(&mut self, gate: &Rec, constraint: Rec) {
        self.circuit.constrain_zero(gate.clone() * constraint);
    }

    fn finish(self) -> StatementFoldCircuit {
        StatementFoldCircuit {
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

struct ScopedWords {
    values: Vec<Rec>,
    raw: StatementWords,
}

impl ScopedWords {
    fn new(builder: &mut TrackedBuilder, scope: u32, words: &StatementWords) -> Self {
        let values = words
            .iter()
            .copied()
            .enumerate()
            .map(|(index, word)| {
                builder.input(
                    FoldCircuitInputSource::StatementWord {
                        scope,
                        index: u32::try_from(index).expect("statement word index fits u32"),
                    },
                    word.as_u32(),
                )
            })
            .collect();
        Self {
            values,
            raw: *words,
        }
    }

    fn value(&self, index: usize) -> Rec {
        self.values[index].clone()
    }

    fn raw(&self, index: usize) -> u32 {
        self.raw[index].as_u32()
    }
}

/// Builds the fixed binary-fold circuit from canonical statement words.
pub fn build_statement_fold_circuit(
    witness: StatementFoldCircuitWitness<'_>,
) -> StatementFoldCircuit {
    let mut builder = TrackedBuilder::new();
    let binary = builder.input(
        FoldCircuitInputSource::BinarySelector,
        u32::from(witness.binary_selector),
    );
    let one = constant(1);
    builder.constrain(&one, binary.clone() * (one.clone() - binary.clone()));

    let left = ScopedWords::new(&mut builder, LEFT_STATEMENT_SCOPE, witness.left);
    let right = ScopedWords::new(&mut builder, RIGHT_STATEMENT_SCOPE, witness.right);
    let parent = ScopedWords::new(&mut builder, PARENT_STATEMENT_SCOPE, witness.parent);

    constrain_common_job(&mut builder, &binary, &left, &right, &parent);
    constrain_slot_fold(&mut builder, &binary, &left, &right, &parent);
    constrain_body_fold(&mut builder, &binary, &left, &right, &parent);
    builder.finish()
}

fn constrain_common_job(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    left: &ScopedWords,
    right: &ScopedWords,
    parent: &ScopedWords,
) {
    for index in layout::SPAN_TAG..=layout::JOB_SLOT_HEIGHT {
        constrain_equal(builder, gate, left.value(index), right.value(index));
        constrain_equal(builder, gate, parent.value(index), left.value(index));
    }
}

fn constrain_slot_fold(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    left: &ScopedWords,
    right: &ScopedWords,
    parent: &ScopedWords,
) {
    constrain_equal(
        builder,
        gate,
        left.value(layout::SLOT_TAG),
        right.value(layout::SLOT_TAG),
    );
    constrain_equal(
        builder,
        gate,
        parent.value(layout::SLOT_TAG),
        left.value(layout::SLOT_TAG),
    );
    constrain_equal(
        builder,
        gate,
        left.value(layout::SLOT_HEIGHT),
        right.value(layout::SLOT_HEIGHT),
    );
    builder.constrain(
        gate,
        parent.value(layout::SLOT_HEIGHT) - left.value(layout::SLOT_HEIGHT) - constant(1),
    );

    let left_node = limb_range(left, layout::SLOT_NODE_INDEX_START, 4);
    let right_node = limb_range(right, layout::SLOT_NODE_INDEX_START, 4);
    let parent_node = limb_range(parent, layout::SLOT_NODE_INDEX_START, 4);
    add_limbs(
        builder,
        gate,
        &left_node,
        &[constant(1), constant(0), constant(0), constant(0)],
        &right_node,
        &raw_range(left, layout::SLOT_NODE_INDEX_START, 4),
        &[1, 0, 0, 0],
        &raw_range(right, layout::SLOT_NODE_INDEX_START, 4),
    );
    add_limbs(
        builder,
        gate,
        &parent_node,
        &parent_node,
        &left_node,
        &raw_range(parent, layout::SLOT_NODE_INDEX_START, 4),
        &raw_range(parent, layout::SLOT_NODE_INDEX_START, 4),
        &raw_range(left, layout::SLOT_NODE_INDEX_START, 4),
    );
}

fn constrain_body_fold(
    builder: &mut TrackedBuilder,
    binary: &Rec,
    left: &ScopedWords,
    right: &ScopedWords,
    parent: &ScopedWords,
) {
    let left_executed = body_flag(builder, binary, left);
    let right_executed = body_flag(builder, binary, right);
    let parent_executed = body_flag(builder, binary, parent);
    let one = constant(1);
    let left_empty = one.clone() - left_executed.clone();
    let right_empty = one.clone() - right_executed.clone();
    let both_executed = binary.clone() * left_executed.clone() * right_executed.clone();
    let left_only = binary.clone() * left_executed.clone() * right_empty.clone();
    let both_empty = binary.clone() * left_empty.clone() * right_empty;

    builder.constrain(binary, left_empty * right_executed.clone());
    builder.constrain(
        binary,
        parent_executed
            - (left_executed.clone() + right_executed.clone() - left_executed * right_executed),
    );

    for index in layout::EXECUTED_START..SPAN_STATEMENT_CANONICAL_WORDS {
        constrain_equal(builder, &left_only, parent.value(index), left.value(index));
        builder.constrain(&both_empty, parent.value(index));
    }

    constrain_both_executed(builder, &both_executed, left, right, parent);
}

fn constrain_both_executed(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    left: &ScopedWords,
    right: &ScopedWords,
    parent: &ScopedWords,
) {
    copy_range(builder, gate, parent, left, layout::EXECUTED_TAG, 1);
    copy_range(builder, gate, parent, left, layout::FIRST_SEGMENT_START, 2);
    add_field_range(
        builder,
        gate,
        left,
        right,
        parent,
        layout::EXECUTED_SEGMENT_COUNT_START,
        2,
    );
    copy_range(builder, gate, parent, left, layout::FIRST_CYCLE_START, 4);
    add_field_range(
        builder,
        gate,
        left,
        right,
        parent,
        layout::EXECUTED_CYCLE_COUNT_START,
        4,
    );
    copy_range(
        builder,
        gate,
        parent,
        left,
        layout::ENTRY_STATE_START,
        super::statement::MACHINE_STATE_CANONICAL_WORDS,
    );
    copy_range(
        builder,
        gate,
        parent,
        right,
        layout::EXIT_STATE_START,
        super::statement::MACHINE_STATE_CANONICAL_WORDS,
    );
    copy_range(
        builder,
        gate,
        parent,
        left,
        layout::INPUT_EDGE_START,
        super::statement::EDGE_CLAIM_CANONICAL_WORDS,
    );
    copy_range(
        builder,
        gate,
        parent,
        right,
        layout::OUTPUT_EDGE_START,
        super::statement::EDGE_CLAIM_CANONICAL_WORDS,
    );

    add_cross_range(
        builder,
        gate,
        left,
        layout::FIRST_SEGMENT_START,
        layout::EXECUTED_SEGMENT_COUNT_START,
        right,
        layout::FIRST_SEGMENT_START,
        2,
    );
    add_cross_range(
        builder,
        gate,
        left,
        layout::FIRST_CYCLE_START,
        layout::EXECUTED_CYCLE_COUNT_START,
        right,
        layout::FIRST_CYCLE_START,
        4,
    );
    for offset in 0..super::statement::MACHINE_STATE_CANONICAL_WORDS {
        constrain_equal(
            builder,
            gate,
            left.value(layout::EXIT_STATE_START + offset),
            right.value(layout::ENTRY_STATE_START + offset),
        );
    }

    let left_output_present = edge_flag(builder, gate, left, layout::OUTPUT_EDGE_TAG);
    let right_input_present = edge_flag(builder, gate, right, layout::INPUT_EDGE_TAG);
    builder.constrain(gate, left_output_present);
    builder.constrain(gate, right_input_present);
}

fn body_flag(builder: &mut TrackedBuilder, gate: &Rec, words: &ScopedWords) -> Rec {
    let actual =
        u32::from(words.raw(layout::BODY_TAG) == CanonicalTag::ExecutedBody.word().as_u32());
    let flag = builder.private(actual);
    constrain_boolean(builder, gate, &flag);
    let empty = constant(CanonicalTag::EmptyBody.word().as_u32());
    let executed = constant(CanonicalTag::ExecutedBody.word().as_u32());
    builder.constrain(
        gate,
        words.value(layout::BODY_TAG) - empty.clone() - flag.clone() * (executed - empty),
    );
    flag
}

fn edge_flag(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &ScopedWords,
    tag_index: usize,
) -> Rec {
    let actual = u32::from(words.raw(tag_index) == CanonicalTag::PresentEdge.word().as_u32());
    let flag = builder.private(actual);
    constrain_boolean(builder, gate, &flag);
    let absent = constant(CanonicalTag::AbsentEdge.word().as_u32());
    let present = constant(CanonicalTag::PresentEdge.word().as_u32());
    builder.constrain(
        gate,
        words.value(tag_index) - absent.clone() - flag.clone() * (present - absent),
    );
    flag
}

fn add_field_range(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    left: &ScopedWords,
    right: &ScopedWords,
    parent: &ScopedWords,
    start: usize,
    width: usize,
) {
    add_limbs(
        builder,
        gate,
        &limb_range(left, start, width),
        &limb_range(right, start, width),
        &limb_range(parent, start, width),
        &raw_range(left, start, width),
        &raw_range(right, start, width),
        &raw_range(parent, start, width),
    );
}

fn add_cross_range(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    left: &ScopedWords,
    left_start: usize,
    left_count_start: usize,
    right: &ScopedWords,
    right_start: usize,
    width: usize,
) {
    add_limbs(
        builder,
        gate,
        &limb_range(left, left_start, width),
        &limb_range(left, left_count_start, width),
        &limb_range(right, right_start, width),
        &raw_range(left, left_start, width),
        &raw_range(left, left_count_start, width),
        &raw_range(right, right_start, width),
    );
}

fn add_limbs(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    lhs: &[Rec],
    rhs: &[Rec],
    output: &[Rec],
    lhs_raw: &[u32],
    rhs_raw: &[u32],
    output_raw: &[u32],
) {
    debug_assert_eq!(lhs.len(), rhs.len());
    debug_assert_eq!(lhs.len(), output.len());
    debug_assert_eq!(lhs.len(), lhs_raw.len());
    debug_assert_eq!(lhs.len(), rhs_raw.len());
    debug_assert_eq!(lhs.len(), output_raw.len());
    let mut carry_value = 0_u64;
    let mut carry = constant(0);
    for index in 0..lhs.len() {
        let total = u64::from(lhs_raw[index]) + u64::from(rhs_raw[index]) + carry_value;
        let next_carry_value = total / u64::from(U16_BASE);
        let next_carry =
            builder.private(u32::try_from(next_carry_value).expect("u16 addition carry fits u32"));
        constrain_boolean(builder, gate, &next_carry);
        builder.constrain(
            gate,
            lhs[index].clone() + rhs[index].clone() + carry
                - output[index].clone()
                - next_carry.clone() * constant(U16_BASE),
        );
        carry_value = next_carry_value;
        carry = next_carry;
    }
    builder.constrain(gate, carry);
}

fn copy_range(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    target: &ScopedWords,
    source: &ScopedWords,
    start: usize,
    width: usize,
) {
    for index in start..start + width {
        constrain_equal(builder, gate, target.value(index), source.value(index));
    }
}

fn limb_range(words: &ScopedWords, start: usize, width: usize) -> Vec<Rec> {
    (start..start + width)
        .map(|index| words.value(index))
        .collect()
}

fn raw_range(words: &ScopedWords, start: usize, width: usize) -> Vec<u32> {
    (start..start + width)
        .map(|index| words.raw(index))
        .collect()
}

fn constrain_equal(builder: &mut TrackedBuilder, gate: &Rec, lhs: Rec, rhs: Rec) {
    builder.constrain(gate, lhs - rhs);
}

fn constrain_boolean(builder: &mut TrackedBuilder, gate: &Rec, value: &Rec) {
    builder.constrain(gate, value.clone() * (constant(1) - value.clone()));
}

fn constant(value: u32) -> Rec {
    Rec::from(BaseField::from(value))
}

/// Converts a typed statement into its fixed canonical word array.
pub fn statement_words(statement: &SpanStatement) -> Result<StatementWords, StatementFoldError> {
    let words = statement.canonical_words();
    let actual = words.len();
    words
        .try_into()
        .map_err(|_| StatementFoldError::CanonicalWordCountMismatch {
            expected: SPAN_STATEMENT_CANONICAL_WORDS,
            actual,
        })
}

/// Invalid canonical statement input for the fold circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementFoldError {
    CanonicalWordCountMismatch { expected: usize, actual: usize },
}

impl fmt::Display for StatementFoldError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CanonicalWordCountMismatch { expected, actual } => write!(
                formatter,
                "canonical statement has {actual} words, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for StatementFoldError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    use crate::v2::test_fixtures::{executed_and_empty, two_empty, two_executed};

    fn circuit(statements: (SpanStatement, SpanStatement, SpanStatement)) -> StatementFoldCircuit {
        let (left, right, parent) = statements;
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let parent = statement_words(&parent).expect("parent statement width is canonical");
        build_statement_fold_circuit(StatementFoldCircuitWitness {
            binary_selector: true,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    #[derive(Clone, Copy)]
    enum FoldTamper {
        RightJob,
        RightNode,
        ParentNode,
        RightHeight,
        ParentHeight,
        RightFirstSegment,
        RightFirstCycle,
        RightEntryState,
        LeftOutput,
        RightInput,
    }

    fn tampered_circuit(tamper: FoldTamper) -> StatementFoldCircuit {
        let (left, right, parent) = two_executed();
        let mut left = statement_words(&left).expect("left statement width is canonical");
        let mut right = statement_words(&right).expect("right statement width is canonical");
        let mut parent = statement_words(&parent).expect("parent statement width is canonical");
        match tamper {
            FoldTamper::RightJob => right[layout::PROTOCOL_START] = M31Word::from(99),
            FoldTamper::RightNode => right[layout::SLOT_NODE_INDEX_START] = M31Word::from(2),
            FoldTamper::ParentNode => parent[layout::SLOT_NODE_INDEX_START] = M31Word::from(1),
            FoldTamper::RightHeight => right[layout::SLOT_HEIGHT] = M31Word::from(1),
            FoldTamper::ParentHeight => parent[layout::SLOT_HEIGHT] = M31Word::from(2),
            FoldTamper::RightFirstSegment => right[layout::FIRST_SEGMENT_START] = M31Word::from(2),
            FoldTamper::RightFirstCycle => right[layout::FIRST_CYCLE_START] = M31Word::from(5),
            FoldTamper::RightEntryState => {
                right[layout::ENTRY_STATE_START + layout::MACHINE_STATE_PC_START_OFFSET] =
                    M31Word::from(99)
            }
            FoldTamper::LeftOutput => {
                left[layout::OUTPUT_EDGE_TAG] = CanonicalTag::PresentEdge.word()
            }
            FoldTamper::RightInput => {
                right[layout::INPUT_EDGE_TAG] = CanonicalTag::PresentEdge.word()
            }
        }
        build_statement_fold_circuit(StatementFoldCircuitWitness {
            binary_selector: true,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    #[rstest]
    #[case::both_executed(two_executed())]
    #[case::executed_then_empty(executed_and_empty())]
    #[case::both_empty(two_empty())]
    fn every_valid_binary_body_case_satisfies_the_fold_circuit(
        #[case] statements: (SpanStatement, SpanStatement, SpanStatement),
    ) {
        assert_eq!(circuit(statements).nonzero_output_count(), 0);
    }

    #[rstest]
    fn changed_parent_segment_count_is_rejected() {
        let (left, right, parent) = two_executed();
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let mut parent = statement_words(&parent).expect("parent statement width is canonical");
        parent[layout::EXECUTED_SEGMENT_COUNT_START] = M31Word::from(3);
        let circuit = build_statement_fold_circuit(StatementFoldCircuitWitness {
            binary_selector: true,
            left: &left,
            right: &right,
            parent: &parent,
        });
        assert_ne!(circuit.nonzero_output_count(), 0);
    }

    #[rstest]
    fn swapped_children_are_rejected() {
        let (left, right, parent) = two_executed();
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let parent = statement_words(&parent).expect("parent statement width is canonical");
        let circuit = build_statement_fold_circuit(StatementFoldCircuitWitness {
            binary_selector: true,
            left: &right,
            right: &left,
            parent: &parent,
        });
        assert_ne!(circuit.nonzero_output_count(), 0);
    }

    #[rstest]
    #[case::job(FoldTamper::RightJob)]
    #[case::right_node(FoldTamper::RightNode)]
    #[case::parent_node(FoldTamper::ParentNode)]
    #[case::right_height(FoldTamper::RightHeight)]
    #[case::parent_height(FoldTamper::ParentHeight)]
    #[case::segment_continuity(FoldTamper::RightFirstSegment)]
    #[case::cycle_continuity(FoldTamper::RightFirstCycle)]
    #[case::state_continuity(FoldTamper::RightEntryState)]
    #[case::left_output(FoldTamper::LeftOutput)]
    #[case::right_input(FoldTamper::RightInput)]
    fn every_binary_fold_boundary_rejects_substitution(#[case] tamper: FoldTamper) {
        assert_ne!(tampered_circuit(tamper).nonzero_output_count(), 0);
    }

    #[rstest]
    fn inactive_binary_circuit_accepts_zero_padded_inputs() {
        let zero = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
        let circuit = build_statement_fold_circuit(StatementFoldCircuitWitness {
            binary_selector: false,
            left: &zero,
            right: &zero,
            parent: &zero,
        });
        assert_eq!(circuit.nonzero_output_count(), 0);
    }

    #[rstest]
    fn fold_circuit_structure_is_independent_of_the_body_case() {
        let shapes = [two_executed(), executed_and_empty(), two_empty()].map(|statements| {
            let circuit = circuit(statements);
            let node_count = circuit.circuit().arena().nodes.len();
            (
                node_count,
                circuit.circuit().outputs().len(),
                circuit.input_bindings().len(),
            )
        });
        assert_eq!(shapes[1..], [shapes[0], shapes[0]]);
    }

    #[rstest]
    fn every_statement_word_has_one_fixed_circuit_input() {
        let circuit = circuit(two_executed());
        let statement_inputs = circuit
            .input_bindings()
            .iter()
            .filter(|binding| {
                matches!(binding.source, FoldCircuitInputSource::StatementWord { .. })
            })
            .count();
        assert_eq!(statement_inputs, 3 * SPAN_STATEMENT_CANONICAL_WORDS);
    }
}
