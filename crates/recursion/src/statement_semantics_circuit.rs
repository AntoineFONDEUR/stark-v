//! Universal statement semantics compiled into the recursion arithmetic circuit.
//!
//! Statement words are range-bound before entering this circuit. Segment and
//! empty modes establish the checked height-zero base cases, while binary mode
//! enforces the complete [`SpanStatement::fold`] transformation. The circuit
//! shape is identical in every mode, and every equation remains a distinct
//! zero output so one failing invariant cannot cancel another.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;

use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

use super::protocol::{CanonicalTag, CanonicalWords};
use super::statement::{SPAN_STATEMENT_CANONICAL_WORDS, SpanStatement, canonical_layout as layout};
use super::statement_input_air::{
    LEFT_STATEMENT_SCOPE, PARENT_STATEMENT_SCOPE, RIGHT_STATEMENT_SCOPE, SEGMENT_STATEMENT_SCOPE,
};
use super::wire::ProofKind;

const U16_BASE: u32 = 1 << 16;

pub type StatementWords = [M31Word; SPAN_STATEMENT_CANONICAL_WORDS];

/// Universal verifier modes in which one circuit input carries witness data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProofKindSet {
    segment: bool,
    binary: bool,
    empty: bool,
}

impl ProofKindSet {
    pub const SEGMENT: Self = Self {
        segment: true,
        binary: false,
        empty: false,
    };
    pub const BINARY: Self = Self {
        segment: false,
        binary: true,
        empty: false,
    };
    pub const EMPTY: Self = Self {
        segment: false,
        binary: false,
        empty: true,
    };
    pub const LEAVES: Self = Self {
        segment: true,
        binary: false,
        empty: true,
    };
    pub const ALL: Self = Self {
        segment: true,
        binary: true,
        empty: true,
    };

    pub const fn contains(self, kind: ProofKind) -> bool {
        match kind {
            ProofKind::SegmentLeaf => self.segment,
            ProofKind::BinaryNode => self.binary,
            ProofKind::EmptyLeaf => self.empty,
        }
    }

    pub const fn selectors(self) -> [bool; 3] {
        [self.segment, self.binary, self.empty]
    }
}

/// Source of one input node in the fixed statement circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementCircuitInputSource {
    StatementWord {
        scope: u32,
        index: u32,
        active_kinds: ProofKindSet,
    },
    ProofSelector {
        kind: ProofKind,
    },
    PrivateWitness {
        active_kinds: ProofKindSet,
    },
}

/// Node binding needed to connect circuit inputs to AIR relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StatementCircuitInputBinding {
    pub node_id: u32,
    pub source: StatementCircuitInputSource,
}

/// Fixed statement circuit plus the ownership of every input node.
#[derive(Debug)]
pub struct StatementSemanticsCircuit {
    circuit: ConstraintCircuit,
    input_bindings: Vec<StatementCircuitInputBinding>,
}

impl StatementSemanticsCircuit {
    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[StatementCircuitInputBinding] {
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

/// Values for one universal statement-semantics circuit instance.
#[derive(Clone, Copy)]
pub struct StatementSemanticsCircuitWitness<'a> {
    pub segment_selector: bool,
    pub binary_selector: bool,
    pub empty_selector: bool,
    pub segment: &'a StatementWords,
    pub left: &'a StatementWords,
    pub right: &'a StatementWords,
    pub parent: &'a StatementWords,
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<StatementCircuitInputBinding>,
    selected_kind: Option<ProofKind>,
}

impl TrackedBuilder {
    fn new(selected_kind: Option<ProofKind>) -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
            selected_kind,
        }
    }

    fn input(&mut self, source: StatementCircuitInputSource, value: u32) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value)));
        self.bindings.push(StatementCircuitInputBinding {
            node_id: u32::try_from(node_id).expect("circuit input node count fits u32"),
            source,
        });
        value
    }

    fn private(&mut self, active_kinds: ProofKindSet, value: u32) -> Rec {
        let value = if self
            .selected_kind
            .is_some_and(|kind| active_kinds.contains(kind))
        {
            value
        } else {
            0
        };
        self.input(
            StatementCircuitInputSource::PrivateWitness { active_kinds },
            value,
        )
    }

    fn constrain(&mut self, gate: &Rec, constraint: Rec) {
        self.circuit.constrain_zero(gate.clone() * constraint);
    }

    fn finish(self) -> StatementSemanticsCircuit {
        StatementSemanticsCircuit {
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
    fn new(
        builder: &mut TrackedBuilder,
        scope: u32,
        active_kinds: ProofKindSet,
        words: &StatementWords,
    ) -> Self {
        let values = words
            .iter()
            .copied()
            .enumerate()
            .map(|(index, word)| {
                builder.input(
                    StatementCircuitInputSource::StatementWord {
                        scope,
                        index: u32::try_from(index).expect("statement word index fits u32"),
                        active_kinds,
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

/// Builds the fixed universal circuit from canonical statement words.
pub fn build_statement_semantics_circuit(
    witness: StatementSemanticsCircuitWitness<'_>,
) -> StatementSemanticsCircuit {
    let selected_kind = match (
        witness.segment_selector,
        witness.binary_selector,
        witness.empty_selector,
    ) {
        (true, false, false) => Some(ProofKind::SegmentLeaf),
        (false, true, false) => Some(ProofKind::BinaryNode),
        (false, false, true) => Some(ProofKind::EmptyLeaf),
        _ => None,
    };
    let mut builder = TrackedBuilder::new(selected_kind);
    let segment_selector = builder.input(
        StatementCircuitInputSource::ProofSelector {
            kind: ProofKind::SegmentLeaf,
        },
        u32::from(witness.segment_selector),
    );
    let binary = builder.input(
        StatementCircuitInputSource::ProofSelector {
            kind: ProofKind::BinaryNode,
        },
        u32::from(witness.binary_selector),
    );
    let empty_selector = builder.input(
        StatementCircuitInputSource::ProofSelector {
            kind: ProofKind::EmptyLeaf,
        },
        u32::from(witness.empty_selector),
    );
    let one = constant(1);
    constrain_boolean(&mut builder, &one, &segment_selector);
    constrain_boolean(&mut builder, &one, &binary);
    constrain_boolean(&mut builder, &one, &empty_selector);
    builder.constrain(&one, segment_selector.clone() * binary.clone());
    builder.constrain(&one, segment_selector.clone() * empty_selector.clone());
    builder.constrain(&one, binary.clone() * empty_selector.clone());

    let segment = ScopedWords::new(
        &mut builder,
        SEGMENT_STATEMENT_SCOPE,
        ProofKindSet::SEGMENT,
        witness.segment,
    );
    let left = ScopedWords::new(
        &mut builder,
        LEFT_STATEMENT_SCOPE,
        ProofKindSet::BINARY,
        witness.left,
    );
    let right = ScopedWords::new(
        &mut builder,
        RIGHT_STATEMENT_SCOPE,
        ProofKindSet::BINARY,
        witness.right,
    );
    let parent = ScopedWords::new(
        &mut builder,
        PARENT_STATEMENT_SCOPE,
        ProofKindSet::ALL,
        witness.parent,
    );

    constrain_common_job(&mut builder, &binary, &left, &right, &parent);
    constrain_slot_fold(&mut builder, &binary, &left, &right, &parent);
    constrain_body_fold(&mut builder, &binary, &left, &right, &parent);
    constrain_leaf_semantics(
        &mut builder,
        &segment_selector,
        &empty_selector,
        &segment,
        &parent,
    );
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

fn constrain_leaf_semantics(
    builder: &mut TrackedBuilder,
    segment_selector: &Rec,
    empty_selector: &Rec,
    segment: &ScopedWords,
    parent: &ScopedWords,
) {
    let leaf = segment_selector.clone() + empty_selector.clone();
    for index in 0..SPAN_STATEMENT_CANONICAL_WORDS {
        constrain_equal(
            builder,
            segment_selector,
            segment.value(index),
            parent.value(index),
        );
    }

    constrain_tag(
        builder,
        &leaf,
        parent,
        layout::SPAN_TAG,
        CanonicalTag::SpanStatement,
    );
    constrain_tag(
        builder,
        &leaf,
        parent,
        layout::JOB_TAG,
        CanonicalTag::JobContext,
    );
    constrain_tag(
        builder,
        &leaf,
        parent,
        layout::COMPLETE_TAG,
        CanonicalTag::CompleteExecution,
    );
    constrain_machine_state_shape(builder, &leaf, parent, layout::INITIAL_STATE_START);
    constrain_machine_state_shape(builder, &leaf, parent, layout::FINAL_STATE_START);
    constrain_tag(
        builder,
        &leaf,
        parent,
        layout::SLOT_TAG,
        CanonicalTag::SlotSpan,
    );
    builder.constrain(&leaf, parent.value(layout::SLOT_HEIGHT));

    let total_cycle_bits =
        decompose_word_bits(builder, &leaf, parent, layout::TOTAL_CYCLES_START, 4);
    builder.constrain(&leaf, constant(1) - or_bits(&total_cycle_bits));

    let segment_count_bits =
        decompose_word_bits(builder, &leaf, parent, layout::JOB_SEGMENT_COUNT_START, 2);
    let segment_count_minus_one = subtract_one_bits(builder, &leaf, &segment_count_bits, parent);
    let height_flags = bit_length_flags(&segment_count_minus_one);
    let encoded_height =
        height_flags
            .iter()
            .enumerate()
            .fold(constant(0), |sum, (height, flag)| {
                sum + flag.clone()
                    * constant(u32::try_from(height).expect("statement height fits u32"))
            });
    builder.constrain(
        &leaf,
        parent.value(layout::JOB_SLOT_HEIGHT) - encoded_height,
    );

    let node_bits = decompose_word_bits(builder, &leaf, parent, layout::SLOT_NODE_INDEX_START, 2);
    builder.constrain(&leaf, parent.value(layout::SLOT_NODE_INDEX_START + 2));
    builder.constrain(&leaf, parent.value(layout::SLOT_NODE_INDEX_START + 3));
    for (bit_index, node_bit) in node_bits.iter().enumerate() {
        let height_too_small = height_flags
            .iter()
            .take(bit_index + 1)
            .cloned()
            .fold(constant(0), |sum, flag| sum + flag);
        builder.constrain(&leaf, node_bit.clone() * height_too_small);
    }

    let node_before_segment_count = less_than_bits(&node_bits, &segment_count_bits);
    builder.constrain(
        segment_selector,
        constant(1) - node_before_segment_count.clone(),
    );
    builder.constrain(empty_selector, node_before_segment_count);

    builder.constrain(
        &leaf,
        parent.value(layout::BODY_TAG)
            - segment_selector.clone() * constant(CanonicalTag::ExecutedBody.word().as_u32())
            - empty_selector.clone() * constant(CanonicalTag::EmptyBody.word().as_u32()),
    );
    for index in layout::EXECUTED_START..SPAN_STATEMENT_CANONICAL_WORDS {
        builder.constrain(empty_selector, parent.value(index));
    }

    constrain_segment_leaf(
        builder,
        segment_selector,
        parent,
        &node_bits,
        &segment_count_minus_one,
        &total_cycle_bits,
    );
}

fn constrain_segment_leaf(
    builder: &mut TrackedBuilder,
    segment: &Rec,
    words: &ScopedWords,
    node_bits: &[Rec],
    segment_count_minus_one: &[Rec],
    total_cycle_bits: &[Rec],
) {
    constrain_tag(
        builder,
        segment,
        words,
        layout::EXECUTED_TAG,
        CanonicalTag::ExecutedSpan,
    );
    constrain_equal(
        builder,
        segment,
        words.value(layout::FIRST_SEGMENT_START),
        words.value(layout::SLOT_NODE_INDEX_START),
    );
    constrain_equal(
        builder,
        segment,
        words.value(layout::FIRST_SEGMENT_START + 1),
        words.value(layout::SLOT_NODE_INDEX_START + 1),
    );
    builder.constrain(
        segment,
        words.value(layout::EXECUTED_SEGMENT_COUNT_START) - constant(1),
    );
    builder.constrain(
        segment,
        words.value(layout::EXECUTED_SEGMENT_COUNT_START + 1),
    );

    constrain_machine_state_shape(builder, segment, words, layout::ENTRY_STATE_START);
    constrain_machine_state_shape(builder, segment, words, layout::EXIT_STATE_START);

    let first_cycle_bits =
        decompose_word_bits(builder, segment, words, layout::FIRST_CYCLE_START, 4);
    let cycle_count_bits = decompose_word_bits(
        builder,
        segment,
        words,
        layout::EXECUTED_CYCLE_COUNT_START,
        4,
    );
    builder.constrain(segment, constant(1) - or_bits(&cycle_count_bits));
    let (end_cycle_bits, overflow) = add_bits(&first_cycle_bits, &cycle_count_bits);
    builder.constrain(segment, overflow);
    builder.constrain(segment, less_than_bits(total_cycle_bits, &end_cycle_bits));

    let first = constant(1) - or_bits(node_bits);
    let last = equal_bits(node_bits, segment_count_minus_one);
    let first_gate = segment.clone() * first.clone();
    let last_gate = segment.clone() * last.clone();

    for index in layout::FIRST_CYCLE_START..layout::FIRST_CYCLE_START + 4 {
        builder.constrain(&first_gate, words.value(index));
    }
    copy_cross_range(
        builder,
        &first_gate,
        words,
        layout::ENTRY_STATE_START,
        layout::INITIAL_STATE_START,
        super::statement::MACHINE_STATE_CANONICAL_WORDS,
    );
    for (end_bit, total_bit) in end_cycle_bits.iter().zip(total_cycle_bits) {
        constrain_equal(builder, &last_gate, end_bit.clone(), total_bit.clone());
    }
    copy_cross_range(
        builder,
        &last_gate,
        words,
        layout::EXIT_STATE_START,
        layout::FINAL_STATE_START,
        super::statement::MACHINE_STATE_CANONICAL_WORDS,
    );

    constrain_edge(
        builder,
        segment,
        &first,
        words,
        layout::INPUT_EDGE_TAG,
        layout::INPUT_EDGE_DIGEST_START,
        layout::PUBLIC_INPUT_START,
    );
    constrain_edge(
        builder,
        segment,
        &last,
        words,
        layout::OUTPUT_EDGE_TAG,
        layout::OUTPUT_EDGE_DIGEST_START,
        layout::PUBLIC_OUTPUT_START,
    );
}

fn constrain_machine_state_shape(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &ScopedWords,
    start: usize,
) {
    constrain_tag(
        builder,
        gate,
        words,
        start + layout::MACHINE_STATE_TAG_OFFSET,
        CanonicalTag::MachineState,
    );
    builder.constrain(
        gate,
        words.value(start + layout::MACHINE_STATE_REGISTERS_START_OFFSET),
    );
    builder.constrain(
        gate,
        words.value(start + layout::MACHINE_STATE_REGISTERS_START_OFFSET + 1),
    );
}

fn constrain_edge(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    present: &Rec,
    words: &ScopedWords,
    tag_index: usize,
    digest_start: usize,
    complete_digest_start: usize,
) {
    let absent = constant(CanonicalTag::AbsentEdge.word().as_u32());
    let present_tag = constant(CanonicalTag::PresentEdge.word().as_u32());
    builder.constrain(
        gate,
        words.value(tag_index) - absent.clone() - present.clone() * (present_tag - absent),
    );
    for offset in 0..8 {
        builder.constrain(
            gate,
            words.value(digest_start + offset)
                - present.clone() * words.value(complete_digest_start + offset),
        );
    }
}

fn constrain_tag(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &ScopedWords,
    index: usize,
    tag: CanonicalTag,
) {
    builder.constrain(gate, words.value(index) - constant(tag.word().as_u32()));
}

fn decompose_word_bits(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &ScopedWords,
    start: usize,
    width: usize,
) -> Vec<Rec> {
    let mut bits = Vec::with_capacity(width * 16);
    for limb_index in 0..width {
        let raw = words.raw(start + limb_index);
        let limb_bits = (0..16)
            .map(|bit_index| {
                let bit = builder.private(ProofKindSet::LEAVES, (raw >> bit_index) & 1);
                constrain_boolean(builder, gate, &bit);
                bit
            })
            .collect::<Vec<_>>();
        let reconstructed = limb_bits
            .iter()
            .enumerate()
            .fold(constant(0), |sum, (bit_index, bit)| {
                sum + bit.clone() * constant(1_u32 << bit_index)
            });
        builder.constrain(gate, words.value(start + limb_index) - reconstructed);
        bits.extend(limb_bits);
    }
    bits
}

fn subtract_one_bits(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    value_bits: &[Rec],
    words: &ScopedWords,
) -> Vec<Rec> {
    let raw = words.raw(layout::JOB_SEGMENT_COUNT_START)
        | (words.raw(layout::JOB_SEGMENT_COUNT_START + 1) << 16);
    let raw_minus_one = raw.wrapping_sub(1);
    let minus_one_bits = (0..32)
        .map(|bit_index| {
            let bit = builder.private(ProofKindSet::LEAVES, (raw_minus_one >> bit_index) & 1);
            constrain_boolean(builder, gate, &bit);
            bit
        })
        .collect::<Vec<_>>();

    let mut carry = constant(1);
    for (value_bit, minus_one_bit) in value_bits.iter().zip(&minus_one_bits) {
        let sum_bit = minus_one_bit.clone() + carry.clone()
            - constant(2) * minus_one_bit.clone() * carry.clone();
        constrain_equal(builder, gate, value_bit.clone(), sum_bit);
        carry = minus_one_bit.clone() * carry;
    }
    builder.constrain(gate, carry);
    minus_one_bits
}

fn bit_length_flags(bits: &[Rec]) -> Vec<Rec> {
    let mut flags = vec![constant(0); bits.len() + 1];
    let mut seen = constant(0);
    for index in (0..bits.len()).rev() {
        let highest = bits[index].clone() * (constant(1) - seen.clone());
        flags[index + 1] = highest;
        seen = seen.clone() + bits[index].clone() - seen * bits[index].clone();
    }
    flags[0] = constant(1) - seen;
    flags
}

fn or_bits(bits: &[Rec]) -> Rec {
    bits.iter().fold(constant(0), |seen, bit| {
        seen.clone() + bit.clone() - seen * bit.clone()
    })
}

fn equal_bits(lhs: &[Rec], rhs: &[Rec]) -> Rec {
    debug_assert_eq!(lhs.len(), rhs.len());
    lhs.iter().zip(rhs).fold(constant(1), |equal, (lhs, rhs)| {
        let same =
            constant(1) - lhs.clone() - rhs.clone() + constant(2) * lhs.clone() * rhs.clone();
        equal * same
    })
}

fn less_than_bits(lhs: &[Rec], rhs: &[Rec]) -> Rec {
    debug_assert_eq!(lhs.len(), rhs.len());
    let mut equal_above = constant(1);
    let mut less = constant(0);
    for (lhs, rhs) in lhs.iter().zip(rhs).rev() {
        less += equal_above.clone() * (constant(1) - lhs.clone()) * rhs.clone();
        let same =
            constant(1) - lhs.clone() - rhs.clone() + constant(2) * lhs.clone() * rhs.clone();
        let next_equal_above = equal_above * same;
        equal_above = next_equal_above;
    }
    less
}

fn add_bits(lhs: &[Rec], rhs: &[Rec]) -> (Vec<Rec>, Rec) {
    debug_assert_eq!(lhs.len(), rhs.len());
    let mut carry = constant(0);
    let mut output = Vec::with_capacity(lhs.len());
    for (lhs, rhs) in lhs.iter().zip(rhs) {
        let lhs_xor_rhs = lhs.clone() + rhs.clone() - constant(2) * lhs.clone() * rhs.clone();
        let output_bit =
            lhs_xor_rhs.clone() + carry.clone() - constant(2) * lhs_xor_rhs.clone() * carry.clone();
        carry = lhs.clone() * rhs.clone() + carry * lhs_xor_rhs;
        output.push(output_bit);
    }
    (output, carry)
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
    let flag = builder.private(ProofKindSet::BINARY, actual);
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
    let flag = builder.private(ProofKindSet::BINARY, actual);
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
        let next_carry = builder.private(
            ProofKindSet::BINARY,
            u32::try_from(next_carry_value).expect("u16 addition carry fits u32"),
        );
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

fn copy_cross_range(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &ScopedWords,
    target_start: usize,
    source_start: usize,
    width: usize,
) {
    for offset in 0..width {
        constrain_equal(
            builder,
            gate,
            words.value(target_start + offset),
            words.value(source_start + offset),
        );
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
pub fn statement_words(
    statement: &SpanStatement,
) -> Result<StatementWords, StatementSemanticsError> {
    let words = statement.canonical_words();
    let actual = words.len();
    words
        .try_into()
        .map_err(|_| StatementSemanticsError::CanonicalWordCountMismatch {
            expected: SPAN_STATEMENT_CANONICAL_WORDS,
            actual,
        })
}

/// Invalid canonical input for the statement-semantics circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementSemanticsError {
    CanonicalWordCountMismatch { expected: usize, actual: usize },
}

impl fmt::Display for StatementSemanticsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CanonicalWordCountMismatch { expected, actual } => write!(
                formatter,
                "canonical statement has {actual} words, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for StatementSemanticsError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    use crate::test_fixtures::{executed_and_empty, job, leaf, state, two_empty, two_executed};

    fn zero_words() -> StatementWords {
        [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS]
    }

    fn inactive_circuit() -> StatementSemanticsCircuit {
        let zero = zero_words();
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: false,
            empty_selector: false,
            segment: &zero,
            left: &zero,
            right: &zero,
            parent: &zero,
        })
    }

    fn binary_circuit(
        statements: (SpanStatement, SpanStatement, SpanStatement),
    ) -> StatementSemanticsCircuit {
        let (left, right, parent) = statements;
        let zero = zero_words();
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let parent = statement_words(&parent).expect("parent statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &zero,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    fn segment_circuit(statement: &SpanStatement) -> StatementSemanticsCircuit {
        let zero = zero_words();
        let statement = statement_words(statement).expect("segment statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: true,
            binary_selector: false,
            empty_selector: false,
            segment: &statement,
            left: &zero,
            right: &zero,
            parent: &statement,
        })
    }

    fn empty_circuit(statement: &SpanStatement) -> StatementSemanticsCircuit {
        let zero = zero_words();
        let statement = statement_words(statement).expect("empty statement width is canonical");
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: false,
            empty_selector: true,
            segment: &zero,
            left: &zero,
            right: &zero,
            parent: &statement,
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

    fn tampered_fold_circuit(tamper: FoldTamper) -> StatementSemanticsCircuit {
        let (left, right, parent) = two_executed();
        let zero = zero_words();
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
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &zero,
            left: &left,
            right: &right,
            parent: &parent,
        })
    }

    #[derive(Clone, Copy)]
    enum LeafTamper {
        SpanTag,
        InitialZeroRegister,
        ZeroTotalCycles,
        ZeroSegmentCount,
        JobHeight,
        SlotHeight,
        NodeOutsideCapacity,
        FirstSegment,
        SegmentCount,
        ZeroCycleCount,
        CycleOutsideJob,
        CycleOverflow,
        InitialState,
        FinalState,
        InputEdge,
        OutputEdge,
        EmptyPayload,
        EmptyBeforePadding,
    }

    fn tampered_leaf_circuit(tamper: LeafTamper) -> StatementSemanticsCircuit {
        let job = job(3, 12);
        let (statement, empty_mode) = match tamper {
            LeafTamper::InitialState | LeafTamper::InputEdge => {
                (leaf(job, 0, 0, 4, state(0), state(1)), false)
            }
            LeafTamper::FinalState | LeafTamper::OutputEdge => {
                (leaf(job, 2, 8, 4, state(2), state(3)), false)
            }
            LeafTamper::EmptyPayload | LeafTamper::EmptyBeforePadding => (
                SpanStatement::empty_leaf(job, 3).expect("slot three is padding"),
                true,
            ),
            _ => (leaf(job, 1, 4, 4, state(1), state(2)), false),
        };
        let zero = zero_words();
        let mut parent = statement_words(&statement).expect("leaf statement width is canonical");
        match tamper {
            LeafTamper::SpanTag => parent[layout::SPAN_TAG] = M31Word::from(99),
            LeafTamper::InitialZeroRegister => {
                parent[layout::INITIAL_STATE_START + layout::MACHINE_STATE_REGISTERS_START_OFFSET] =
                    M31Word::from(1)
            }
            LeafTamper::ZeroTotalCycles => parent
                [layout::TOTAL_CYCLES_START..layout::TOTAL_CYCLES_START + 4]
                .fill(M31Word::ZERO),
            LeafTamper::ZeroSegmentCount => parent
                [layout::JOB_SEGMENT_COUNT_START..layout::JOB_SEGMENT_COUNT_START + 2]
                .fill(M31Word::ZERO),
            LeafTamper::JobHeight => parent[layout::JOB_SLOT_HEIGHT] = M31Word::from(1),
            LeafTamper::SlotHeight => parent[layout::SLOT_HEIGHT] = M31Word::from(1),
            LeafTamper::NodeOutsideCapacity => {
                parent[layout::SLOT_NODE_INDEX_START] = M31Word::from(4)
            }
            LeafTamper::FirstSegment => parent[layout::FIRST_SEGMENT_START] = M31Word::from(2),
            LeafTamper::SegmentCount => {
                parent[layout::EXECUTED_SEGMENT_COUNT_START] = M31Word::from(2)
            }
            LeafTamper::ZeroCycleCount => parent
                [layout::EXECUTED_CYCLE_COUNT_START..layout::EXECUTED_CYCLE_COUNT_START + 4]
                .fill(M31Word::ZERO),
            LeafTamper::CycleOutsideJob => parent[layout::FIRST_CYCLE_START] = M31Word::from(11),
            LeafTamper::CycleOverflow => parent
                [layout::FIRST_CYCLE_START..layout::FIRST_CYCLE_START + 4]
                .fill(M31Word::from(u16::MAX)),
            LeafTamper::InitialState => {
                parent[layout::ENTRY_STATE_START + layout::MACHINE_STATE_PC_START_OFFSET] =
                    M31Word::from(1)
            }
            LeafTamper::FinalState => {
                parent[layout::EXIT_STATE_START + layout::MACHINE_STATE_PC_START_OFFSET] =
                    M31Word::from(1)
            }
            LeafTamper::InputEdge => {
                parent[layout::INPUT_EDGE_TAG] = CanonicalTag::AbsentEdge.word()
            }
            LeafTamper::OutputEdge => {
                parent[layout::OUTPUT_EDGE_TAG] = CanonicalTag::AbsentEdge.word()
            }
            LeafTamper::EmptyPayload => parent[layout::EXECUTED_TAG] = M31Word::from(1),
            LeafTamper::EmptyBeforePadding => {
                parent[layout::SLOT_NODE_INDEX_START] = M31Word::from(2)
            }
        }
        let segment = if empty_mode { zero } else { parent };
        build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: !empty_mode,
            binary_selector: false,
            empty_selector: empty_mode,
            segment: &segment,
            left: &zero,
            right: &zero,
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
        assert_eq!(binary_circuit(statements).nonzero_output_count(), 0);
    }

    #[rstest]
    #[case::first(leaf(job(3, 12), 0, 0, 4, state(0), state(1)))]
    #[case::middle(leaf(job(3, 12), 1, 4, 4, state(1), state(2)))]
    #[case::last(leaf(job(3, 12), 2, 8, 4, state(2), state(3)))]
    fn every_segment_leaf_position_satisfies_the_semantics_circuit(
        #[case] statement: SpanStatement,
    ) {
        assert_eq!(segment_circuit(&statement).nonzero_output_count(), 0);
    }

    #[rstest]
    #[case::one(1)]
    #[case::two(2)]
    #[case::three(3)]
    #[case::four(4)]
    #[case::five(5)]
    #[case::u16_max(u16::MAX.into())]
    #[case::above_u16(u32::from(u16::MAX) + 1)]
    #[case::height_seventeen((1_u32 << 16) + 1)]
    #[case::u32_max(u32::MAX)]
    fn segment_leaf_accepts_every_job_height_boundary(#[case] segment_count: u32) {
        let total_cycles = if segment_count == 1 { 1 } else { 10 };
        let statement = leaf(
            job(segment_count, total_cycles),
            0,
            0,
            1,
            state(0),
            state(1),
        );
        assert_eq!(segment_circuit(&statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn maximum_padding_index_satisfies_height_thirty_two() {
        let job = job(u32::MAX, 10);
        let statement =
            SpanStatement::empty_leaf(job, u32::MAX).expect("the last u32 slot is suffix padding");
        assert_eq!(empty_circuit(&statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn maximum_cycle_endpoint_satisfies_u64_addition() {
        let job = job(2, u64::MAX);
        let statement = leaf(job, 1, u64::MAX - 1, 1, state(1), state(2));
        assert_eq!(segment_circuit(&statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn suffix_padding_leaf_satisfies_the_semantics_circuit() {
        let job = job(3, 12);
        let statement = SpanStatement::empty_leaf(job, 3).expect("slot three is padding");
        assert_eq!(empty_circuit(&statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn changed_parent_segment_count_is_rejected() {
        let (left, right, parent) = two_executed();
        let left = statement_words(&left).expect("left statement width is canonical");
        let right = statement_words(&right).expect("right statement width is canonical");
        let mut parent = statement_words(&parent).expect("parent statement width is canonical");
        parent[layout::EXECUTED_SEGMENT_COUNT_START] = M31Word::from(3);
        let zero = zero_words();
        let circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &zero,
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
        let zero = zero_words();
        let circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: false,
            binary_selector: true,
            empty_selector: false,
            segment: &zero,
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
        assert_ne!(tampered_fold_circuit(tamper).nonzero_output_count(), 0);
    }

    #[rstest]
    #[case::span_tag(LeafTamper::SpanTag)]
    #[case::initial_zero_register(LeafTamper::InitialZeroRegister)]
    #[case::zero_total_cycles(LeafTamper::ZeroTotalCycles)]
    #[case::zero_segment_count(LeafTamper::ZeroSegmentCount)]
    #[case::job_height(LeafTamper::JobHeight)]
    #[case::slot_height(LeafTamper::SlotHeight)]
    #[case::node_outside_capacity(LeafTamper::NodeOutsideCapacity)]
    #[case::first_segment(LeafTamper::FirstSegment)]
    #[case::segment_count(LeafTamper::SegmentCount)]
    #[case::zero_cycle_count(LeafTamper::ZeroCycleCount)]
    #[case::cycle_outside_job(LeafTamper::CycleOutsideJob)]
    #[case::cycle_overflow(LeafTamper::CycleOverflow)]
    #[case::initial_state(LeafTamper::InitialState)]
    #[case::final_state(LeafTamper::FinalState)]
    #[case::input_edge(LeafTamper::InputEdge)]
    #[case::output_edge(LeafTamper::OutputEdge)]
    #[case::empty_payload(LeafTamper::EmptyPayload)]
    #[case::empty_before_padding(LeafTamper::EmptyBeforePadding)]
    fn every_leaf_validity_boundary_rejects_substitution(#[case] tamper: LeafTamper) {
        assert_ne!(tampered_leaf_circuit(tamper).nonzero_output_count(), 0);
    }

    #[rstest]
    fn segment_transcript_statement_must_equal_the_parent_statement() {
        let job = job(3, 12);
        let statement = leaf(job, 1, 4, 4, state(1), state(2));
        let zero = zero_words();
        let segment = statement_words(&statement).expect("segment statement width is canonical");
        let mut parent = segment;
        parent[layout::PROTOCOL_START] = M31Word::from(99);
        let circuit = build_statement_semantics_circuit(StatementSemanticsCircuitWitness {
            segment_selector: true,
            binary_selector: false,
            empty_selector: false,
            segment: &segment,
            left: &zero,
            right: &zero,
            parent: &parent,
        });
        assert_ne!(circuit.nonzero_output_count(), 0);
    }

    #[rstest]
    fn inactive_reference_circuit_accepts_zero_padded_inputs() {
        assert_eq!(inactive_circuit().nonzero_output_count(), 0);
    }

    #[rstest]
    fn statement_circuit_structure_is_independent_of_the_universal_mode() {
        let job = job(3, 12);
        let segment = segment_circuit(&leaf(job, 1, 4, 4, state(1), state(2)));
        let empty =
            empty_circuit(&SpanStatement::empty_leaf(job, 3).expect("slot three is padding"));
        let circuits = [
            inactive_circuit(),
            binary_circuit(two_executed()),
            segment,
            empty,
        ];
        let shapes = circuits.map(|circuit| {
            let node_count = circuit.circuit().arena().nodes.len();
            (
                node_count,
                circuit.circuit().outputs().len(),
                circuit.input_bindings().len(),
            )
        });
        assert_eq!(shapes[1..], [shapes[0], shapes[0], shapes[0]]);
    }

    #[rstest]
    fn every_statement_word_has_one_fixed_circuit_input() {
        let circuit = binary_circuit(two_executed());
        let statement_inputs = circuit
            .input_bindings()
            .iter()
            .filter(|binding| {
                matches!(
                    binding.source,
                    StatementCircuitInputSource::StatementWord { .. }
                )
            })
            .count();
        assert_eq!(statement_inputs, 4 * SPAN_STATEMENT_CANONICAL_WORDS);
    }
}
