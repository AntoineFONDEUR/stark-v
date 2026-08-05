//! Fixed arithmetic semantics linking a VM claim to its segment statement.
//!
//! The circuit consumes every canonical claim word and a separately scoped
//! copy of the transcript-bound statement. It proves exact machine boundary
//! equality, canonical vector prefixes and lengths, mandatory Merkle roots,
//! zero journal state, and the M31 bounds needed by VM public LogUp tuples.
//! Its structure depends only on the verifier-owned claim capacity.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;

use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

use super::protocol::CanonicalTag;
use super::statement::{
    MACHINE_STATE_CANONICAL_WORDS, SPAN_STATEMENT_CANONICAL_WORDS,
    canonical_layout as statement_layout,
};
use super::statement_semantics_circuit::StatementWords;
use super::vm_public_claim::{
    VmPublicClaimShape, canonical_layout as claim_layout, canonical_vm_public_claim_word_kinds,
};

const U16_BASE: u32 = 1 << 16;
const U16_MAX: u32 = 0xffff;

/// Source relation of one fixed VM-claim semantic circuit input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmClaimCircuitInputSource {
    ClaimWord { index: u32 },
    StatementWord { index: u32 },
    IoDigestWord { io_kind: u32, limb: u32 },
    SegmentSelector,
    PrivateWitness,
}

/// Circuit input node and its exact AIR source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmClaimCircuitInputBinding {
    pub node_id: u32,
    pub source: VmClaimCircuitInputSource,
}

/// Fixed claim-to-statement circuit and all input ownership metadata.
#[derive(Debug)]
pub struct VmPublicClaimSemanticsCircuit {
    shape: VmPublicClaimShape,
    circuit: ConstraintCircuit,
    input_bindings: Vec<VmClaimCircuitInputBinding>,
}

impl VmPublicClaimSemanticsCircuit {
    pub const fn shape(&self) -> VmPublicClaimShape {
        self.shape
    }

    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[VmClaimCircuitInputBinding] {
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

    /// Returns the first violated zero-output constraint for diagnostics.
    pub fn first_nonzero_output(&self) -> Option<(usize, usize, SecureField)> {
        let arena = self.circuit.arena();
        self.circuit
            .outputs()
            .iter()
            .copied()
            .enumerate()
            .find_map(|(ordinal, node_id)| {
                let value = arena.nodes[node_id].value;
                (!value.is_zero()).then_some((ordinal, node_id, value))
            })
    }
}

/// Values for one universal claim-to-statement circuit instance.
pub struct VmPublicClaimSemanticsWitness<'a> {
    pub segment_selector: bool,
    pub claim_words: &'a [M31Word],
    pub statement_words: &'a StatementWords,
    pub input_digest: &'a [M31Word; 8],
    pub output_digest: &'a [M31Word; 8],
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<VmClaimCircuitInputBinding>,
    segment_selected: bool,
}

impl TrackedBuilder {
    fn new(segment_selected: bool) -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
            segment_selected,
        }
    }

    fn input(&mut self, source: VmClaimCircuitInputSource, value: u32) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value)));
        self.bindings.push(VmClaimCircuitInputBinding {
            node_id: u32::try_from(node_id).expect("VM claim circuit input count fits u32"),
            source,
        });
        value
    }

    fn private(&mut self, value: u32) -> Rec {
        self.input(
            VmClaimCircuitInputSource::PrivateWitness,
            if self.segment_selected { value } else { 0 },
        )
    }

    fn constrain(&mut self, gate: &Rec, constraint: Rec) {
        self.circuit.constrain_zero(gate.clone() * constraint);
    }

    fn finish(self, shape: VmPublicClaimShape) -> VmPublicClaimSemanticsCircuit {
        VmPublicClaimSemanticsCircuit {
            shape,
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

struct BoundWords {
    values: Vec<Rec>,
    raw: Vec<u32>,
}

impl BoundWords {
    fn claim(builder: &mut TrackedBuilder, words: &[M31Word]) -> Self {
        Self::new(builder, words, |index| {
            VmClaimCircuitInputSource::ClaimWord { index }
        })
    }

    fn statement(builder: &mut TrackedBuilder, words: &StatementWords) -> Self {
        Self::new(builder, words, |index| {
            VmClaimCircuitInputSource::StatementWord { index }
        })
    }

    fn io_digest(builder: &mut TrackedBuilder, io_kind: u32, words: &[M31Word; 8]) -> Self {
        Self::new(builder, words, |limb| {
            VmClaimCircuitInputSource::IoDigestWord { io_kind, limb }
        })
    }

    fn new(
        builder: &mut TrackedBuilder,
        words: &[M31Word],
        source: impl Fn(u32) -> VmClaimCircuitInputSource,
    ) -> Self {
        let values = words
            .iter()
            .copied()
            .enumerate()
            .map(|(index, word)| {
                let index = u32::try_from(index).expect("canonical word index fits u32");
                builder.input(source(index), word.as_u32())
            })
            .collect();
        Self {
            values,
            raw: words.iter().map(|word| word.as_u32()).collect(),
        }
    }

    fn value(&self, index: usize) -> Rec {
        self.values[index].clone()
    }

    fn raw(&self, index: usize) -> u32 {
        self.raw[index]
    }
}

/// Builds the fixed semantic circuit for one trusted claim capacity.
pub fn build_vm_public_claim_semantics_circuit(
    shape: VmPublicClaimShape,
    witness: VmPublicClaimSemanticsWitness<'_>,
) -> Result<VmPublicClaimSemanticsCircuit, VmPublicClaimSemanticsError> {
    let expected_claim_words = canonical_vm_public_claim_word_kinds(shape).len();
    if witness.claim_words.len() != expected_claim_words {
        return Err(VmPublicClaimSemanticsError::ClaimWordCountMismatch {
            expected: expected_claim_words,
            actual: witness.claim_words.len(),
        });
    }
    if witness.statement_words.len() != SPAN_STATEMENT_CANONICAL_WORDS {
        return Err(VmPublicClaimSemanticsError::StatementWordCountMismatch {
            expected: SPAN_STATEMENT_CANONICAL_WORDS,
            actual: witness.statement_words.len(),
        });
    }

    let mut builder = TrackedBuilder::new(witness.segment_selector);
    let segment = builder.input(
        VmClaimCircuitInputSource::SegmentSelector,
        u32::from(witness.segment_selector),
    );
    let one = constant(1);
    constrain_boolean(&mut builder, &one, &segment);
    let claim = BoundWords::claim(&mut builder, witness.claim_words);
    let statement = BoundWords::statement(&mut builder, witness.statement_words);
    let input_digest = BoundWords::io_digest(&mut builder, 0, witness.input_digest);
    let output_digest = BoundWords::io_digest(&mut builder, 1, witness.output_digest);

    constrain_roots_and_machine_state(&mut builder, &segment, &claim, &statement);
    constrain_vector_layout(
        &mut builder,
        &segment,
        shape,
        &claim,
        &statement,
        &input_digest,
        &output_digest,
    );
    constrain_relation_field_bounds(&mut builder, &segment, shape, &claim);
    Ok(builder.finish(shape))
}

fn constrain_roots_and_machine_state(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    claim: &BoundWords,
    statement: &BoundWords,
) {
    for present in [
        claim_layout::PROGRAM_ROOT_PRESENT,
        claim_layout::INITIAL_RW_ROOT_PRESENT,
        claim_layout::FINAL_RW_ROOT_PRESENT,
    ] {
        constrain_equal(builder, gate, claim.value(present), constant(1));
    }

    copy_range(
        builder,
        gate,
        claim,
        claim_layout::PROGRAM_ROOT_START,
        statement,
        statement_layout::PROGRAM_START,
        8,
    );
    constrain_machine_boundary(
        builder,
        gate,
        claim,
        claim_layout::INITIAL_PC_START,
        claim_layout::INITIAL_REGISTERS_START,
        claim_layout::INITIAL_RW_ROOT_START,
        statement,
        statement_layout::ENTRY_STATE_START,
    );
    constrain_machine_boundary(
        builder,
        gate,
        claim,
        claim_layout::FINAL_PC_START,
        claim_layout::FINAL_REGISTERS_START,
        claim_layout::FINAL_RW_ROOT_START,
        statement,
        statement_layout::EXIT_STATE_START,
    );
    copy_range(
        builder,
        gate,
        claim,
        claim_layout::CLOCK_START,
        statement,
        statement_layout::EXECUTED_CYCLE_COUNT_START,
        2,
    );
    constrain_zero(
        builder,
        gate,
        statement.value(statement_layout::EXECUTED_CYCLE_COUNT_START + 2),
    );
    constrain_zero(
        builder,
        gate,
        statement.value(statement_layout::EXECUTED_CYCLE_COUNT_START + 3),
    );
}

#[allow(clippy::too_many_arguments)]
fn constrain_machine_boundary(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    claim: &BoundWords,
    pc_start: usize,
    registers_start: usize,
    root_start: usize,
    statement: &BoundWords,
    state_start: usize,
) {
    copy_range(
        builder,
        gate,
        claim,
        pc_start,
        statement,
        state_start + statement_layout::MACHINE_STATE_PC_START_OFFSET,
        2,
    );
    copy_range(
        builder,
        gate,
        claim,
        registers_start,
        statement,
        state_start + statement_layout::MACHINE_STATE_REGISTERS_START_OFFSET,
        64,
    );
    copy_range(
        builder,
        gate,
        claim,
        root_start,
        statement,
        state_start + statement_layout::MACHINE_STATE_RW_DIGEST_START_OFFSET,
        8,
    );
    for offset in 0..8 {
        constrain_zero(
            builder,
            gate,
            statement.value(
                state_start + statement_layout::MACHINE_STATE_IO_DIGEST_START_OFFSET + offset,
            ),
        );
    }
    debug_assert_eq!(
        statement_layout::MACHINE_STATE_IO_DIGEST_START_OFFSET + 8,
        MACHINE_STATE_CANONICAL_WORDS
    );
}

fn constrain_vector_layout(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    shape: VmPublicClaimShape,
    claim: &BoundWords,
    statement: &BoundWords,
    input_digest: &BoundWords,
    output_digest: &BoundWords,
) {
    let input_flags = constrain_input_slots(builder, gate, shape, claim);
    let output_flags = constrain_output_slots(builder, gate, shape, claim);

    copy_range(
        builder,
        gate,
        claim,
        claim_layout::HEADER_OUTPUT_WORD_COUNT_START,
        claim,
        claim_layout::output_word_count_start(shape),
        2,
    );

    let input_present = edge_present(builder, gate, statement, statement_layout::INPUT_EDGE_TAG);
    for flag in &input_flags {
        builder.constrain(gate, flag.clone() * (constant(1) - input_present.clone()));
    }
    for offset in 0..2 {
        builder.constrain(
            gate,
            (constant(1) - input_present.clone())
                * claim.value(claim_layout::INPUT_LENGTH_START + offset),
        );
    }
    constrain_input_byte_length(builder, gate, claim, &input_flags);
    for limb in 0..8 {
        builder.constrain(
            gate,
            input_present.clone()
                * (input_digest.value(limb)
                    - statement.value(statement_layout::INPUT_EDGE_DIGEST_START + limb)),
        );
    }

    let output_present = edge_present(builder, gate, statement, statement_layout::OUTPUT_EDGE_TAG);
    let first_output = output_flags.first().cloned().unwrap_or_else(|| constant(0));
    constrain_equal(builder, gate, first_output, output_present.clone());
    for flag in &output_flags {
        builder.constrain(gate, flag.clone() * (constant(1) - output_present.clone()));
    }
    for offset in 0..2 {
        builder.constrain(
            gate,
            (constant(1) - output_present.clone())
                * claim.value(claim_layout::OUTPUT_LENGTH_START + offset),
        );
    }
    constrain_output_header_and_addresses(builder, gate, shape, claim, &output_flags);
    for limb in 0..8 {
        builder.constrain(
            gate,
            output_present.clone()
                * (output_digest.value(limb)
                    - statement.value(statement_layout::OUTPUT_EDGE_DIGEST_START + limb)),
        );
    }
}

fn constrain_input_slots(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    shape: VmPublicClaimShape,
    claim: &BoundWords,
) -> Vec<Rec> {
    let mut flags = Vec::with_capacity(shape.max_input_words() as usize);
    let mut previous = constant(1);
    let mut count = constant(0);
    for index in 0..shape.max_input_words() as usize {
        let flag = claim.value(claim_layout::input_slot_present(index));
        constrain_boolean(builder, gate, &flag);
        builder.constrain(gate, flag.clone() * (constant(1) - previous));
        for offset in 0..2 {
            builder.constrain(
                gate,
                (constant(1) - flag.clone())
                    * claim.value(claim_layout::input_slot_value_start(index) + offset),
            );
        }
        count += flag.clone();
        previous = flag.clone();
        flags.push(flag);
    }
    constrain_equal(
        builder,
        gate,
        compose_u32(claim, claim_layout::INPUT_WORD_COUNT_START),
        count,
    );
    flags
}

fn constrain_output_slots(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    shape: VmPublicClaimShape,
    claim: &BoundWords,
) -> Vec<Rec> {
    let mut flags = Vec::with_capacity(shape.max_output_words() as usize);
    let mut previous = constant(1);
    let mut count = constant(0);
    for index in 0..shape.max_output_words() as usize {
        let flag = claim.value(claim_layout::output_slot_present(shape, index));
        constrain_boolean(builder, gate, &flag);
        builder.constrain(gate, flag.clone() * (constant(1) - previous));
        for offset in 0..6 {
            builder.constrain(
                gate,
                (constant(1) - flag.clone())
                    * claim.value(claim_layout::output_slot_address_start(shape, index) + offset),
            );
        }
        count += flag.clone();
        previous = flag.clone();
        flags.push(flag);
    }
    constrain_equal(
        builder,
        gate,
        compose_u32(claim, claim_layout::output_word_count_start(shape)),
        count,
    );
    flags
}

fn constrain_input_byte_length(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    claim: &BoundWords,
    flags: &[Rec],
) {
    let count = compose_u32(claim, claim_layout::INPUT_WORD_COUNT_START);
    let length = compose_u32(claim, claim_layout::INPUT_LENGTH_START);
    let has_words = flags.first().cloned().unwrap_or_else(|| constant(0));
    let raw_count = raw_u32(claim, claim_layout::INPUT_WORD_COUNT_START);
    let raw_length = raw_u32(claim, claim_layout::INPUT_LENGTH_START);
    let raw_padding = if raw_count == 0 {
        0
    } else {
        raw_count.wrapping_mul(4).wrapping_sub(raw_length)
    };
    let padding_low = builder.private(raw_padding & 1);
    let padding_high = builder.private((raw_padding >> 1) & 1);
    constrain_boolean(builder, gate, &padding_low);
    constrain_boolean(builder, gate, &padding_high);
    builder.constrain(
        gate,
        (constant(1) - has_words.clone()) * padding_low.clone(),
    );
    builder.constrain(gate, (constant(1) - has_words) * padding_high.clone());
    let padding = padding_low + constant(2) * padding_high;
    builder.constrain(gate, length - constant(4) * count + padding);
}

fn constrain_output_header_and_addresses(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    shape: VmPublicClaimShape,
    claim: &BoundWords,
    flags: &[Rec],
) {
    if flags.is_empty() {
        return;
    }
    let header_len_bits = u32_bits(
        builder,
        gate,
        claim,
        claim_layout::OUTPUT_LENGTH_ADDRESS_START,
    );
    let first_address_start = claim_layout::output_slot_address_start(shape, 0);
    let first_address_bits = u32_bits(builder, gate, claim, first_address_start);
    let first_output_gate = gate.clone() * flags[0].clone();
    constrain_zero(builder, &first_output_gate, first_address_bits[0].clone());
    constrain_zero(builder, &first_output_gate, first_address_bits[1].clone());
    for bit in 2..32 {
        constrain_equal(
            builder,
            &first_output_gate,
            first_address_bits[bit].clone(),
            header_len_bits[bit].clone(),
        );
    }
    copy_range(
        builder,
        gate,
        claim,
        claim_layout::OUTPUT_LENGTH_START,
        claim,
        claim_layout::output_slot_value_start(shape, 0),
        2,
    );

    let data_address_bits = u32_bits(
        builder,
        gate,
        claim,
        claim_layout::OUTPUT_DATA_ADDRESS_START,
    );
    let offset = data_address_bits[0].clone() + constant(2) * data_address_bits[1].clone();
    let output_count = compose_u32(claim, claim_layout::output_word_count_start(shape));
    let data_count = output_count - constant(1);
    let output_length = compose_u32(claim, claim_layout::OUTPUT_LENGTH_START);
    let has_data = flags.get(1).cloned().unwrap_or_else(|| constant(0));
    let raw_count = raw_u32(claim, claim_layout::output_word_count_start(shape));
    let raw_length = raw_u32(claim, claim_layout::OUTPUT_LENGTH_START);
    let raw_offset = raw_u32(claim, claim_layout::OUTPUT_DATA_ADDRESS_START) & 3;
    let raw_padding = if raw_count <= 1 {
        0
    } else {
        (raw_count - 1)
            .wrapping_mul(4)
            .wrapping_sub(raw_length.wrapping_add(raw_offset))
    };
    let padding_low = builder.private(raw_padding & 1);
    let padding_high = builder.private((raw_padding >> 1) & 1);
    constrain_boolean(builder, gate, &padding_low);
    constrain_boolean(builder, gate, &padding_high);
    builder.constrain(gate, (constant(1) - has_data.clone()) * padding_low.clone());
    builder.constrain(
        gate,
        (constant(1) - has_data.clone()) * padding_high.clone(),
    );
    builder.constrain(
        gate,
        (constant(1) - has_data.clone()) * output_length.clone(),
    );
    let padding = padding_low + constant(2) * padding_high;
    builder.constrain(
        gate,
        has_data.clone() * (output_length + offset - constant(4) * data_count + padding),
    );

    let aligned_low = claim.value(claim_layout::OUTPUT_DATA_ADDRESS_START)
        - data_address_bits[0].clone()
        - constant(2) * data_address_bits[1].clone();
    let aligned_high = claim.value(claim_layout::OUTPUT_DATA_ADDRESS_START + 1);
    let raw_aligned = raw_u32(claim, claim_layout::OUTPUT_DATA_ADDRESS_START) & !3;
    for (index, flag) in flags.iter().enumerate().skip(1) {
        constrain_add_constant_u32(
            builder,
            &(gate.clone() * flag.clone()),
            [aligned_low.clone(), aligned_high.clone()],
            raw_aligned,
            u32::try_from((index - 1) * 4).expect("output shape offset fits u32"),
            [
                claim.value(claim_layout::output_slot_address_start(shape, index)),
                claim.value(claim_layout::output_slot_address_start(shape, index) + 1),
            ],
        );
    }
}

fn constrain_relation_field_bounds(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    shape: VmPublicClaimShape,
    claim: &BoundWords,
) {
    for start in [
        claim_layout::INITIAL_PC_START,
        claim_layout::FINAL_PC_START,
        claim_layout::CLOCK_START,
        claim_layout::INPUT_START_START,
        claim_layout::INPUT_WORD_COUNT_START,
        claim_layout::OUTPUT_LENGTH_ADDRESS_START,
        claim_layout::OUTPUT_DATA_ADDRESS_START,
        claim_layout::OUTPUT_LENGTH_START,
        claim_layout::HEADER_OUTPUT_WORD_COUNT_START,
        claim_layout::output_word_count_start(shape),
    ] {
        constrain_canonical_m31_u32(builder, gate, claim, start, false);
    }
    constrain_canonical_m31_u32(
        builder,
        gate,
        claim,
        claim_layout::INPUT_LENGTH_START,
        false,
    );
    let clock_bits = u32_bits(builder, gate, claim, claim_layout::CLOCK_START);
    reject_constant_bits(builder, gate, &clock_bits, 0x7fff_fffe);

    for register in 0..32 {
        let start = claim_layout::REGISTER_LAST_CLOCKS_START + register * 2;
        let last_clock_bits = constrain_canonical_m31_u32(builder, gate, claim, start, false);
        constrain_less_equal(builder, gate, &last_clock_bits, &clock_bits);
    }
    for index in 0..shape.max_output_words() as usize {
        let flag = claim.value(claim_layout::output_slot_present(shape, index));
        let address_bits = constrain_canonical_m31_u32(
            builder,
            &(gate.clone() * flag.clone()),
            claim,
            claim_layout::output_slot_address_start(shape, index),
            false,
        );
        let output_clock_bits = constrain_canonical_m31_u32(
            builder,
            &(gate.clone() * flag.clone()),
            claim,
            claim_layout::output_slot_clock_start(shape, index),
            false,
        );
        constrain_less_equal(
            builder,
            &(gate.clone() * flag),
            &output_clock_bits,
            &clock_bits,
        );
        let _ = address_bits;
    }
}

fn constrain_canonical_m31_u32(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &BoundWords,
    start: usize,
    reject_clock_max: bool,
) -> Vec<Rec> {
    let bits = u32_bits(builder, gate, words, start);
    constrain_zero(builder, gate, bits[31].clone());
    reject_constant_bits(builder, gate, &bits, 0x7fff_ffff);
    if reject_clock_max {
        reject_constant_bits(builder, gate, &bits, 0x7fff_fffe);
    }
    bits
}

fn u32_bits(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    words: &BoundWords,
    start: usize,
) -> Vec<Rec> {
    let raw = raw_u32(words, start);
    let mut bits = Vec::with_capacity(32);
    for limb in 0..2 {
        let limb_bits = (0..16)
            .map(|bit| {
                let value = builder.private((raw >> (limb * 16 + bit)) & 1);
                constrain_boolean(builder, gate, &value);
                value
            })
            .collect::<Vec<_>>();
        let reconstructed = limb_bits
            .iter()
            .enumerate()
            .fold(constant(0), |sum, (bit, value)| {
                sum + value.clone() * constant(1_u32 << bit)
            });
        constrain_equal(builder, gate, words.value(start + limb), reconstructed);
        bits.extend(limb_bits);
    }
    bits
}

fn reject_constant_bits(builder: &mut TrackedBuilder, gate: &Rec, bits: &[Rec], value: u32) {
    let equal = bits
        .iter()
        .enumerate()
        .fold(constant(1), |equal, (bit, actual)| {
            let expected = (value >> bit) & 1;
            equal
                * if expected == 1 {
                    actual.clone()
                } else {
                    constant(1) - actual.clone()
                }
        });
    constrain_zero(builder, gate, equal);
}

fn constrain_less_equal(builder: &mut TrackedBuilder, gate: &Rec, lhs: &[Rec], rhs: &[Rec]) {
    let less = less_than_bits(lhs, rhs);
    let equal = equal_bits(lhs, rhs);
    builder.constrain(gate, less + equal - constant(1));
}

fn less_than_bits(lhs: &[Rec], rhs: &[Rec]) -> Rec {
    let mut equal_above = constant(1);
    let mut less = constant(0);
    for (lhs, rhs) in lhs.iter().zip(rhs).rev() {
        less += equal_above.clone() * (constant(1) - lhs.clone()) * rhs.clone();
        let same =
            constant(1) - lhs.clone() - rhs.clone() + constant(2) * lhs.clone() * rhs.clone();
        equal_above *= same;
    }
    less
}

fn equal_bits(lhs: &[Rec], rhs: &[Rec]) -> Rec {
    lhs.iter().zip(rhs).fold(constant(1), |equal, (lhs, rhs)| {
        equal * (constant(1) - lhs.clone() - rhs.clone() + constant(2) * lhs.clone() * rhs.clone())
    })
}

fn edge_present(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    statement: &BoundWords,
    tag_index: usize,
) -> Rec {
    let actual = u32::from(statement.raw(tag_index) == CanonicalTag::PresentEdge.word().as_u32());
    let present = builder.private(actual);
    constrain_boolean(builder, gate, &present);
    let absent_tag = constant(CanonicalTag::AbsentEdge.word().as_u32());
    let present_tag = constant(CanonicalTag::PresentEdge.word().as_u32());
    builder.constrain(
        gate,
        statement.value(tag_index)
            - absent_tag.clone()
            - present.clone() * (present_tag - absent_tag),
    );
    present
}

fn constrain_add_constant_u32(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    input: [Rec; 2],
    raw_input: u32,
    addend: u32,
    output: [Rec; 2],
) {
    let expected = raw_input.checked_add(addend);
    let raw_output = expected.unwrap_or(0);
    let input_low = raw_input & U16_MAX;
    let add_low = addend & U16_MAX;
    let carry_value = u32::from(input_low + add_low >= U16_BASE);
    let carry = builder.private(carry_value);
    constrain_boolean(builder, gate, &carry);
    builder.constrain(
        gate,
        input[0].clone() + constant(add_low)
            - output[0].clone()
            - constant(U16_BASE) * carry.clone(),
    );
    builder.constrain(
        gate,
        input[1].clone() + constant(addend >> 16) + carry - output[1].clone(),
    );
    if expected.is_none() {
        builder.constrain(gate, constant(1));
    }
    debug_assert_eq!(
        raw_output,
        (raw_output & U16_MAX) | ((raw_output >> 16) << 16)
    );
}

fn compose_u32(words: &BoundWords, start: usize) -> Rec {
    words.value(start) + constant(U16_BASE) * words.value(start + 1)
}

fn raw_u32(words: &BoundWords, start: usize) -> u32 {
    words.raw(start) | (words.raw(start + 1) << 16)
}

#[allow(clippy::too_many_arguments)]
fn copy_range(
    builder: &mut TrackedBuilder,
    gate: &Rec,
    source: &BoundWords,
    source_start: usize,
    target: &BoundWords,
    target_start: usize,
    width: usize,
) {
    for offset in 0..width {
        constrain_equal(
            builder,
            gate,
            source.value(source_start + offset),
            target.value(target_start + offset),
        );
    }
}

fn constrain_equal(builder: &mut TrackedBuilder, gate: &Rec, lhs: Rec, rhs: Rec) {
    builder.constrain(gate, lhs - rhs);
}

fn constrain_zero(builder: &mut TrackedBuilder, gate: &Rec, value: Rec) {
    builder.constrain(gate, value);
}

fn constrain_boolean(builder: &mut TrackedBuilder, gate: &Rec, value: &Rec) {
    builder.constrain(gate, value.clone() * (constant(1) - value.clone()));
}

fn constant(value: u32) -> Rec {
    Rec::from(BaseField::from(value))
}

/// Invalid fixed circuit witness shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmPublicClaimSemanticsError {
    ClaimWordCountMismatch { expected: usize, actual: usize },
    StatementWordCountMismatch { expected: usize, actual: usize },
}

impl fmt::Display for VmPublicClaimSemanticsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ClaimWordCountMismatch { expected, actual } => write!(
                formatter,
                "VM claim semantic circuit has {actual} claim words, expected {expected}"
            ),
            Self::StatementWordCountMismatch { expected, actual } => write!(
                formatter,
                "VM claim semantic circuit has {actual} statement words, expected {expected}"
            ),
        }
    }
}

impl std::error::Error for VmPublicClaimSemanticsError {}

#[cfg(test)]
pub(crate) mod tests {
    use air::digest::{Digest8, IoDigest, MemoryDigest, ProgramDigest, ProtocolId};
    use rstest::rstest;

    use super::*;
    use crate::statement::{
        CompleteExecutionStatement, EdgeClaim, ExecutedSpan, JobContext, MachineState,
        SpanStatement,
    };
    use crate::statement_semantics_circuit::statement_words;
    use crate::vm_public_claim::tests::{public_data, shape};
    use crate::vm_public_claim::{
        canonical_vm_public_claim_words, public_input_digest, public_output_digest,
    };

    pub(crate) fn valid_words() -> (Vec<M31Word>, StatementWords) {
        let shape = shape();
        let claim = public_data();
        let zero_io = IoDigest::from(Digest8::new([M31Word::ZERO; 8]));
        let entry = MachineState::new(
            claim.initial_pc,
            claim.initial_regs,
            MemoryDigest::from(
                Digest8::try_from(claim.initial_rw_root.expect("fixture root is present"))
                    .expect("fixture root is canonical"),
            ),
            zero_io,
        )
        .expect("fixture entry state is canonical");
        let exit = MachineState::new(
            claim.final_pc,
            claim.final_regs,
            MemoryDigest::from(
                Digest8::try_from(claim.final_rw_root.expect("fixture root is present"))
                    .expect("fixture root is canonical"),
            ),
            zero_io,
        )
        .expect("fixture exit state is canonical");
        let input = public_input_digest(&claim.io_entries, shape)
            .expect("fixture input digest is canonical");
        let output = public_output_digest(&claim.io_entries, shape)
            .expect("fixture output digest is canonical");
        let complete = CompleteExecutionStatement::new(
            ProtocolId::from(Digest8::new([M31Word::from(9); 8])),
            ProgramDigest::from(
                Digest8::try_from(claim.program_root.expect("fixture root is present"))
                    .expect("fixture root is canonical"),
            ),
            entry,
            exit,
            input,
            output,
            u64::from(claim.clock),
        )
        .expect("fixture execution is nonempty");
        let job = JobContext::new(complete, 1).expect("fixture has one segment");
        let span = ExecutedSpan::new(
            0,
            1,
            0,
            u64::from(claim.clock),
            entry,
            exit,
            EdgeClaim::present(input),
            EdgeClaim::present(output),
        )
        .expect("fixture span is nonempty");
        let statement =
            SpanStatement::segment_leaf(job, 0, span).expect("fixture statement is a checked leaf");
        (
            canonical_vm_public_claim_words(&claim, shape).expect("fixture claim is canonical"),
            statement_words(&statement).expect("fixture statement width is canonical"),
        )
    }

    pub(crate) fn valid_digests() -> ([M31Word; 8], [M31Word; 8]) {
        let claim = public_data();
        (
            public_input_digest(&claim.io_entries, shape())
                .expect("fixture input digest is canonical")
                .into_digest()
                .into_words(),
            public_output_digest(&claim.io_entries, shape())
                .expect("fixture output digest is canonical")
                .into_digest()
                .into_words(),
        )
    }

    fn circuit(claim: &[M31Word], statement: &StatementWords) -> VmPublicClaimSemanticsCircuit {
        let (input_digest, output_digest) = valid_digests();
        build_vm_public_claim_semantics_circuit(
            shape(),
            VmPublicClaimSemanticsWitness {
                segment_selector: true,
                claim_words: claim,
                statement_words: statement,
                input_digest: &input_digest,
                output_digest: &output_digest,
            },
        )
        .expect("fixture word widths are fixed")
    }

    #[rstest]
    fn valid_vm_claim_matches_its_segment_statement() {
        let (claim, statement) = valid_words();
        assert_eq!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn program_root_substitution_fails() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::PROGRAM_ROOT_START] = M31Word::from(99);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn public_input_digest_substitution_fails() {
        let (claim, statement) = valid_words();
        let (mut input_digest, output_digest) = valid_digests();
        input_digest[0] = M31Word::try_from(input_digest[0].as_u32() + 1)
            .expect("tampered digest word remains canonical M31");
        let tampered = build_vm_public_claim_semantics_circuit(
            shape(),
            VmPublicClaimSemanticsWitness {
                segment_selector: true,
                claim_words: &claim,
                statement_words: &statement,
                input_digest: &input_digest,
                output_digest: &output_digest,
            },
        )
        .expect("fixture word widths are fixed");
        assert_ne!(tampered.nonzero_output_count(), 0);
    }

    #[rstest]
    fn public_output_digest_substitution_fails() {
        let (claim, statement) = valid_words();
        let (input_digest, mut output_digest) = valid_digests();
        output_digest[0] = M31Word::try_from(output_digest[0].as_u32() + 1)
            .expect("tampered digest word remains canonical M31");
        let tampered = build_vm_public_claim_semantics_circuit(
            shape(),
            VmPublicClaimSemanticsWitness {
                segment_selector: true,
                claim_words: &claim,
                statement_words: &statement,
                input_digest: &input_digest,
                output_digest: &output_digest,
            },
        )
        .expect("fixture word widths are fixed");
        assert_ne!(tampered.nonzero_output_count(), 0);
    }

    #[rstest]
    fn m31_modulus_pc_alias_fails_even_when_the_statement_matches() {
        let (mut claim, mut statement) = valid_words();
        claim[claim_layout::INITIAL_PC_START] = M31Word::from(u16::MAX);
        claim[claim_layout::INITIAL_PC_START + 1] = M31Word::from(0x7fff_u16);
        let entry_pc =
            statement_layout::ENTRY_STATE_START + statement_layout::MACHINE_STATE_PC_START_OFFSET;
        statement[entry_pc] = M31Word::from(u16::MAX);
        statement[entry_pc + 1] = M31Word::from(0x7fff_u16);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn final_clock_alias_at_m31_modulus_fails() {
        let (mut claim, mut statement) = valid_words();
        claim[claim_layout::CLOCK_START] = M31Word::from(u16::MAX - 1);
        claim[claim_layout::CLOCK_START + 1] = M31Word::from(0x7fff_u16);
        statement[statement_layout::EXECUTED_CYCLE_COUNT_START] = M31Word::from(u16::MAX - 1);
        statement[statement_layout::EXECUTED_CYCLE_COUNT_START + 1] = M31Word::from(0x7fff_u16);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn register_access_after_segment_end_fails() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::REGISTER_LAST_CLOCKS_START + 2] = M31Word::from(9);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn non_prefix_input_slots_fail() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::input_slot_present(1)] = M31Word::ZERO;
        claim[claim_layout::input_slot_value_start(1)] = M31Word::ZERO;
        claim[claim_layout::input_slot_value_start(1) + 1] = M31Word::ZERO;
        claim[claim_layout::input_slot_present(2)] = M31Word::from(1);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn inactive_input_slot_data_fails() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::input_slot_value_start(2)] = M31Word::from(1);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn absent_program_root_fails() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::PROGRAM_ROOT_PRESENT] = M31Word::ZERO;
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn nonzero_statement_journal_state_fails() {
        let (claim, mut statement) = valid_words();
        statement[statement_layout::ENTRY_STATE_START
            + statement_layout::MACHINE_STATE_IO_DIGEST_START_OFFSET] = M31Word::from(1);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn malformed_output_data_address_sequence_fails() {
        let (mut claim, statement) = valid_words();
        let address = claim_layout::output_slot_address_start(shape(), 1);
        claim[address] = M31Word::try_from(claim[address].as_u32() + 4)
            .expect("tampered fixture address remains canonical M31");
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn output_vector_length_disagrees_with_byte_length_fails() {
        let (mut claim, statement) = valid_words();
        claim[claim_layout::OUTPUT_LENGTH_START] = M31Word::from(8);
        assert_ne!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn absent_output_allows_runner_header_addresses_without_output_slots() {
        let (mut claim, mut statement) = valid_words();
        claim[claim_layout::OUTPUT_LENGTH_START] = M31Word::ZERO;
        claim[claim_layout::OUTPUT_LENGTH_START + 1] = M31Word::ZERO;
        claim[claim_layout::HEADER_OUTPUT_WORD_COUNT_START] = M31Word::ZERO;
        claim[claim_layout::HEADER_OUTPUT_WORD_COUNT_START + 1] = M31Word::ZERO;
        let output_count = claim_layout::output_word_count_start(shape());
        claim[output_count] = M31Word::ZERO;
        claim[output_count + 1] = M31Word::ZERO;
        let output_slots = claim_layout::output_slots_start(shape());
        claim[output_slots..].fill(M31Word::ZERO);
        statement[statement_layout::OUTPUT_EDGE_TAG] = CanonicalTag::AbsentEdge.word();
        statement[statement_layout::OUTPUT_EDGE_DIGEST_START..][..8].fill(M31Word::ZERO);
        assert_eq!(circuit(&claim, &statement).nonzero_output_count(), 0);
    }

    #[rstest]
    fn inactive_mode_has_the_same_circuit_structure() {
        let (claim, statement) = valid_words();
        let active = circuit(&claim, &statement);
        let zero_claim = vec![M31Word::ZERO; claim.len()];
        let zero_statement = [M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS];
        let zero_digest = [M31Word::ZERO; 8];
        let inactive = build_vm_public_claim_semantics_circuit(
            shape(),
            VmPublicClaimSemanticsWitness {
                segment_selector: false,
                claim_words: &zero_claim,
                statement_words: &zero_statement,
                input_digest: &zero_digest,
                output_digest: &zero_digest,
            },
        )
        .expect("fixture word widths are fixed");
        assert_eq!(
            (active.input_bindings(), active.circuit().outputs()),
            (inactive.input_bindings(), inactive.circuit().outputs())
        );
    }
}
