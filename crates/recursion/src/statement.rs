//! Pure statement geometry for the recursion binary induction.
//!
//! A job fixes the complete execution claim plus the prover's internal
//! segment count and its unique minimal tree height. Height-zero statements
//! classify each slot as executed or padding. Binary folds preserve exact
//! slot, segment, cycle, machine-state, and edge-IO continuity.

use core::fmt;
use core::num::{NonZeroU32, NonZeroU64};

use air::digest::{Digest8, IoDigest, M31Word, MemoryDigest, ProgramDigest, ProtocolId};

use super::protocol::{CanonicalTag, CanonicalWords};

const MAX_SLOT_HEIGHT: u8 = 32;
const SLOT_BOUND: u64 = 1_u64 << MAX_SLOT_HEIGHT;

pub const MACHINE_STATE_CANONICAL_WORDS: usize = 1 + 2 + 32 * 2 + 8 + 8;
pub const COMPLETE_EXECUTION_CANONICAL_WORDS: usize =
    1 + 8 + 8 + 2 * MACHINE_STATE_CANONICAL_WORDS + 8 + 8 + 4;
pub const JOB_CONTEXT_CANONICAL_WORDS: usize = 1 + COMPLETE_EXECUTION_CANONICAL_WORDS + 2 + 1;
pub const SLOT_SPAN_CANONICAL_WORDS: usize = 1 + 4 + 1;
pub const EDGE_CLAIM_CANONICAL_WORDS: usize = 1 + 8;
pub const EXECUTED_SPAN_CANONICAL_WORDS: usize =
    1 + 2 + 2 + 4 + 4 + 2 * MACHINE_STATE_CANONICAL_WORDS + 2 * EDGE_CLAIM_CANONICAL_WORDS;
pub const SPAN_BODY_CANONICAL_WORDS: usize = 1 + EXECUTED_SPAN_CANONICAL_WORDS;
pub const SPAN_STATEMENT_CANONICAL_WORDS: usize =
    1 + JOB_CONTEXT_CANONICAL_WORDS + SLOT_SPAN_CANONICAL_WORDS + SPAN_BODY_CANONICAL_WORDS;

/// Word offsets in [`SpanStatement::canonical_words`].
pub mod canonical_layout {
    use super::{
        JOB_CONTEXT_CANONICAL_WORDS, MACHINE_STATE_CANONICAL_WORDS, SLOT_SPAN_CANONICAL_WORDS,
        SPAN_STATEMENT_CANONICAL_WORDS,
    };

    pub const SPAN_TAG: usize = 0;
    pub const JOB_START: usize = SPAN_TAG + 1;
    pub const JOB_TAG: usize = JOB_START;
    pub const COMPLETE_START: usize = JOB_TAG + 1;
    pub const COMPLETE_TAG: usize = COMPLETE_START;
    pub const PROTOCOL_START: usize = COMPLETE_TAG + 1;
    pub const PROGRAM_START: usize = PROTOCOL_START + 8;
    pub const INITIAL_STATE_START: usize = PROGRAM_START + 8;
    pub const FINAL_STATE_START: usize = INITIAL_STATE_START + MACHINE_STATE_CANONICAL_WORDS;
    pub const PUBLIC_INPUT_START: usize = FINAL_STATE_START + MACHINE_STATE_CANONICAL_WORDS;
    pub const PUBLIC_OUTPUT_START: usize = PUBLIC_INPUT_START + 8;
    pub const TOTAL_CYCLES_START: usize = PUBLIC_OUTPUT_START + 8;
    pub const JOB_SEGMENT_COUNT_START: usize = TOTAL_CYCLES_START + 4;
    pub const JOB_SLOT_HEIGHT: usize = JOB_SEGMENT_COUNT_START + 2;

    pub const SLOT_START: usize = JOB_START + JOB_CONTEXT_CANONICAL_WORDS;
    pub const SLOT_TAG: usize = SLOT_START;
    pub const SLOT_NODE_INDEX_START: usize = SLOT_TAG + 1;
    pub const SLOT_HEIGHT: usize = SLOT_NODE_INDEX_START + 4;

    pub const BODY_START: usize = SLOT_START + SLOT_SPAN_CANONICAL_WORDS;
    pub const BODY_TAG: usize = BODY_START;
    pub const EXECUTED_START: usize = BODY_TAG + 1;
    pub const EXECUTED_TAG: usize = EXECUTED_START;
    pub const FIRST_SEGMENT_START: usize = EXECUTED_TAG + 1;
    pub const EXECUTED_SEGMENT_COUNT_START: usize = FIRST_SEGMENT_START + 2;
    pub const FIRST_CYCLE_START: usize = EXECUTED_SEGMENT_COUNT_START + 2;
    pub const EXECUTED_CYCLE_COUNT_START: usize = FIRST_CYCLE_START + 4;
    pub const ENTRY_STATE_START: usize = EXECUTED_CYCLE_COUNT_START + 4;
    pub const EXIT_STATE_START: usize = ENTRY_STATE_START + MACHINE_STATE_CANONICAL_WORDS;
    pub const INPUT_EDGE_START: usize = EXIT_STATE_START + MACHINE_STATE_CANONICAL_WORDS;
    pub const INPUT_EDGE_TAG: usize = INPUT_EDGE_START;
    pub const INPUT_EDGE_DIGEST_START: usize = INPUT_EDGE_TAG + 1;
    pub const OUTPUT_EDGE_START: usize = INPUT_EDGE_DIGEST_START + 8;
    pub const OUTPUT_EDGE_TAG: usize = OUTPUT_EDGE_START;
    pub const OUTPUT_EDGE_DIGEST_START: usize = OUTPUT_EDGE_TAG + 1;

    pub const MACHINE_STATE_TAG_OFFSET: usize = 0;
    pub const MACHINE_STATE_PC_START_OFFSET: usize = MACHINE_STATE_TAG_OFFSET + 1;
    pub const MACHINE_STATE_REGISTERS_START_OFFSET: usize = MACHINE_STATE_PC_START_OFFSET + 2;
    pub const MACHINE_STATE_RW_DIGEST_START_OFFSET: usize =
        MACHINE_STATE_REGISTERS_START_OFFSET + 64;
    pub const MACHINE_STATE_IO_DIGEST_START_OFFSET: usize =
        MACHINE_STATE_RW_DIGEST_START_OFFSET + 8;

    const MACHINE_STATE_STARTS: [usize; 4] = [
        INITIAL_STATE_START,
        FINAL_STATE_START,
        ENTRY_STATE_START,
        EXIT_STATE_START,
    ];

    /// Whether a word is a raw 16-bit limb or a smaller integer field.
    pub fn is_integer_word(index: usize) -> bool {
        let in_machine_state = MACHINE_STATE_STARTS.iter().any(|start| {
            (*start + MACHINE_STATE_PC_START_OFFSET..*start + MACHINE_STATE_RW_DIGEST_START_OFFSET)
                .contains(&index)
        });
        in_machine_state
            || (TOTAL_CYCLES_START..TOTAL_CYCLES_START + 4).contains(&index)
            || (JOB_SEGMENT_COUNT_START..JOB_SEGMENT_COUNT_START + 2).contains(&index)
            || index == JOB_SLOT_HEIGHT
            || (SLOT_NODE_INDEX_START..SLOT_NODE_INDEX_START + 4).contains(&index)
            || index == SLOT_HEIGHT
            || (FIRST_SEGMENT_START..FIRST_SEGMENT_START + 2).contains(&index)
            || (EXECUTED_SEGMENT_COUNT_START..EXECUTED_SEGMENT_COUNT_START + 2).contains(&index)
            || (FIRST_CYCLE_START..FIRST_CYCLE_START + 4).contains(&index)
            || (EXECUTED_CYCLE_COUNT_START..EXECUTED_CYCLE_COUNT_START + 4).contains(&index)
    }

    const _: () = assert!(OUTPUT_EDGE_DIGEST_START + 8 == SPAN_STATEMENT_CANONICAL_WORDS);
}

/// Complete machine state at one segment boundary.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct MachineState {
    pc: u32,
    registers: [u32; 32],
    rw_memory: MemoryDigest,
    public_io_state: IoDigest,
}

impl MachineState {
    /// Constructs a state whose immutable zero register is canonical.
    pub fn new(
        pc: u32,
        registers: [u32; 32],
        rw_memory: MemoryDigest,
        public_io_state: IoDigest,
    ) -> Result<Self, StatementError> {
        if registers[0] != 0 {
            return Err(StatementError::ZeroRegisterIsNonZero);
        }
        Ok(Self {
            pc,
            registers,
            rw_memory,
            public_io_state,
        })
    }

    pub const fn pc(&self) -> u32 {
        self.pc
    }

    pub const fn registers(&self) -> &[u32; 32] {
        &self.registers
    }

    pub const fn rw_memory(&self) -> MemoryDigest {
        self.rw_memory
    }

    pub const fn public_io_state(&self) -> IoDigest {
        self.public_io_state
    }
}

/// Application-supplied execution claim. Segmentation is deliberately absent.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct CompleteExecutionStatement {
    protocol: ProtocolId,
    program: ProgramDigest,
    initial_state: MachineState,
    final_state: MachineState,
    public_input: IoDigest,
    public_output: IoDigest,
    total_cycles: NonZeroU64,
}

impl CompleteExecutionStatement {
    pub fn new(
        protocol: ProtocolId,
        program: ProgramDigest,
        initial_state: MachineState,
        final_state: MachineState,
        public_input: IoDigest,
        public_output: IoDigest,
        total_cycles: u64,
    ) -> Result<Self, StatementError> {
        let total_cycles = NonZeroU64::new(total_cycles).ok_or(StatementError::ZeroTotalCycles)?;
        Ok(Self {
            protocol,
            program,
            initial_state,
            final_state,
            public_input,
            public_output,
            total_cycles,
        })
    }

    pub const fn protocol(&self) -> ProtocolId {
        self.protocol
    }

    pub const fn program(&self) -> ProgramDigest {
        self.program
    }

    pub const fn initial_state(&self) -> MachineState {
        self.initial_state
    }

    pub const fn final_state(&self) -> MachineState {
        self.final_state
    }

    pub const fn public_input(&self) -> IoDigest {
        self.public_input
    }

    pub const fn public_output(&self) -> IoDigest {
        self.public_output
    }

    pub const fn total_cycles(&self) -> u64 {
        self.total_cycles.get()
    }
}

/// Internal recursion metadata bound to one complete execution.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct JobContext {
    complete: CompleteExecutionStatement,
    segment_count: NonZeroU32,
    slot_height: u8,
}

impl JobContext {
    /// Derives the unique minimal binary-tree height from the segment count.
    pub fn new(
        complete: CompleteExecutionStatement,
        segment_count: u32,
    ) -> Result<Self, StatementError> {
        let segment_count =
            NonZeroU32::new(segment_count).ok_or(StatementError::ZeroSegmentCount)?;
        let slot_height = ceil_log2(segment_count.get());
        Ok(Self {
            complete,
            segment_count,
            slot_height,
        })
    }

    pub const fn complete(&self) -> &CompleteExecutionStatement {
        &self.complete
    }

    pub const fn segment_count(&self) -> u32 {
        self.segment_count.get()
    }

    pub const fn total_cycles(&self) -> u64 {
        self.complete.total_cycles()
    }

    pub const fn slot_height(&self) -> u8 {
        self.slot_height
    }

    pub const fn slot_capacity(&self) -> u64 {
        1_u64 << self.slot_height
    }
}

/// One aligned power-of-two slot range in the canonical binary tree.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SlotSpan {
    first: u64,
    height: u8,
}

impl SlotSpan {
    pub fn new(first: u64, height: u8) -> Result<Self, StatementError> {
        if height > MAX_SLOT_HEIGHT {
            return Err(StatementError::SlotHeightOutOfRange);
        }
        let capacity = 1_u64 << height;
        let end = first
            .checked_add(capacity)
            .ok_or(StatementError::SlotRangeOverflow)?;
        if end > SLOT_BOUND {
            return Err(StatementError::SlotRangeOverflow);
        }
        Ok(Self { first, height })
    }

    pub const fn first(&self) -> u64 {
        self.first
    }

    pub const fn height(&self) -> u8 {
        self.height
    }

    /// Position among spans at this height.
    pub const fn node_index(&self) -> u64 {
        self.first >> self.height
    }

    pub const fn capacity(&self) -> u64 {
        1_u64 << self.height
    }

    pub const fn end_exclusive(&self) -> u64 {
        self.first + self.capacity()
    }
}

/// Public IO present at an outer execution edge or absent at an interior edge.
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq)]
pub struct EdgeClaim {
    digest: Option<IoDigest>,
}

impl EdgeClaim {
    pub const fn absent() -> Self {
        Self { digest: None }
    }

    pub const fn present(digest: IoDigest) -> Self {
        Self {
            digest: Some(digest),
        }
    }

    pub const fn digest(&self) -> Option<IoDigest> {
        self.digest
    }

    pub const fn is_absent(&self) -> bool {
        self.digest.is_none()
    }
}

/// Real execution covered by one statement.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct ExecutedSpan {
    first_segment: u32,
    segment_count: NonZeroU32,
    first_cycle: u64,
    cycle_count: NonZeroU64,
    entry: MachineState,
    exit: MachineState,
    input: EdgeClaim,
    output: EdgeClaim,
}

impl ExecutedSpan {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        first_segment: u32,
        segment_count: u32,
        first_cycle: u64,
        cycle_count: u64,
        entry: MachineState,
        exit: MachineState,
        input: EdgeClaim,
        output: EdgeClaim,
    ) -> Result<Self, StatementError> {
        let segment_count =
            NonZeroU32::new(segment_count).ok_or(StatementError::ZeroExecutedSegments)?;
        let cycle_count = NonZeroU64::new(cycle_count).ok_or(StatementError::ZeroExecutedCycles)?;
        first_segment
            .checked_add(segment_count.get())
            .ok_or(StatementError::SegmentRangeOverflow)?;
        first_cycle
            .checked_add(cycle_count.get())
            .ok_or(StatementError::CycleRangeOverflow)?;
        Ok(Self {
            first_segment,
            segment_count,
            first_cycle,
            cycle_count,
            entry,
            exit,
            input,
            output,
        })
    }

    pub const fn first_segment(&self) -> u32 {
        self.first_segment
    }

    pub const fn segment_count(&self) -> u32 {
        self.segment_count.get()
    }

    pub const fn end_segment(&self) -> u32 {
        self.first_segment + self.segment_count.get()
    }

    pub const fn first_cycle(&self) -> u64 {
        self.first_cycle
    }

    pub const fn cycle_count(&self) -> u64 {
        self.cycle_count.get()
    }

    pub const fn end_cycle(&self) -> u64 {
        self.first_cycle + self.cycle_count.get()
    }

    pub const fn entry(&self) -> MachineState {
        self.entry
    }

    pub const fn exit(&self) -> MachineState {
        self.exit
    }

    pub const fn input(&self) -> EdgeClaim {
        self.input
    }

    pub const fn output(&self) -> EdgeClaim {
        self.output
    }
}

/// Executed prefix or canonical empty padding for one slot range.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SpanBody {
    executed: Option<ExecutedSpan>,
}

impl SpanBody {
    pub const fn empty() -> Self {
        Self { executed: None }
    }

    pub const fn executed(span: ExecutedSpan) -> Self {
        Self {
            executed: Some(span),
        }
    }

    pub const fn is_empty(&self) -> bool {
        self.executed.is_none()
    }

    pub const fn executed_span(&self) -> Option<&ExecutedSpan> {
        self.executed.as_ref()
    }
}

/// One inductive statement over a canonical slot range.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct SpanStatement {
    job: JobContext,
    slots: SlotSpan,
    body: SpanBody,
}

impl SpanStatement {
    pub fn new(job: JobContext, slots: SlotSpan, body: SpanBody) -> Result<Self, StatementError> {
        validate_slots(&job, slots)?;
        match body.executed {
            None => validate_empty(&job, slots)?,
            Some(span) => validate_executed(&job, slots, &span)?,
        }
        Ok(Self { job, slots, body })
    }

    pub fn segment_leaf(
        job: JobContext,
        index: u32,
        span: ExecutedSpan,
    ) -> Result<Self, StatementError> {
        let slots = SlotSpan::new(u64::from(index), 0)?;
        Self::new(job, slots, SpanBody::executed(span))
    }

    pub fn empty_leaf(job: JobContext, index: u32) -> Result<Self, StatementError> {
        let slots = SlotSpan::new(u64::from(index), 0)?;
        Self::new(job, slots, SpanBody::empty())
    }

    pub fn fold(left: &Self, right: &Self) -> Result<Self, StatementError> {
        if left.job != right.job {
            return Err(StatementError::JobMismatch);
        }
        if left.slots.height != right.slots.height {
            return Err(StatementError::ChildHeightMismatch);
        }
        if left.slots.end_exclusive() != right.slots.first {
            return Err(StatementError::SlotsNotAdjacent);
        }

        let parent_height = left
            .slots
            .height
            .checked_add(1)
            .ok_or(StatementError::SlotHeightOutOfRange)?;
        let parent_slots = SlotSpan::new(left.slots.first, parent_height)?;
        if parent_slots.first % parent_slots.capacity() != 0 {
            return Err(StatementError::SlotsMisaligned);
        }

        let body = match (left.body.executed, right.body.executed) {
            (Some(left_span), Some(right_span)) => {
                SpanBody::executed(fold_executed(left_span, right_span)?)
            }
            (Some(span), None) => SpanBody::executed(span),
            (None, None) => SpanBody::empty(),
            (None, Some(_)) => {
                return Err(StatementError::EmptyBeforeExecuted);
            }
        };
        Self::new(left.job, parent_slots, body)
    }

    pub const fn job(&self) -> &JobContext {
        &self.job
    }

    pub const fn slots(&self) -> SlotSpan {
        self.slots
    }

    pub const fn body(&self) -> &SpanBody {
        &self.body
    }
}

/// Canonical internal root for one complete execution statement.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct RootStatement {
    statement: SpanStatement,
}

impl RootStatement {
    pub fn new(statement: SpanStatement) -> Result<Self, StatementError> {
        let job = statement.job;
        if statement.slots.first != 0 {
            return Err(StatementError::RootSlotStartMismatch);
        }
        if statement.slots.height != job.slot_height {
            return Err(StatementError::RootHeightNotMinimal);
        }
        let span = statement
            .body
            .executed_span()
            .ok_or(StatementError::RootIsEmpty)?;
        if span.first_segment != 0 {
            return Err(StatementError::RootSegmentStartMismatch);
        }
        if span.segment_count.get() != job.segment_count.get() {
            return Err(StatementError::RootSegmentCountMismatch);
        }
        if span.first_cycle != 0 {
            return Err(StatementError::RootCycleStartMismatch);
        }
        if span.cycle_count.get() != job.total_cycles() {
            return Err(StatementError::RootCycleCountMismatch);
        }
        if span.entry != job.complete.initial_state {
            return Err(StatementError::RootInitialStateMismatch);
        }
        if span.exit != job.complete.final_state {
            return Err(StatementError::RootFinalStateMismatch);
        }
        if span.input.digest != Some(job.complete.public_input) {
            return Err(StatementError::RootInputMismatch);
        }
        if span.output.digest != Some(job.complete.public_output) {
            return Err(StatementError::RootOutputMismatch);
        }
        Ok(Self { statement })
    }

    pub const fn statement(&self) -> &SpanStatement {
        &self.statement
    }

    pub const fn complete_execution(&self) -> &CompleteExecutionStatement {
        &self.statement.job.complete
    }
}

fn validate_slots(job: &JobContext, slots: SlotSpan) -> Result<(), StatementError> {
    if !slots.first.is_multiple_of(slots.capacity()) {
        return Err(StatementError::SlotsMisaligned);
    }
    if slots.end_exclusive() > job.slot_capacity() {
        return Err(StatementError::SlotsOutsideJob);
    }
    Ok(())
}

fn validate_empty(job: &JobContext, slots: SlotSpan) -> Result<(), StatementError> {
    if slots.first < u64::from(job.segment_count.get()) {
        return Err(StatementError::InteriorEmptySpan);
    }
    Ok(())
}

fn validate_executed(
    job: &JobContext,
    slots: SlotSpan,
    span: &ExecutedSpan,
) -> Result<(), StatementError> {
    let job_segments = u64::from(job.segment_count.get());
    if slots.first >= job_segments {
        return Err(StatementError::ExecutedPaddingSpan);
    }
    if u64::from(span.first_segment) != slots.first {
        return Err(StatementError::ExecutedSlotStartMismatch);
    }
    let expected_end = slots.end_exclusive().min(job_segments);
    if u64::from(span.end_segment()) != expected_end {
        return Err(StatementError::ExecutedSlotCoverageMismatch);
    }
    if span.end_cycle() > job.total_cycles() {
        return Err(StatementError::ExecutedCyclesOutsideJob);
    }

    if span.first_segment == 0 {
        if span.first_cycle != 0 {
            return Err(StatementError::InitialCycleMismatch);
        }
        if span.entry != job.complete.initial_state {
            return Err(StatementError::InitialStateMismatch);
        }
        if span.input.digest != Some(job.complete.public_input) {
            return Err(StatementError::InputMismatch);
        }
    } else if !span.input.is_absent() {
        return Err(StatementError::InputMismatch);
    }

    if span.end_segment() == job.segment_count.get() {
        if span.end_cycle() != job.total_cycles() {
            return Err(StatementError::FinalCycleMismatch);
        }
        if span.exit != job.complete.final_state {
            return Err(StatementError::FinalStateMismatch);
        }
        if span.output.digest != Some(job.complete.public_output) {
            return Err(StatementError::OutputMismatch);
        }
    } else if !span.output.is_absent() {
        return Err(StatementError::OutputMismatch);
    }
    Ok(())
}

fn fold_executed(left: ExecutedSpan, right: ExecutedSpan) -> Result<ExecutedSpan, StatementError> {
    if left.end_segment() != right.first_segment {
        return Err(StatementError::SegmentDiscontinuity);
    }
    if left.end_cycle() != right.first_cycle {
        return Err(StatementError::CycleDiscontinuity);
    }
    if left.exit != right.entry {
        return Err(StatementError::StateDiscontinuity);
    }
    if !left.output.is_absent() {
        return Err(StatementError::LeftOutputPresent);
    }
    if !right.input.is_absent() {
        return Err(StatementError::RightInputPresent);
    }
    let segment_count = left
        .segment_count
        .get()
        .checked_add(right.segment_count.get())
        .ok_or(StatementError::SegmentRangeOverflow)?;
    let cycle_count = left
        .cycle_count
        .get()
        .checked_add(right.cycle_count.get())
        .ok_or(StatementError::CycleRangeOverflow)?;
    ExecutedSpan::new(
        left.first_segment,
        segment_count,
        left.first_cycle,
        cycle_count,
        left.entry,
        right.exit,
        left.input,
        right.output,
    )
}

fn append_raw_u32(output: &mut Vec<M31Word>, value: u32) {
    output.extend([
        M31Word::from((value & 0xffff) as u16),
        M31Word::from((value >> 16) as u16),
    ]);
}

fn append_raw_u64(output: &mut Vec<M31Word>, value: u64) {
    output.extend([
        M31Word::from((value & 0xffff) as u16),
        M31Word::from(((value >> 16) & 0xffff) as u16),
        M31Word::from(((value >> 32) & 0xffff) as u16),
        M31Word::from((value >> 48) as u16),
    ]);
}

fn append_digest(output: &mut Vec<M31Word>, digest: Digest8) {
    output.extend(digest.into_words());
}

impl CanonicalWords for MachineState {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::MachineState.word());
        append_raw_u32(output, self.pc);
        for register in self.registers {
            append_raw_u32(output, register);
        }
        append_digest(output, self.rw_memory.into_digest());
        append_digest(output, self.public_io_state.into_digest());
    }
}

impl CanonicalWords for CompleteExecutionStatement {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::CompleteExecution.word());
        append_digest(output, self.protocol.into_digest());
        append_digest(output, self.program.into_digest());
        self.initial_state.append_canonical_words(output);
        self.final_state.append_canonical_words(output);
        append_digest(output, self.public_input.into_digest());
        append_digest(output, self.public_output.into_digest());
        append_raw_u64(output, self.total_cycles.get());
    }
}

impl CanonicalWords for JobContext {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::JobContext.word());
        self.complete.append_canonical_words(output);
        append_raw_u32(output, self.segment_count.get());
        output.push(M31Word::from(self.slot_height as u16));
    }
}

impl CanonicalWords for SlotSpan {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::SlotSpan.word());
        append_raw_u64(output, self.node_index());
        output.push(M31Word::from(self.height as u16));
    }
}

impl CanonicalWords for EdgeClaim {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        match self.digest {
            None => {
                output.push(CanonicalTag::AbsentEdge.word());
                output.extend([M31Word::ZERO; 8]);
            }
            Some(digest) => {
                output.push(CanonicalTag::PresentEdge.word());
                append_digest(output, digest.into_digest());
            }
        }
    }
}

impl CanonicalWords for ExecutedSpan {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::ExecutedSpan.word());
        append_raw_u32(output, self.first_segment);
        append_raw_u32(output, self.segment_count.get());
        append_raw_u64(output, self.first_cycle);
        append_raw_u64(output, self.cycle_count.get());
        self.entry.append_canonical_words(output);
        self.exit.append_canonical_words(output);
        self.input.append_canonical_words(output);
        self.output.append_canonical_words(output);
    }
}

impl CanonicalWords for SpanBody {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        match self.executed {
            None => {
                output.push(CanonicalTag::EmptyBody.word());
                output.extend([M31Word::ZERO; EXECUTED_SPAN_CANONICAL_WORDS]);
            }
            Some(span) => {
                output.push(CanonicalTag::ExecutedBody.word());
                span.append_canonical_words(output);
            }
        }
    }
}

impl CanonicalWords for SpanStatement {
    fn append_canonical_words(&self, output: &mut Vec<M31Word>) {
        output.push(CanonicalTag::SpanStatement.word());
        self.job.append_canonical_words(output);
        self.slots.append_canonical_words(output);
        self.body.append_canonical_words(output);
    }
}

const fn ceil_log2(value: u32) -> u8 {
    (u32::BITS - (value - 1).leading_zeros()) as u8
}

/// Rejection reason from a checked statement constructor or fold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatementError {
    ZeroRegisterIsNonZero,
    ZeroTotalCycles,
    ZeroSegmentCount,
    SlotHeightOutOfRange,
    SlotRangeOverflow,
    SlotsMisaligned,
    SlotsOutsideJob,
    ZeroExecutedSegments,
    ZeroExecutedCycles,
    SegmentRangeOverflow,
    CycleRangeOverflow,
    InteriorEmptySpan,
    ExecutedPaddingSpan,
    ExecutedSlotStartMismatch,
    ExecutedSlotCoverageMismatch,
    ExecutedCyclesOutsideJob,
    InitialCycleMismatch,
    FinalCycleMismatch,
    InitialStateMismatch,
    FinalStateMismatch,
    InputMismatch,
    OutputMismatch,
    JobMismatch,
    ChildHeightMismatch,
    SlotsNotAdjacent,
    EmptyBeforeExecuted,
    SegmentDiscontinuity,
    CycleDiscontinuity,
    StateDiscontinuity,
    LeftOutputPresent,
    RightInputPresent,
    RootSlotStartMismatch,
    RootHeightNotMinimal,
    RootIsEmpty,
    RootSegmentStartMismatch,
    RootSegmentCountMismatch,
    RootCycleStartMismatch,
    RootCycleCountMismatch,
    RootInitialStateMismatch,
    RootFinalStateMismatch,
    RootInputMismatch,
    RootOutputMismatch,
}

impl fmt::Display for StatementError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for StatementError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use air::digest::{Digest8, M31Word};
    use prover::poseidon2_channel::poseidon2_hash_m31_words;

    use super::*;

    const STATEMENT_ENCODING_HASH_DOMAIN: u16 = 0x5354;

    fn digest(seed: u16) -> Digest8 {
        Digest8::new([
            M31Word::from(seed),
            M31Word::from(seed + 1),
            M31Word::from(seed + 2),
            M31Word::from(seed + 3),
            M31Word::from(seed + 4),
            M31Word::from(seed + 5),
            M31Word::from(seed + 6),
            M31Word::from(seed + 7),
        ])
    }

    fn state(seed: u32) -> MachineState {
        let mut registers = [0_u32; 32];
        registers[1] = seed;
        MachineState::new(
            seed * 4,
            registers,
            MemoryDigest::from(digest(seed as u16 + 10)),
            IoDigest::from(digest(seed as u16 + 20)),
        )
        .expect("fixture state is canonical")
    }

    fn complete(final_state: MachineState, total_cycles: u64) -> CompleteExecutionStatement {
        CompleteExecutionStatement::new(
            ProtocolId::from(digest(1)),
            ProgramDigest::from(digest(2)),
            state(0),
            final_state,
            IoDigest::from(digest(3)),
            IoDigest::from(digest(4)),
            total_cycles,
        )
        .expect("fixture execution is nonempty")
    }

    fn job(segment_count: u32, total_cycles: u64) -> JobContext {
        JobContext::new(complete(state(segment_count), total_cycles), segment_count)
            .expect("fixture job has segments")
    }

    fn leaf(
        job: JobContext,
        index: u32,
        first_cycle: u64,
        cycle_count: u64,
        entry: MachineState,
        exit: MachineState,
    ) -> SpanStatement {
        let input = if index == 0 {
            EdgeClaim::present(job.complete.public_input)
        } else {
            EdgeClaim::absent()
        };
        let output = if index + 1 == job.segment_count() {
            EdgeClaim::present(job.complete.public_output)
        } else {
            EdgeClaim::absent()
        };
        let span = ExecutedSpan::new(
            index,
            1,
            first_cycle,
            cycle_count,
            entry,
            exit,
            input,
            output,
        )
        .expect("fixture segment range is valid");
        SpanStatement::segment_leaf(job, index, span).expect("fixture leaf matches its job")
    }

    fn unchecked_statement(job: JobContext, slot: u32, body: SpanBody) -> SpanStatement {
        SpanStatement {
            job,
            slots: SlotSpan::new(u64::from(slot), 0).expect("fixture slot exists"),
            body,
        }
    }

    fn two_segment_root() -> RootStatement {
        let job = job(2, 10);
        let left = leaf(job, 0, 0, 4, state(0), state(1));
        let right = leaf(job, 1, 4, 6, state(1), state(2));
        let folded = SpanStatement::fold(&left, &right).expect("fixture children chain");
        RootStatement::new(folded).expect("fixture root is canonical")
    }

    #[rstest]
    fn canonical_statement_variants_have_one_fixed_word_count() {
        let executed = *two_segment_root().statement();
        let empty =
            SpanStatement::empty_leaf(job(3, 12), 3).expect("the final slot is canonical padding");
        assert_eq!(
            (
                executed.canonical_words().len(),
                empty.canonical_words().len()
            ),
            (
                SPAN_STATEMENT_CANONICAL_WORDS,
                SPAN_STATEMENT_CANONICAL_WORDS,
            )
        );
    }

    #[rstest]
    fn canonical_nested_statement_lengths_match_their_layout_constants() {
        let root = two_segment_root();
        let statement = root.statement();
        let span = statement
            .body()
            .executed_span()
            .expect("fixture root is executed");
        assert_eq!(
            (
                statement
                    .job()
                    .complete()
                    .initial_state()
                    .canonical_words()
                    .len(),
                statement.job().complete().canonical_words().len(),
                statement.job().canonical_words().len(),
                statement.slots().canonical_words().len(),
                span.input().canonical_words().len(),
                span.canonical_words().len(),
                statement.body().canonical_words().len(),
            ),
            (
                MACHINE_STATE_CANONICAL_WORDS,
                COMPLETE_EXECUTION_CANONICAL_WORDS,
                JOB_CONTEXT_CANONICAL_WORDS,
                SLOT_SPAN_CANONICAL_WORDS,
                EDGE_CLAIM_CANONICAL_WORDS,
                EXECUTED_SPAN_CANONICAL_WORDS,
                SPAN_BODY_CANONICAL_WORDS,
            )
        );
    }

    #[rstest]
    fn slot_span_encoding_uses_the_height_relative_node_index() {
        let slots = SlotSpan::new(8, 2).expect("fixture span is aligned and bounded");
        assert_eq!(
            slots.canonical_words(),
            vec![
                CanonicalTag::SlotSpan.word(),
                M31Word::from(2),
                M31Word::ZERO,
                M31Word::ZERO,
                M31Word::ZERO,
                M31Word::from(2),
            ]
        );
    }

    #[rstest]
    fn canonical_layout_classifies_every_raw_integer_word() {
        let integer_count = (0..SPAN_STATEMENT_CANONICAL_WORDS)
            .filter(|index| canonical_layout::is_integer_word(*index))
            .count();
        assert_eq!(
            (
                integer_count,
                canonical_layout::is_integer_word(canonical_layout::BODY_TAG),
                canonical_layout::is_integer_word(
                    canonical_layout::INITIAL_STATE_START
                        + canonical_layout::MACHINE_STATE_RW_DIGEST_START_OFFSET,
                ),
            ),
            (288, false, false)
        );
    }

    #[rstest]
    fn raw_machine_words_do_not_alias_m31_values_in_the_statement_stream() {
        let registers = [0_u32; 32];
        let zero = MachineState::new(
            0,
            registers,
            MemoryDigest::from(digest(10)),
            IoDigest::from(digest(20)),
        )
        .expect("zero state is canonical");
        let modulus = MachineState::new(
            stwo::core::fields::m31::P,
            registers,
            MemoryDigest::from(digest(10)),
            IoDigest::from(digest(20)),
        )
        .expect("raw RV32 pc may equal the M31 modulus");
        assert_ne!(zero.canonical_words(), modulus.canonical_words());
    }

    #[rstest]
    fn absent_edge_has_one_canonical_zero_payload() {
        let words = EdgeClaim::absent().canonical_words();
        assert_eq!(
            (
                words.len(),
                words[0],
                words[1..].iter().all(|word| *word == M31Word::ZERO),
            ),
            (
                EDGE_CLAIM_CANONICAL_WORDS,
                CanonicalTag::AbsentEdge.word(),
                true,
            )
        );
    }

    #[rstest]
    fn canonical_statement_encoding_matches_its_conformance_digest() {
        let digest = poseidon2_hash_m31_words(
            &two_segment_root().statement().canonical_words(),
            M31Word::from(STATEMENT_ENCODING_HASH_DOMAIN),
        );
        assert_eq!(
            digest,
            Digest8::new([
                M31Word::try_from(2_071_595_421_u32).expect("fixture word is canonical"),
                M31Word::try_from(1_009_775_542_u32).expect("fixture word is canonical"),
                M31Word::try_from(158_433_216_u32).expect("fixture word is canonical"),
                M31Word::try_from(66_183_187_u32).expect("fixture word is canonical"),
                M31Word::try_from(1_095_277_275_u32).expect("fixture word is canonical"),
                M31Word::try_from(2_036_583_477_u32).expect("fixture word is canonical"),
                M31Word::try_from(727_733_824_u32).expect("fixture word is canonical"),
                M31Word::try_from(1_581_175_808_u32).expect("fixture word is canonical"),
            ])
        );
    }

    #[test]
    fn complete_execution_has_no_segment_count() {
        assert_eq!(two_segment_root().complete_execution().total_cycles(), 10);
    }

    #[test]
    fn one_segment_job_has_height_zero() {
        assert_eq!(job(1, 1).slot_height(), 0);
    }

    #[test]
    fn three_segment_job_has_minimal_height_two() {
        assert_eq!(job(3, 12).slot_height(), 2);
    }

    #[test]
    fn two_executed_children_fold_into_a_root() {
        assert_eq!(
            two_segment_root()
                .statement()
                .body()
                .executed_span()
                .map(|span| (span.segment_count(), span.cycle_count())),
            Some((2, 10))
        );
    }

    #[test]
    fn executed_and_empty_children_preserve_the_executed_prefix() {
        let job = job(3, 12);
        let executed = leaf(job, 2, 8, 4, state(2), state(3));
        let empty = SpanStatement::empty_leaf(job, 3).expect("slot three is padding");
        assert_eq!(
            SpanStatement::fold(&executed, &empty)
                .map(|statement| statement.body.executed_span().copied()),
            Ok(Some(*executed.body.executed_span().expect("executed leaf")))
        );
    }

    #[test]
    fn two_empty_children_fold_into_empty_padding() {
        let job = job(5, 5);
        let left = SpanStatement::empty_leaf(job, 6).expect("slot six is padding");
        let right = SpanStatement::empty_leaf(job, 7).expect("slot seven is padding");
        assert_eq!(
            SpanStatement::fold(&left, &right).map(|statement| statement.body.is_empty()),
            Ok(true)
        );
    }

    #[test]
    fn three_segments_and_one_empty_leaf_form_the_minimal_root() {
        let job = job(3, 12);
        let leaf0 = leaf(job, 0, 0, 4, state(0), state(1));
        let leaf1 = leaf(job, 1, 4, 4, state(1), state(2));
        let leaf2 = leaf(job, 2, 8, 4, state(2), state(3));
        let empty3 = SpanStatement::empty_leaf(job, 3).expect("slot three is padding");
        let left = SpanStatement::fold(&leaf0, &leaf1).expect("left pair chains");
        let right = SpanStatement::fold(&leaf2, &empty3).expect("right pair pads");
        let root = SpanStatement::fold(&left, &right).expect("pairs chain");
        assert_eq!(
            RootStatement::new(root).map(|root| root.statement.slots.height),
            Ok(2)
        );
    }

    #[test]
    fn real_leaf_is_rejected_at_the_first_padding_slot() {
        let job = job(1, 1);
        let span = ExecutedSpan::new(
            1,
            1,
            0,
            1,
            state(0),
            state(1),
            EdgeClaim::absent(),
            EdgeClaim::absent(),
        )
        .expect("range itself is representable");
        assert_eq!(
            SpanStatement::segment_leaf(job, 1, span),
            Err(StatementError::SlotsOutsideJob)
        );
    }

    #[test]
    fn empty_leaf_is_rejected_inside_the_executed_prefix() {
        assert_eq!(
            SpanStatement::empty_leaf(job(2, 2), 1),
            Err(StatementError::InteriorEmptySpan)
        );
    }

    #[derive(Clone, Copy, Debug)]
    enum FoldAttack {
        Gap,
        Overlap,
        Swap,
        UnequalHeight,
        InteriorEmpty,
        StateMismatch,
        CycleMismatch,
        LeftOutput,
        RightInput,
    }

    fn attacked_pair(attack: FoldAttack) -> (SpanStatement, SpanStatement, StatementError) {
        match attack {
            FoldAttack::Gap => {
                let job = job(3, 12);
                (
                    leaf(job, 0, 0, 4, state(0), state(1)),
                    leaf(job, 2, 8, 4, state(2), state(3)),
                    StatementError::SlotsNotAdjacent,
                )
            }
            FoldAttack::Overlap => {
                let job = job(2, 10);
                let left = leaf(job, 0, 0, 4, state(0), state(1));
                (left, left, StatementError::SlotsNotAdjacent)
            }
            FoldAttack::Swap => {
                let job = job(2, 10);
                (
                    leaf(job, 1, 4, 6, state(1), state(2)),
                    leaf(job, 0, 0, 4, state(0), state(1)),
                    StatementError::SlotsNotAdjacent,
                )
            }
            FoldAttack::UnequalHeight => {
                let job = job(3, 12);
                let leaf0 = leaf(job, 0, 0, 4, state(0), state(1));
                let leaf1 = leaf(job, 1, 4, 4, state(1), state(2));
                let pair = SpanStatement::fold(&leaf0, &leaf1).expect("pair chains");
                (
                    pair,
                    leaf(job, 2, 8, 4, state(2), state(3)),
                    StatementError::ChildHeightMismatch,
                )
            }
            FoldAttack::InteriorEmpty => {
                let job = job(2, 10);
                (
                    unchecked_statement(job, 0, SpanBody::empty()),
                    leaf(job, 1, 4, 6, state(1), state(2)),
                    StatementError::EmptyBeforeExecuted,
                )
            }
            FoldAttack::StateMismatch => {
                let job = job(2, 10);
                (
                    leaf(job, 0, 0, 4, state(0), state(9)),
                    leaf(job, 1, 4, 6, state(1), state(2)),
                    StatementError::StateDiscontinuity,
                )
            }
            FoldAttack::CycleMismatch => {
                let job = job(2, 10);
                (
                    leaf(job, 0, 0, 4, state(0), state(1)),
                    leaf(job, 1, 5, 5, state(1), state(2)),
                    StatementError::CycleDiscontinuity,
                )
            }
            FoldAttack::LeftOutput => {
                let job = job(2, 10);
                let span = ExecutedSpan::new(
                    0,
                    1,
                    0,
                    4,
                    state(0),
                    state(1),
                    EdgeClaim::present(job.complete.public_input),
                    EdgeClaim::present(job.complete.public_output),
                )
                .expect("attacked span is representable");
                (
                    unchecked_statement(job, 0, SpanBody::executed(span)),
                    leaf(job, 1, 4, 6, state(1), state(2)),
                    StatementError::LeftOutputPresent,
                )
            }
            FoldAttack::RightInput => {
                let job = job(2, 10);
                let span = ExecutedSpan::new(
                    1,
                    1,
                    4,
                    6,
                    state(1),
                    state(2),
                    EdgeClaim::present(job.complete.public_input),
                    EdgeClaim::present(job.complete.public_output),
                )
                .expect("attacked span is representable");
                (
                    leaf(job, 0, 0, 4, state(0), state(1)),
                    unchecked_statement(job, 1, SpanBody::executed(span)),
                    StatementError::RightInputPresent,
                )
            }
        }
    }

    #[rstest]
    #[case::gap(FoldAttack::Gap)]
    #[case::overlap(FoldAttack::Overlap)]
    #[case::swap(FoldAttack::Swap)]
    #[case::unequal_height(FoldAttack::UnequalHeight)]
    #[case::interior_empty(FoldAttack::InteriorEmpty)]
    #[case::state_mismatch(FoldAttack::StateMismatch)]
    #[case::cycle_mismatch(FoldAttack::CycleMismatch)]
    #[case::left_output(FoldAttack::LeftOutput)]
    #[case::right_input(FoldAttack::RightInput)]
    fn binary_fold_rejects_adversarial_children(#[case] attack: FoldAttack) {
        let (left, right, expected) = attacked_pair(attack);
        assert_eq!(SpanStatement::fold(&left, &right), Err(expected));
    }

    #[derive(Clone, Copy, Debug)]
    enum RootAttack {
        NonMinimalHeight,
        WrongCycleCount,
        MissingInput,
        MissingOutput,
    }

    fn attacked_root(attack: RootAttack) -> (SpanStatement, StatementError) {
        let canonical = *two_segment_root().statement();
        match attack {
            RootAttack::NonMinimalHeight => (
                SpanStatement {
                    slots: SlotSpan::new(0, 2).expect("height two is representable"),
                    ..canonical
                },
                StatementError::RootHeightNotMinimal,
            ),
            RootAttack::WrongCycleCount => {
                let span = ExecutedSpan::new(
                    0,
                    2,
                    0,
                    9,
                    state(0),
                    state(2),
                    canonical.body.executed_span().expect("executed root").input,
                    canonical
                        .body
                        .executed_span()
                        .expect("executed root")
                        .output,
                )
                .expect("attacked range is representable");
                (
                    SpanStatement {
                        body: SpanBody::executed(span),
                        ..canonical
                    },
                    StatementError::RootCycleCountMismatch,
                )
            }
            RootAttack::MissingInput => {
                let original = *canonical.body.executed_span().expect("executed root");
                let span = ExecutedSpan::new(
                    original.first_segment,
                    original.segment_count.get(),
                    original.first_cycle,
                    original.cycle_count.get(),
                    original.entry,
                    original.exit,
                    EdgeClaim::absent(),
                    original.output,
                )
                .expect("attacked range is representable");
                (
                    SpanStatement {
                        body: SpanBody::executed(span),
                        ..canonical
                    },
                    StatementError::RootInputMismatch,
                )
            }
            RootAttack::MissingOutput => {
                let original = *canonical.body.executed_span().expect("executed root");
                let span = ExecutedSpan::new(
                    original.first_segment,
                    original.segment_count.get(),
                    original.first_cycle,
                    original.cycle_count.get(),
                    original.entry,
                    original.exit,
                    original.input,
                    EdgeClaim::absent(),
                )
                .expect("attacked range is representable");
                (
                    SpanStatement {
                        body: SpanBody::executed(span),
                        ..canonical
                    },
                    StatementError::RootOutputMismatch,
                )
            }
        }
    }

    #[rstest]
    #[case::non_minimal_height(RootAttack::NonMinimalHeight)]
    #[case::wrong_cycle_count(RootAttack::WrongCycleCount)]
    #[case::missing_input(RootAttack::MissingInput)]
    #[case::missing_output(RootAttack::MissingOutput)]
    fn root_rejects_non_canonical_job_coverage(#[case] attack: RootAttack) {
        let (statement, expected) = attacked_root(attack);
        assert_eq!(RootStatement::new(statement), Err(expected));
    }

    #[derive(Clone, Copy, Debug)]
    enum OverflowAttack {
        Slot,
        Segment,
        Cycle,
    }

    fn overflow_error(attack: OverflowAttack) -> StatementError {
        match attack {
            OverflowAttack::Slot => SlotSpan::new(SLOT_BOUND, 0).expect_err("slot must overflow"),
            OverflowAttack::Segment => ExecutedSpan::new(
                u32::MAX,
                1,
                0,
                1,
                state(0),
                state(1),
                EdgeClaim::absent(),
                EdgeClaim::absent(),
            )
            .expect_err("segment range must overflow"),
            OverflowAttack::Cycle => ExecutedSpan::new(
                0,
                1,
                u64::MAX,
                1,
                state(0),
                state(1),
                EdgeClaim::absent(),
                EdgeClaim::absent(),
            )
            .expect_err("cycle range must overflow"),
        }
    }

    #[rstest]
    #[case::slot(OverflowAttack::Slot, StatementError::SlotRangeOverflow)]
    #[case::segment(OverflowAttack::Segment, StatementError::SegmentRangeOverflow)]
    #[case::cycle(OverflowAttack::Cycle, StatementError::CycleRangeOverflow)]
    fn checked_constructors_reject_overflow(
        #[case] attack: OverflowAttack,
        #[case] expected: StatementError,
    ) {
        assert_eq!(overflow_error(attack), expected);
    }
}
