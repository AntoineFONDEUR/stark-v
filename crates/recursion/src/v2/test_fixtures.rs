//! Shared typed fixtures for recursion V2 component tests.

use air::digest::{Digest8, IoDigest, M31Word, MemoryDigest, ProgramDigest, ProtocolId};

use super::statement::{
    CompleteExecutionStatement, EdgeClaim, ExecutedSpan, JobContext, MachineState, SpanStatement,
};

pub(crate) fn digest(seed: u16) -> Digest8 {
    Digest8::new(core::array::from_fn(|offset| {
        M31Word::from(seed + offset as u16)
    }))
}

pub(crate) fn state(seed: u32) -> MachineState {
    let mut registers = [0_u32; 32];
    registers[1] = seed;
    MachineState::new(
        seed * 4,
        registers,
        MemoryDigest::from(digest(seed as u16 + 10)),
        IoDigest::from(digest(seed as u16 + 20)),
    )
    .expect("fixture keeps the zero register immutable")
}

pub(crate) fn job(segment_count: u32, total_cycles: u64) -> JobContext {
    let complete = CompleteExecutionStatement::new(
        ProtocolId::from(digest(1)),
        ProgramDigest::from(digest(2)),
        state(0),
        state(segment_count),
        IoDigest::from(digest(3)),
        IoDigest::from(digest(4)),
        total_cycles,
    )
    .expect("fixture execution is nonempty");
    JobContext::new(complete, segment_count).expect("fixture job has segments")
}

pub(crate) fn leaf(
    job: JobContext,
    index: u32,
    first_cycle: u64,
    cycle_count: u64,
    entry: MachineState,
    exit: MachineState,
) -> SpanStatement {
    let input = if index == 0 {
        EdgeClaim::present(job.complete().public_input())
    } else {
        EdgeClaim::absent()
    };
    let output = if index + 1 == job.segment_count() {
        EdgeClaim::present(job.complete().public_output())
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
    .expect("fixture execution span is nonempty");
    SpanStatement::segment_leaf(job, index, span).expect("fixture leaf matches its job")
}

pub(crate) fn two_executed() -> (SpanStatement, SpanStatement, SpanStatement) {
    let job = job(2, 10);
    let left = leaf(job, 0, 0, 4, state(0), state(1));
    let right = leaf(job, 1, 4, 6, state(1), state(2));
    let parent = SpanStatement::fold(&left, &right).expect("fixture children chain");
    (left, right, parent)
}

pub(crate) fn executed_and_empty() -> (SpanStatement, SpanStatement, SpanStatement) {
    let job = job(3, 12);
    let left = leaf(job, 2, 8, 4, state(2), state(3));
    let right = SpanStatement::empty_leaf(job, 3).expect("slot three is suffix padding");
    let parent = SpanStatement::fold(&left, &right).expect("executed prefix keeps padding");
    (left, right, parent)
}

pub(crate) fn two_empty() -> (SpanStatement, SpanStatement, SpanStatement) {
    let job = job(5, 20);
    let left = SpanStatement::empty_leaf(job, 6).expect("slot six is suffix padding");
    let right = SpanStatement::empty_leaf(job, 7).expect("slot seven is suffix padding");
    let parent = SpanStatement::fold(&left, &right).expect("padding children fold");
    (left, right, parent)
}
