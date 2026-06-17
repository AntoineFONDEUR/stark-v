#![feature(allocator_api)]
mod commitment;
mod cpu;
mod elf;
mod execute;
mod io;
mod memory;
mod program;
#[macro_use]
mod trace;
mod ops;

use thiserror::Error;

/// Get or decode an instruction at the given PC, caching the result.
pub(crate) fn get_or_decode(cache: &mut InstCache, mem: &Memory, pc: u32) -> Option<DecodedInst> {
    if let Some(&inst) = cache.get(&pc) {
        return Some(inst);
    }

    let word = mem.read_u32(pc);
    let decoded = DecodedInst::decode(word)?;
    cache.insert(pc, decoded);
    Some(decoded)
}

pub use air::MAX_TREE_HEIGHT;
pub use air::instructions;
pub use air::poseidon2;
pub use commitment::{CommitmentError, SegmentRole};
pub use cpu::Cpu;
pub use elf::{ElfError, load_elf};
pub use execute::execute;
pub use instructions::{DecodedInst, InstCache, Opcode};
pub use memory::Memory;
pub use trace::{Access, Tracer};

/// Errors that can occur during program execution.
#[derive(Error, Debug)]
pub enum RunError {
    #[error("Failed to load ELF: {0}")]
    Elf(#[from] ElfError),

    #[error("Invalid instruction at PC=0x{pc:08x}")]
    InvalidInstruction { pc: u32 },

    #[error("Exceeded maximum cycles ({max})")]
    MaxCyclesExceeded { cycles: u64, max: u64 },

    #[error("Input length {len} exceeds input capacity {capacity}")]
    InputTooLarge { len: usize, capacity: usize },

    #[error("Commitment error: {0}")]
    Commitment(#[from] CommitmentError),
}

/// Word-aligned I/O word captured from memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IoWord {
    pub addr: u32,
    pub value: u32,
}

/// Result of a successful program execution.
#[derive(Debug)]
pub struct RunResult {
    /// Total number of cycles executed.
    pub cycles: u64,
    /// Entry program counter.
    pub initial_pc: u32,
    /// Final program counter (where halt was detected).
    pub final_pc: u32,
    /// Register values at start of execution.
    pub initial_regs: [u32; 32],
    /// Register values at end of execution.
    pub final_regs: [u32; 32],
    /// Output bytes from guest (postcard-serialized data).
    pub output: Option<Vec<u8>>,
    /// Raw input bytes provided to the guest.
    pub input: Vec<u8>,
    /// Input region start address.
    pub input_start: u32,
    /// Input region end address (exclusive).
    pub input_end: u32,
    /// Output length (value stored at output_len_addr).
    pub output_len: u32,
    /// Address of output length word.
    pub output_len_addr: u32,
    /// Address of output data start.
    pub output_data_addr: u32,
    /// Address of output data end (exclusive).
    pub output_end_addr: u32,
    /// Output words (length word + output data words).
    pub output_words: Vec<IoWord>,
    /// Execution trace for proving.
    pub tracer: Tracer,
}

/// Run an ELF program to completion.
///
/// Executes until the guest halts or an infinite loop is detected (PC unchanged after instruction)
/// or the maximum cycle count is reached.
///
/// # Arguments
/// * `elf_bytes` - Raw bytes of the ELF file
/// * `max_cycles` - Maximum number of cycles before aborting
///
/// # Returns
/// * `Ok(RunResult)` - Program completed successfully
/// * `Err(RunError)` - Execution failed
///
/// # Example
/// ```ignore
/// let elf_bytes = std::fs::read("guest.elf")?;
/// let result = runner::run(&elf_bytes, 10_000_000)?;
/// println!("Completed in {} cycles", result.cycles);
/// ```
pub fn run(elf_bytes: &[u8], max_cycles: u64) -> Result<RunResult, RunError> {
    run_with_input(elf_bytes, &[], max_cycles)
}

/// Run an ELF program to completion with explicit input bytes.
pub fn run_with_input(
    elf_bytes: &[u8],
    input: &[u8],
    max_cycles: u64,
) -> Result<RunResult, RunError> {
    let mut segments = run_segments_with_input(elf_bytes, input, None, max_cycles)?;
    Ok(segments
        .pop()
        .expect("execution produces at least one segment"))
}

/// Run an ELF program to completion, closing the current segment whenever
/// `should_close` returns true for the live tracer (checked before fetching
/// the next instruction, so the boundary lands cleanly between instructions).
///
/// Each segment gets its own tracer with the clock restarting at 0, so each
/// can be proven independently; consecutive segments chain on
/// `(final_pc, final_regs, final_rw_root) == (initial_pc, initial_regs, initial_rw_root)`.
/// Input is anchored in the first segment and outputs in the last (see
/// [`SegmentRole`]).
fn run_segments_impl<F: Fn(&Tracer) -> bool>(
    elf_bytes: &[u8],
    input: &[u8],
    should_close: F,
    max_cycles: u64,
) -> Result<Vec<RunResult>, RunError> {
    let loaded = load_elf(elf_bytes)?;
    let layout = commitment::MemoryLayout::from_loaded(&loaded);

    let mut cpu = Cpu::new(loaded.entry, loaded.sp, loaded.gp);
    let io_addrs = IoAddrs {
        input_start: loaded.input_start_addr,
        input_end: loaded.input_end_addr,
        halt_flag: loaded.halt_flag_addr,
        output_len: loaded.output_len_addr,
        output_data: loaded.output_data_addr,
        output_end: loaded.output_end_addr,
    };
    let mut mem = loaded.memory;
    let input_start = io_addrs.input_start;
    let input_end = io_addrs.input_end;
    let input_capacity = input_end.saturating_sub(input_start) as usize;
    if input.len() > input_capacity {
        return Err(RunError::InputTooLarge {
            len: input.len(),
            capacity: input_capacity,
        });
    }
    for (idx, byte) in input.iter().enumerate() {
        let addr = input_start.wrapping_add(idx as u32);
        mem.write_u8(addr, *byte);
    }
    let mut cache: InstCache = InstCache::default();
    let mut tracer = Tracer::default();

    let mut segments: Vec<RunResult> = Vec::new();
    let mut completed_cycles: u64 = 0;
    let mut seg_initial_pc = cpu.pc;
    let mut seg_initial_regs = cpu.regs();

    let final_pc = loop {
        // Check halt flag before executing next instruction
        if mem.read_u32(io_addrs.halt_flag) != 0 {
            break cpu.pc;
        }

        // Segment boundary: close the current tracer and start a fresh one.
        // The next instruction belongs to the next segment.
        if should_close(&tracer) {
            let role = SegmentRole {
                is_first: segments.is_empty(),
                is_last: false,
            };
            commitment::finalize_commitments_with_role(&mut tracer, &mem, &layout, role)?;
            let finished = std::mem::take(&mut tracer);
            completed_cycles += finished.clock as u64;
            let mut result = make_run_result(
                finished,
                seg_initial_pc,
                cpu.pc,
                seg_initial_regs,
                cpu.regs(),
                input,
                &mem,
                io_addrs,
            );
            // Outputs are anchored in the last segment only; inputs in
            // the first only.
            result.output = None;
            result.output_len = 0;
            result.output_words = Vec::new();
            if !role.is_first {
                result.input = Vec::new();
            }
            segments.push(result);
            seg_initial_pc = cpu.pc;
            seg_initial_regs = cpu.regs();
        }

        let prev_pc = cpu.pc;

        let inst = get_or_decode(&mut cache, &mem, cpu.pc)
            .ok_or(RunError::InvalidInstruction { pc: cpu.pc })?;
        tracer.trace_instr_access(cpu.pc);

        // Early-exit on explicit self-loop sentinels (e.g., `jal x0, 0` used to halt tests).
        // Avoid tracing this noop instruction so the final trace doesn't contain a bogus row.
        let is_self_loop = match inst.opcode {
            instructions::Opcode::Jal if inst.rd == 0 && inst.imm == 0 => true,
            instructions::Opcode::Jalr if inst.rd == 0 => {
                let target = cpu.reg(inst.rs1).wrapping_add(inst.imm as u32) & !1;
                target == cpu.pc
            }
            _ => false,
        };
        if is_self_loop {
            break cpu.pc;
        }

        // Update tracer clock before executing instruction
        tracer.clock += 1;

        execute(&mut cpu, &mut mem, &inst, &mut tracer);

        // Halt on infinite loop (PC unchanged after execution) - backup detection
        if cpu.pc == prev_pc {
            break prev_pc;
        }

        // Safety limit
        if completed_cycles + tracer.clock as u64 > max_cycles {
            return Err(RunError::MaxCyclesExceeded {
                cycles: completed_cycles + tracer.clock as u64,
                max: max_cycles,
            });
        }
    };

    // Final segment: anchor outputs (and input, if this is also the first).
    let role = SegmentRole {
        is_first: segments.is_empty(),
        is_last: true,
    };
    commitment::finalize_commitments_with_role(&mut tracer, &mem, &layout, role)?;
    let mut result = make_run_result(
        tracer,
        seg_initial_pc,
        final_pc,
        seg_initial_regs,
        cpu.regs(),
        input,
        &mem,
        io_addrs,
    );
    if !role.is_first {
        result.input = Vec::new();
    }
    segments.push(result);
    Ok(segments)
}

/// Run an ELF program, splitting into segments of at most `segment_cycles`
/// cycles each. With `segment_cycles = None` the whole execution is a single
/// segment, identical to [`run_with_input`].
///
/// A fixed cycle count is a coarse proxy for capacity: different opcode/lookup
/// mixes fill the component tables at different rates, so prefer
/// [`run_segments_by_capacity`] to pack each segment up to a row budget.
pub fn run_segments_with_input(
    elf_bytes: &[u8],
    input: &[u8],
    segment_cycles: Option<u32>,
    max_cycles: u64,
) -> Result<Vec<RunResult>, RunError> {
    if let Some(n) = segment_cycles {
        // Clock differences within a segment must stay range-checkable
        // (RangeCheck20), and a zero-length segment cannot make progress.
        assert!(
            n > 0 && n < (1 << 20),
            "segment_cycles must be in 1..2^20, got {n}"
        );
    }
    run_segments_impl(
        elf_bytes,
        input,
        move |tracer| segment_cycles.is_some_and(|n| tracer.clock >= n),
        max_cycles,
    )
}

/// Run an ELF program, closing a segment as soon as any component table — or
/// the distinct read/write address set that drives the finalization
/// commitment tables — would reach `max_rows`, rather than after a fixed cycle
/// count.
///
/// The prover pads every component to a power of two at least its row count,
/// so the fullest table bounds the segment's proving size; closing on it packs
/// each segment near the row budget regardless of the opcode/lookup mix. The
/// clock (one row per cycle) is itself one of the monitored quantities, so the
/// segment always closes by `clock == max_rows`, keeping clock differences
/// range-checkable (`max_rows < 2^20`).
pub fn run_segments_by_capacity(
    elf_bytes: &[u8],
    input: &[u8],
    max_rows: u32,
    max_cycles: u64,
) -> Result<Vec<RunResult>, RunError> {
    assert!(
        max_rows > 0 && max_rows < (1 << 20),
        "max_rows must be in 1..2^20, got {max_rows}"
    );
    let budget = max_rows as usize;
    run_segments_impl(
        elf_bytes,
        input,
        move |tracer| {
            tracer.clock as usize >= budget
                || tracer.max_table_len() >= budget
                // Distinct RW addresses drive the memory and poseidon2/merkle
                // commitment tables built at finalization.
                || tracer.mem_clock.len() >= budget
        },
        max_cycles,
    )
}

/// IO-region addresses captured from the loaded ELF before its memory is
/// moved into the execution loop.
#[derive(Clone, Copy)]
struct IoAddrs {
    input_start: u32,
    input_end: u32,
    halt_flag: u32,
    output_len: u32,
    output_data: u32,
    output_end: u32,
}

/// Assemble a [`RunResult`] for a finished segment, reading the current
/// output region from memory.
#[allow(clippy::too_many_arguments)]
fn make_run_result(
    tracer: Tracer,
    initial_pc: u32,
    final_pc: u32,
    initial_regs: [u32; 32],
    final_regs: [u32; 32],
    input: &[u8],
    mem: &Memory,
    io_addrs: IoAddrs,
) -> RunResult {
    let output_len = mem.read_u32(io_addrs.output_len);
    let output = io::read_output(
        mem,
        io_addrs.output_len,
        io_addrs.output_data,
        io_addrs.output_end,
    );
    let output_words =
        collect_output_words(mem, io_addrs.output_len, io_addrs.output_data, output_len);
    RunResult {
        cycles: tracer.clock as u64,
        initial_pc,
        final_pc,
        initial_regs,
        final_regs,
        output,
        input: input.to_vec(),
        input_start: io_addrs.input_start,
        input_end: io_addrs.input_end,
        output_len,
        output_len_addr: io_addrs.output_len,
        output_data_addr: io_addrs.output_data,
        output_end_addr: io_addrs.output_end,
        output_words,
        tracer,
    }
}

pub(crate) fn collect_output_words(
    mem: &Memory,
    output_len_addr: u32,
    output_data_addr: u32,
    output_len: u32,
) -> Vec<IoWord> {
    let mut words = Vec::new();
    let len_addr = output_len_addr & !3;
    words.push(IoWord {
        addr: len_addr,
        value: mem.read_u32(len_addr),
    });
    if output_len == 0 {
        return words;
    }
    let start = output_data_addr & !3;
    let end = output_data_addr.wrapping_add(output_len);
    let end_aligned = end.wrapping_add(3) & !3;
    let mut addr = start;
    while addr < end_aligned {
        words.push(IoWord {
            addr,
            value: mem.read_u32(addr),
        });
        addr = addr.wrapping_add(4);
    }
    words
}
