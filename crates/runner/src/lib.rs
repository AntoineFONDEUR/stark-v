#![feature(allocator_api)]
//! Segmented RV32IM execution and proof-witness construction.

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
mod syscalls;

use thiserror::Error;

use air::poseidon2::Poseidon2Digest;

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

    #[error("Unsupported syscall {id} at PC=0x{pc:08x}")]
    UnsupportedSyscall { pc: u32, id: u32 },

    #[error("Exceeded maximum cycles ({max})")]
    MaxCyclesExceeded { cycles: u64, max: u64 },

    #[error("Input length {len} exceeds input capacity {capacity}")]
    InputTooLarge { len: usize, capacity: usize },

    #[error("Finalized segment {segment_index} uses {rows} rows, exceeding max_rows {max_rows}")]
    FinalizedSegmentCapacityExceeded {
        segment_index: usize,
        rows: usize,
        max_rows: u32,
    },

    #[error("Memory fault at PC=0x{pc:08x}: {kind} address 0x{addr:08x}")]
    MemoryFault {
        pc: u32,
        addr: u32,
        kind: MemoryFaultKind,
    },

    #[error("Commitment error: {0}")]
    Commitment(#[from] CommitmentError),
}

/// Why a memory access was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryFaultKind {
    /// A store targeting the read-only code (TEXT) region. The program table
    /// commits instructions separately, so such a write cannot change what
    /// executes — it is always a guest bug, caught here rather than silently
    /// writing to a shadow location.
    StoreIntoText,
    /// A load or store touching the null page (address below the TEXT origin),
    /// which no valid pointer addresses.
    NullPage,
}

impl std::fmt::Display for MemoryFaultKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MemoryFaultKind::StoreIntoText => write!(f, "store into read-only code"),
            MemoryFaultKind::NullPage => write!(f, "null-page"),
        }
    }
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
    /// Journal digest at this segment's entry boundary.
    pub initial_public_io_state: Poseidon2Digest,
    /// Journal digest at this segment's exit boundary.
    pub final_public_io_state: Poseidon2Digest,
    /// Number of COMMIT calls authenticated by this segment.
    pub journal_count: u32,
    /// Execution clock of this segment's last COMMIT, or zero when absent.
    pub journal_last_clock: u32,
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
/// `(final_pc, final_regs, final_rw_root, final_public_io_state)` equals the
/// next segment's corresponding initial state.
/// Input is anchored in the first segment and outputs in the last (see
/// [`SegmentRole`]).
///
/// Output anchoring consumes each output word's access within the LAST
/// segment's trace, so when splitting is enabled (`should_close` is `Some`)
/// every output-region write must land there: the first store into the
/// output region forces a boundary just before it, and no segment closes
/// afterwards. The mirror of "input is read within the first segment" is
/// thus "output is written within the last segment" — guests must fit their
/// output tail (first output store to halt) in one segment budget.
/// `should_close = None` runs the whole execution as one segment.
fn run_segments_impl<F: Fn(&Tracer) -> bool>(
    elf_bytes: &[u8],
    input: &[u8],
    should_close: Option<F>,
    max_rows: Option<u32>,
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
    // The read-only code region (stores here are always guest bugs) and the
    // TEXT origin (nothing valid lives below it — the null page).
    let text_range = loaded.text_base..loaded.text_end;
    let null_page_top = loaded.text_base;
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
    // Publish the actual input length so the guest reads only live bytes
    // instead of treating the whole buffer as input.
    if let Some(addr) = loaded.input_len_addr {
        mem.write_u32(addr, input.len() as u32);
    }
    let mut cache: InstCache = InstCache::default();
    let mut tracer = Tracer::default();

    let mut segments: Vec<RunResult> = Vec::new();
    let mut completed_cycles: u64 = 0;
    let mut seg_initial_pc = cpu.pc;
    let mut seg_initial_regs = cpu.regs();
    let mut seg_initial_public_io_state = cpu.public_io_state();

    // Set once the guest first stores into the output region: from then on
    // the run is in its output tail and the current segment is the last one.
    let mut output_phase = false;

    let final_pc = loop {
        // Check halt flag before executing next instruction
        if mem.read_u32(io_addrs.halt_flag) != 0 {
            break cpu.pc;
        }

        // Decoding is pure (no trace side effects), so the next instruction
        // can steer the boundary: a first output-region store closes the
        // current segment so the whole output tail lands in the final one.
        let next_inst = get_or_decode(&mut cache, &mem, cpu.pc)
            .ok_or(RunError::InvalidInstruction { pc: cpu.pc })?;
        // Reject stores into read-only code and any access to the null page
        // before it can silently corrupt a shadow location.
        if let Some(fault) = memory_fault(&cpu, &next_inst, &text_range, null_page_top) {
            return Err(fault);
        }
        let output_write = writes_output_region(&cpu, &next_inst, io_addrs);
        let splitting = should_close.is_some();
        let force_close = splitting && output_write && !output_phase && tracer.clock > 0;
        let capacity_close =
            should_close.as_ref().is_some_and(|close| close(&tracer)) && !output_phase;

        // Segment boundary: close the current tracer and start a fresh one.
        // The next instruction belongs to the next segment. After the output
        // phase starts, no boundary is allowed — output words must be
        // anchored by the last segment's trace.
        if capacity_close || force_close {
            let role = SegmentRole {
                is_first: segments.is_empty(),
                is_last: false,
            };
            commitment::finalize_commitments_with_role(&mut tracer, &mem, &layout, role)?;
            ensure_finalized_segment_capacity(&tracer, segments.len(), max_rows)?;
            let finished = std::mem::take(&mut tracer);
            completed_cycles += finished.clock as u64;
            let mut result = make_run_result(
                finished,
                seg_initial_pc,
                cpu.pc,
                seg_initial_regs,
                cpu.regs(),
                seg_initial_public_io_state,
                cpu.public_io_state(),
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
            seg_initial_public_io_state = cpu.public_io_state();
        }
        output_phase |= output_write;

        let prev_pc = cpu.pc;

        let inst = next_inst;
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

        execute(&mut cpu, &mut mem, &inst, &mut tracer)?;

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
    ensure_finalized_segment_capacity(&tracer, segments.len(), max_rows)?;
    let mut result = make_run_result(
        tracer,
        seg_initial_pc,
        final_pc,
        seg_initial_regs,
        cpu.regs(),
        seg_initial_public_io_state,
        cpu.public_io_state(),
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
        segment_cycles.map(|n| move |tracer: &Tracer| tracer.clock >= n),
        None,
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
/// Finalized tables are checked again because commitment construction can add
/// rows that were absent when the live segment reached its boundary.
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
        Some(move |tracer: &Tracer| {
            tracer.clock as usize >= budget
                || tracer.max_table_len() >= budget
                // Distinct RW addresses drive the memory and poseidon2/merkle
                // commitment tables built at finalization.
                || tracer.mem_clock.len() >= budget
        }),
        Some(max_rows),
        max_cycles,
    )
}

/// Check completed tables because finalization adds rows absent from the live tracer.
fn ensure_finalized_segment_capacity(
    tracer: &Tracer,
    segment_index: usize,
    max_rows: Option<u32>,
) -> Result<(), RunError> {
    let Some(max_rows) = max_rows else {
        return Ok(());
    };
    let rows = tracer.max_table_len();
    if rows > max_rows as usize {
        return Err(RunError::FinalizedSegmentCapacityExceeded {
            segment_index,
            rows,
            max_rows,
        });
    }
    Ok(())
}

/// Whether executing `inst` would store into the guest's output region (the
/// word holding the output length, or the output data buffer). Pure: the
/// effective address only depends on the current register file.
fn writes_output_region(cpu: &Cpu, inst: &DecodedInst, io: IoAddrs) -> bool {
    let width = match inst.opcode {
        Opcode::Sb => 1,
        Opcode::Sh => 2,
        Opcode::Sw => 4,
        _ => return false,
    };
    let addr = cpu.reg(inst.rs1).wrapping_add(inst.imm as u32);
    let end = addr.wrapping_add(width);
    let len_word = io.output_len & !3;
    let overlaps = |lo: u32, hi: u32| addr < hi && end > lo;
    overlaps(len_word, len_word.wrapping_add(4)) || overlaps(io.output_data, io.output_end)
}

/// The effective address and access width of a load/store, or `None` for a
/// non-memory instruction. Pure: depends only on the register file.
fn mem_access(cpu: &Cpu, inst: &DecodedInst) -> Option<(u32, u32, bool)> {
    // (addr, width, is_store)
    let (width, is_store) = match inst.opcode {
        Opcode::Sb => (1, true),
        Opcode::Sh => (2, true),
        Opcode::Sw => (4, true),
        Opcode::Lb | Opcode::Lbu => (1, false),
        Opcode::Lh | Opcode::Lhu => (2, false),
        Opcode::Lw => (4, false),
        _ => return None,
    };
    let addr = cpu.reg(inst.rs1).wrapping_add(inst.imm as u32);
    Some((addr, width, is_store))
}

/// Reject stores into the read-only code region and any access straddling the
/// null page. Returns the fault to raise, or `None` if the access is allowed.
fn memory_fault(
    cpu: &Cpu,
    inst: &DecodedInst,
    text_range: &core::ops::Range<u32>,
    null_page_top: u32,
) -> Option<RunError> {
    let (addr, width, is_store) = mem_access(cpu, inst)?;
    let end = addr.wrapping_add(width);
    let overlaps = |lo: u32, hi: u32| addr < hi && end > lo;

    if addr < null_page_top {
        return Some(RunError::MemoryFault {
            pc: cpu.pc,
            addr,
            kind: MemoryFaultKind::NullPage,
        });
    }
    if is_store && !text_range.is_empty() && overlaps(text_range.start, text_range.end) {
        return Some(RunError::MemoryFault {
            pc: cpu.pc,
            addr,
            kind: MemoryFaultKind::StoreIntoText,
        });
    }
    None
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
    initial_public_io_state: Poseidon2Digest,
    final_public_io_state: Poseidon2Digest,
    input: &[u8],
    mem: &Memory,
    io_addrs: IoAddrs,
) -> RunResult {
    let journal_count =
        u32::try_from(tracer.commit.len()).expect("COMMIT trace length exceeds u32");
    let journal_last_clock = tracer.commit.clock.last().copied().unwrap_or(0);
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
        initial_public_io_state,
        final_public_io_state,
        journal_count,
        journal_last_clock,
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
