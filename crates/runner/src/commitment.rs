//! Program and memory commitment trace construction.

use rustc_hash::FxHashMap;
use std::collections::BTreeSet;
use thiserror::Error;

use crate::MAX_TREE_HEIGHT;
use crate::Memory;
use crate::ops::utils::M31_P;
use crate::poseidon2::{POSEIDON2_DEFAULT_HASHES_DEPTH_30, poseidon2_traced};
use crate::program::{ProgramRow, decode_program};
use crate::trace::{MemoryTable, MerkleTable, Poseidon2Table, ProgramTable, Tracer};

// The table has one default hash per Merkle depth, including the root and leaves.
const _: [(); MAX_TREE_HEIGHT as usize] = [(); POSEIDON2_DEFAULT_HASHES_DEPTH_30.len()];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct MemoryLayout {
    pub program_base: u32,
    pub program_end: u32,
    pub data_base: u32,
    pub data_end: u32,
    pub stack_bottom: u32,
    pub stack_top: u32,
    pub io_base: u32,
    pub io_end: u32,
    pub input_base: u32,
    pub input_end: u32,
    pub output_len_addr: u32,
    pub output_data_addr: u32,
    pub output_base: u32,
    pub output_end: u32,
}

impl MemoryLayout {
    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        program_base: u32,
        program_end: u32,
        data_base: u32,
        data_end: u32,
        stack_bottom: u32,
        stack_top: u32,
        io_base: u32,
        io_end: u32,
        input_base: u32,
        input_end: u32,
        output_len_addr: u32,
        output_data_addr: u32,
        output_base: u32,
        output_end: u32,
    ) -> Self {
        Self {
            program_base,
            program_end,
            data_base,
            data_end,
            stack_bottom,
            stack_top,
            io_base,
            io_end,
            input_base,
            input_end,
            output_len_addr,
            output_data_addr,
            output_base,
            output_end,
        }
    }

    pub(crate) fn from_loaded(loaded: &crate::elf::LoadedElf) -> Self {
        let mut io_base = loaded
            .halt_flag_addr
            .min(loaded.output_len_addr)
            .min(loaded.output_data_addr);
        let mut io_end = loaded
            .output_end_addr
            .max(loaded.output_data_addr)
            .max(loaded.output_len_addr)
            .max(loaded.halt_flag_addr)
            .saturating_add(1);
        if loaded.input_start_addr < loaded.input_end_addr {
            io_base = io_base.min(loaded.input_start_addr);
            io_end = io_end.max(loaded.input_end_addr);
        }

        Self {
            program_base: loaded.text_base,
            program_end: loaded.text_end,
            data_base: loaded.data_base,
            data_end: loaded.data_end,
            stack_bottom: loaded.stack_bottom,
            stack_top: loaded.sp,
            io_base,
            io_end,
            input_base: loaded.input_start_addr,
            input_end: loaded.input_end_addr,
            output_len_addr: loaded.output_len_addr,
            output_data_addr: loaded.output_data_addr,
            output_base: loaded.output_len_addr,
            output_end: loaded.output_end_addr,
        }
    }

    pub(crate) fn is_input_addr(&self, addr: u32) -> bool {
        addr >= self.input_base && addr < self.input_end
    }

    pub(crate) fn is_public_output_addr(&self, addr: u32, output_len: u32) -> bool {
        let len_addr = self.output_len_addr & !3;
        if addr == len_addr {
            return true;
        }
        if output_len == 0 {
            return false;
        }
        let start = self.output_data_addr & !3;
        let end = self.output_data_addr.wrapping_add(output_len);
        let end_aligned = end.wrapping_add(3) & !3;
        addr >= start && addr < end_aligned
    }

    pub(crate) fn is_rw_addr(&self, addr: u32) -> bool {
        (addr >= self.data_base && addr < self.data_end)
            || (addr >= self.stack_bottom && addr < self.stack_top)
            || (addr >= self.io_base && addr < self.io_end)
    }
}

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum CommitmentError {
    #[error("Failed to decode instruction at PC=0x{pc:08x} (word=0x{word:08x})")]
    DecodeFailure { pc: u32, word: u32 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MerkleValue {
    pub value: u32,
    pub multiplicity: u32,
}

impl MerkleValue {
    pub fn new(value: u32, multiplicity: u32) -> Self {
        Self {
            value,
            multiplicity,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeData {
    pub index: u32,
    pub depth: u32,
    pub left: MerkleValue,
    pub right: MerkleValue,
    pub cur: MerkleValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MemoryCommitmentEntry {
    addr: u32,
    initial_word: u32,
    final_word: u32,
    final_clock: u32,
    include_initial: bool,
    include_final: bool,
}

impl MemoryCommitmentEntry {
    fn initial_bytes(self) -> [u8; 4] {
        self.initial_word.to_le_bytes()
    }

    fn final_bytes(self) -> [u8; 4] {
        self.final_word.to_le_bytes()
    }
}

fn insert_word_leaves(leaves: &mut FxHashMap<u32, MerkleValue>, addr: u32, word: u32) {
    let bytes = word.to_le_bytes();
    for limb in 0..4u32 {
        leaves.insert(
            addr + limb,
            MerkleValue::new(bytes[limb as usize] as u32, 1),
        );
    }
}

fn collect_program_leaves(program_rows: &[ProgramRow]) -> FxHashMap<u32, MerkleValue> {
    let mut leaves = FxHashMap::default();
    for row in program_rows {
        for limb in 0..4u32 {
            leaves.insert(
                row.addr + limb,
                MerkleValue::new(row.values[limb as usize], 1),
            );
        }
    }
    leaves
}

pub fn build_partial_merkle_tree(
    leaves: &FxHashMap<u32, MerkleValue>,
    poseidon2: &mut Poseidon2Table,
) -> (Vec<NodeData>, u32) {
    let leaf_depth = MAX_TREE_HEIGHT - 1;
    if leaves.is_empty() {
        let root = POSEIDON2_DEFAULT_HASHES_DEPTH_30[0];
        return (vec![], root);
    }

    let defaults = &POSEIDON2_DEFAULT_HASHES_DEPTH_30;
    let mut nodes = Vec::new();
    let mut current: FxHashMap<u32, MerkleValue> = leaves.clone();

    for depth in (1..=leaf_depth).rev() {
        let mut next: FxHashMap<u32, MerkleValue> = FxHashMap::default();
        let mut indices: Vec<u32> = current.keys().copied().collect();
        indices.sort_unstable();
        let mut processed = std::collections::HashSet::new();

        for &index in &indices {
            if processed.contains(&index) {
                continue;
            }

            let sibling_index = index ^ 1;
            let (left_index, right_index) = if index.is_multiple_of(2) {
                (index, sibling_index)
            } else {
                (sibling_index, index)
            };

            let left = current
                .get(&left_index)
                .copied()
                .unwrap_or_else(|| MerkleValue::new(defaults[depth as usize], 0));
            let right = current
                .get(&right_index)
                .copied()
                .unwrap_or_else(|| MerkleValue::new(defaults[depth as usize], 0));

            let out = poseidon2_traced(poseidon2, left.value, right.value);
            let cur = MerkleValue::new(out[0], 1);

            nodes.push(NodeData {
                index: left_index,
                depth,
                left,
                right,
                cur,
            });

            next.insert(left_index >> 1, cur);
            processed.insert(left_index);
            processed.insert(right_index);
        }

        current = next;
    }

    let root = current.get(&0).map(|v| v.value).unwrap_or(0);
    (nodes, root)
}

fn collect_memory_commitment(
    tracer: &Tracer,
    memory: &Memory,
    layout: &MemoryLayout,
    role: SegmentRole,
) -> (
    Vec<MemoryCommitmentEntry>,
    FxHashMap<u32, MerkleValue>,
    FxHashMap<u32, MerkleValue>,
) {
    let output_len = memory.read_u32(layout.output_len_addr);
    let mut entries = Vec::new();
    let mut rw_initial_leaves: FxHashMap<u32, MerkleValue> = FxHashMap::default();
    let mut rw_final_leaves: FxHashMap<u32, MerkleValue> = FxHashMap::default();

    let mut mem_addrs = BTreeSet::new();
    for addr in memory.keys() {
        if layout.is_rw_addr(addr) {
            mem_addrs.insert(addr & !3);
        }
    }
    for addr in tracer.mem_clock.keys().copied() {
        if layout.is_rw_addr(addr) {
            mem_addrs.insert(addr & !3);
        }
    }

    for addr in mem_addrs {
        let is_input = role.is_first && layout.is_input_addr(addr);
        let is_public_output = role.is_last && layout.is_public_output_addr(addr, output_len);
        let final_clock = tracer.mem_clock.get(&addr).copied().unwrap_or(0);
        let accessed = final_clock > 0;
        let include_initial = !is_input;
        let include_final = if is_input {
            accessed
        } else {
            !is_public_output
        };
        let final_word = memory.read_u32(addr);
        let initial_word = tracer.mem_initial.get(&addr).copied().unwrap_or(final_word);

        if include_initial {
            insert_word_leaves(&mut rw_initial_leaves, addr, initial_word);
        }
        if include_final {
            insert_word_leaves(&mut rw_final_leaves, addr, final_word);
        }

        entries.push(MemoryCommitmentEntry {
            addr,
            initial_word,
            final_word,
            final_clock,
            include_initial,
            include_final,
        });
    }

    (entries, rw_initial_leaves, rw_final_leaves)
}

fn push_memory_rows(
    table: &mut MemoryTable,
    entries: &[MemoryCommitmentEntry],
    rw_initial_root: u32,
    rw_final_root: u32,
) {
    for entry in entries {
        if entry.include_initial {
            let bytes = entry.initial_bytes();
            table.push(
                entry.addr,
                0,
                bytes[0] as u32,
                bytes[1] as u32,
                bytes[2] as u32,
                bytes[3] as u32,
                1,
                rw_initial_root,
            );
        }

        if entry.include_final {
            let bytes = entry.final_bytes();
            table.push(
                entry.addr,
                entry.final_clock,
                bytes[0] as u32,
                bytes[1] as u32,
                bytes[2] as u32,
                bytes[3] as u32,
                M31_P - 1,
                rw_final_root,
            );
        }
    }
}

fn push_program_rows(
    table: &mut ProgramTable,
    program_rows: &[ProgramRow],
    program_reads: &FxHashMap<u32, u32>,
    program_root: u32,
) {
    for row in program_rows {
        let read_count = program_reads.get(&row.addr).copied().unwrap_or(0);
        table.push(
            row.addr,
            row.values[0],
            row.values[1],
            row.values[2],
            row.values[3],
            read_count,
            program_root,
        );
    }
}

fn push_merkle_nodes(nodes: Vec<NodeData>, root: u32, table: &mut MerkleTable) {
    for node in nodes {
        table.push(
            node.index,
            node.depth,
            node.left.value,
            node.right.value,
            node.cur.value,
            node.left.multiplicity,
            node.right.multiplicity,
            node.cur.multiplicity,
            root,
        );
    }
}

/// Position of a segment within a (possibly segmented) execution.
///
/// Input words are anchored via public-data LogUp emission only in the first
/// segment, and public outputs are consumed via LogUp only in the last; in
/// every other segment the IO regions are ordinary read-write memory anchored
/// by the Merkle roots, so consecutive segments chain on
/// `final_rw_root(k) == initial_rw_root(k + 1)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SegmentRole {
    pub is_first: bool,
    pub is_last: bool,
}

impl SegmentRole {
    /// A non-segmented execution: single segment, both first and last.
    pub fn single() -> Self {
        Self {
            is_first: true,
            is_last: true,
        }
    }
}

pub(crate) fn finalize_commitments_with_role(
    tracer: &mut Tracer,
    memory: &Memory,
    layout: &MemoryLayout,
    role: SegmentRole,
) -> Result<(), CommitmentError> {
    // Create trace tables
    tracer.program = ProgramTable::new();
    tracer.memory = MemoryTable::new();
    tracer.merkle = MerkleTable::new();
    tracer.poseidon2 = Poseidon2Table::new();

    // Create program leaves
    let program_rows = decode_program(memory, layout)?;
    let program_leaves = collect_program_leaves(&program_rows);

    // Create memory leaves
    let (mem_entries, rw_initial_leaves, rw_final_leaves) =
        collect_memory_commitment(tracer, memory, layout, role);

    // Build Merkle trees and Poseidon2 trace
    let (program_nodes, program_root) =
        build_partial_merkle_tree(&program_leaves, &mut tracer.poseidon2);
    let (rw_initial_nodes, rw_initial_root) =
        build_partial_merkle_tree(&rw_initial_leaves, &mut tracer.poseidon2);
    let (rw_final_nodes, rw_final_root) =
        build_partial_merkle_tree(&rw_final_leaves, &mut tracer.poseidon2);

    // Create memory trace
    push_memory_rows(
        &mut tracer.memory,
        &mem_entries,
        rw_initial_root,
        rw_final_root,
    );

    // Create program trace
    push_program_rows(
        &mut tracer.program,
        &program_rows,
        &tracer.program_reads,
        program_root,
    );

    // Create Merkle tree trace
    push_merkle_nodes(rw_initial_nodes, rw_initial_root, &mut tracer.merkle);
    push_merkle_nodes(rw_final_nodes, rw_final_root, &mut tracer.merkle);
    push_merkle_nodes(program_nodes, program_root, &mut tracer.merkle);

    Ok(())
}

#[cfg(test)]
pub(crate) fn finalize_commitments(
    tracer: &mut Tracer,
    memory: &Memory,
    layout: &MemoryLayout,
) -> Result<(), CommitmentError> {
    finalize_commitments_with_role(tracer, memory, layout, SegmentRole::single())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Memory;
    use crate::{InstCache, RunError, RunResult, execute, instructions, io, load_elf};

    fn run_with_tracer_for_test(
        elf_bytes: &[u8],
        max_cycles: u64,
        mut tracer: Tracer,
    ) -> Result<RunResult, RunError> {
        let loaded = load_elf(elf_bytes)?;
        let layout = MemoryLayout::from_loaded(&loaded);

        let mut cpu = crate::Cpu::new(loaded.entry, loaded.sp, loaded.gp);
        let initial_pc = cpu.pc;
        let initial_regs = cpu.regs();
        let mut mem = loaded.memory;
        let mut cache: InstCache = InstCache::default();

        loop {
            if mem.read_u32(loaded.halt_flag_addr) != 0 {
                let output_len = mem.read_u32(loaded.output_len_addr);
                let output = io::read_output(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    loaded.output_end_addr,
                );
                let output_words = crate::collect_output_words(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    output_len,
                );
                super::finalize_commitments(&mut tracer, &mem, &layout)?;
                return Ok(RunResult {
                    cycles: tracer.clock as u64,
                    initial_pc,
                    final_pc: cpu.pc,
                    initial_regs,
                    final_regs: cpu.regs(),
                    output,
                    input: Vec::new(),
                    input_start: loaded.input_start_addr,
                    input_end: loaded.input_end_addr,
                    output_len,
                    output_len_addr: loaded.output_len_addr,
                    output_data_addr: loaded.output_data_addr,
                    output_end_addr: loaded.output_end_addr,
                    output_words,
                    tracer,
                });
            }

            let prev_pc = cpu.pc;
            let inst = crate::get_or_decode(&mut cache, &mem, cpu.pc)
                .ok_or(RunError::InvalidInstruction { pc: cpu.pc })?;
            tracer.trace_instr_access(cpu.pc);

            let is_self_loop = match inst.opcode {
                instructions::Opcode::Jal if inst.rd == 0 && inst.imm == 0 => true,
                instructions::Opcode::Jalr if inst.rd == 0 => {
                    let target = cpu.reg(inst.rs1).wrapping_add(inst.imm as u32) & !1;
                    target == cpu.pc
                }
                _ => false,
            };
            if is_self_loop {
                let output_len = mem.read_u32(loaded.output_len_addr);
                let output = io::read_output(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    loaded.output_end_addr,
                );
                let output_words = crate::collect_output_words(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    output_len,
                );
                super::finalize_commitments(&mut tracer, &mem, &layout)?;
                return Ok(RunResult {
                    cycles: tracer.clock as u64,
                    initial_pc,
                    final_pc: cpu.pc,
                    initial_regs,
                    final_regs: cpu.regs(),
                    output,
                    input: Vec::new(),
                    input_start: loaded.input_start_addr,
                    input_end: loaded.input_end_addr,
                    output_len,
                    output_len_addr: loaded.output_len_addr,
                    output_data_addr: loaded.output_data_addr,
                    output_end_addr: loaded.output_end_addr,
                    output_words,
                    tracer,
                });
            }

            tracer.clock += 1;
            execute(&mut cpu, &mut mem, &inst, &mut tracer);

            if cpu.pc == prev_pc {
                let output_len = mem.read_u32(loaded.output_len_addr);
                let output = io::read_output(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    loaded.output_end_addr,
                );
                let output_words = crate::collect_output_words(
                    &mem,
                    loaded.output_len_addr,
                    loaded.output_data_addr,
                    output_len,
                );
                super::finalize_commitments(&mut tracer, &mem, &layout)?;
                return Ok(RunResult {
                    cycles: tracer.clock as u64,
                    initial_pc,
                    final_pc: prev_pc,
                    initial_regs,
                    final_regs: cpu.regs(),
                    output,
                    input: Vec::new(),
                    input_start: loaded.input_start_addr,
                    input_end: loaded.input_end_addr,
                    output_len,
                    output_len_addr: loaded.output_len_addr,
                    output_data_addr: loaded.output_data_addr,
                    output_end_addr: loaded.output_end_addr,
                    output_words,
                    tracer,
                });
            }

            if tracer.clock as u64 > max_cycles {
                return Err(RunError::MaxCyclesExceeded {
                    cycles: tracer.clock as u64,
                    max: max_cycles,
                });
            }
        }
    }

    #[test]
    fn test_commitment_decode_failure() {
        let layout = MemoryLayout::new(
            0x1000, 0x2000, 0x3000, 0x4000, 0x5000, 0x6000, 0x7000, 0x8000, 0x7000, 0x7000, 0x7000,
            0x7004, 0x7000, 0x7000,
        );
        let mut mem = Memory::new();
        mem.write_u32(layout.program_base, 0xFFFF_FFFF);
        let mut tracer = Tracer::default();
        let err = super::finalize_commitments(&mut tracer, &mem, &layout).unwrap_err();
        assert_eq!(
            err,
            CommitmentError::DecodeFailure {
                pc: layout.program_base,
                word: 0xFFFF_FFFF
            }
        );
    }

    #[test]
    fn test_commitment_traces_non_empty() {
        prover::e2e::ensure_guest_built();
        let elf_path = prover::e2e::guest_bin_dir().join("memory");
        let elf_bytes = std::fs::read(&elf_path)
            .unwrap_or_else(|e| panic!("Failed to read ELF {elf_path:?}: {e}"));

        let result =
            run_with_tracer_for_test(&elf_bytes, 10_000_000, Tracer::with_max_clock_diff(1))
                .expect("Run failed");
        let tracer = result.tracer;

        assert!(!tracer.program.is_empty());
        assert!(!tracer.merkle.is_empty());
        assert!(!tracer.poseidon2.is_empty());
        assert!(!tracer.clock_update.is_empty());
    }
}
