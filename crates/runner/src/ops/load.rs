//! Load operations - part of load_store family (airs.md Section 13)

use super::utils::imm_to_felt;
use crate::trace::{Access, Tracer};
use crate::{Cpu, DecodedInst, Memory};

/// Fill one load_store row from the base-address read, the source and
/// destination accesses (register vs RW memory selected by load/store), the
/// instruction operands, the sub-word shift/marker witness and the eight
/// one-hot opcode flags.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_load_store(
    tracer: &mut Tracer,
    pc: u32,
    dst: &Access,
    rs1: &Access,
    src: &Access,
    r2_idx: u32,
    imm_felt: u32,
    src_msb: u32,
    shift_amount: u32,
    src_addr_selector: u32,
    dst_addr_selector: u32,
    marker: [u32; 4],
    flags: [u32; 8],
) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;
    let clock = tracer.clock;
    let limbs = |a: &Access| {
        [
            a.addr,
            a.prev & 0xFF,
            (a.prev >> 8) & 0xFF,
            (a.prev >> 16) & 0xFF,
            (a.prev >> 24) & 0xFF,
            a.clock_prev,
            a.next & 0xFF,
            (a.next >> 8) & 0xFF,
            (a.next >> 16) & 0xFF,
            (a.next >> 24) & 0xFF,
        ]
    };
    let mut args = Vec::with_capacity(50);
    args.extend([clock, pc]);
    args.extend(limbs(dst));
    args.extend(limbs(rs1));
    args.extend(limbs(src));
    args.extend([
        r2_idx,
        imm_felt,
        src_msb,
        shift_amount,
        src_addr_selector,
        dst_addr_selector,
    ]);
    args.extend(marker);
    args.extend(flags);
    air::opcodes::load_store::load_store_fill(
        &mut tracer.load_store,
        args.into_iter()
            .map(f)
            .collect::<Vec<_>>()
            .try_into()
            .expect("load_store fill takes 50 felts"),
        [],
    );
}

/// Extract a byte from a u32 word at the given byte offset (0-3).
#[inline]
fn extract_byte(word: u32, offset: u32) -> u8 {
    (word >> (8 * (offset & 3))) as u8
}

/// Extract a half-word from a u32 word at the given byte offset (0 or 2).
#[inline]
fn extract_halfword(word: u32, offset: u32) -> u16 {
    (word >> (8 * (offset & 2))) as u16
}

/// Compute load/store witness columns
fn compute_load_store_witness(addr: u32, is_byte: bool, is_half: bool) -> LoadStoreWitness {
    let byte_offset = addr & 3;
    let shift_amount = if is_byte {
        byte_offset
    } else if is_half {
        byte_offset & 2
    } else {
        0
    };

    // One-hot encoding of byte position for loads
    let mut marker = [0u32; 4];
    if is_byte {
        marker[byte_offset as usize] = 1;
    } else if is_half {
        // For half-word: either [1,1,0,0] or [0,0,1,1]
        if byte_offset < 2 {
            marker[0] = 1;
            marker[1] = 1;
        } else {
            marker[2] = 1;
            marker[3] = 1;
        }
    }
    // For word loads, marker is all zeros

    LoadStoreWitness {
        shift_amount,
        marker,
    }
}

struct LoadStoreWitness {
    shift_amount: u32,
    marker: [u32; 4],
}

pub fn lb(cpu: &mut Cpu, memory: &Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let mem = memory.read_u8_traced(addr, tracer);
    let byte = extract_byte(mem.next, addr);
    let value = byte as i8 as i32 as u32; // Sign-extend
    let rd = cpu.write_reg(inst.rd, value, tracer);
    cpu.advance_pc();

    let w = compute_load_store_witness(addr, true, false);
    let src_msb = ((byte >> 7) & 1) as u32; // Sign bit of loaded byte
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: lb=1, lh=0, lbu=0, lhu=0, lw=0, sb=0, sh=0, sw=0
    // For loads: dst=rd, src=mem, r2_idx=rd_addr
    // src_addr_selector = mem_addr - shift_amount, dst_addr_selector = r2_idx
    let src_addr_selector = addr - w.shift_amount;
    let dst_addr_selector = inst.rd as u32;
    fill_load_store(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &mem,
        inst.rd as u32,
        imm_felt,
        src_msb,
        w.shift_amount,
        src_addr_selector,
        dst_addr_selector,
        w.marker,
        [1, 0, 0, 0, 0, 0, 0, 0],
    );
}

pub fn lh(cpu: &mut Cpu, memory: &Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let mem = memory.read_u16_traced(addr, tracer);
    let halfword = extract_halfword(mem.next, addr);
    let value = halfword as i16 as i32 as u32; // Sign-extend
    let rd = cpu.write_reg(inst.rd, value, tracer);
    cpu.advance_pc();

    let w = compute_load_store_witness(addr, false, true);
    let src_msb = ((halfword >> 15) & 1) as u32; // Sign bit of loaded half-word
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: lb=0, lh=1, lbu=0, lhu=0, lw=0, sb=0, sh=0, sw=0
    // For loads: dst=rd, src=mem, r2_idx=rd_addr
    // src_addr_selector = mem_addr - shift_amount, dst_addr_selector = r2_idx
    let src_addr_selector = addr - w.shift_amount;
    let dst_addr_selector = inst.rd as u32;
    fill_load_store(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &mem,
        inst.rd as u32,
        imm_felt,
        src_msb,
        w.shift_amount,
        src_addr_selector,
        dst_addr_selector,
        w.marker,
        [0, 1, 0, 0, 0, 0, 0, 0],
    );
}

pub fn lw(cpu: &mut Cpu, memory: &Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let mem = memory.read_u32_traced(addr, tracer);
    let value = mem.next;
    let rd = cpu.write_reg(inst.rd, value, tracer);
    cpu.advance_pc();

    let w = compute_load_store_witness(addr, false, false);
    let src_msb = (value >> 31) & 1;
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: lb=0, lh=0, lbu=0, lhu=0, lw=1, sb=0, sh=0, sw=0
    // For loads: dst=rd, src=mem, r2_idx=rd_addr
    // src_addr_selector = mem_addr - shift_amount, dst_addr_selector = r2_idx
    let src_addr_selector = addr - w.shift_amount;
    let dst_addr_selector = inst.rd as u32;
    fill_load_store(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &mem,
        inst.rd as u32,
        imm_felt,
        src_msb,
        w.shift_amount,
        src_addr_selector,
        dst_addr_selector,
        w.marker,
        [0, 0, 0, 0, 1, 0, 0, 0],
    );
}

pub fn lbu(cpu: &mut Cpu, memory: &Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let mem = memory.read_u8_traced(addr, tracer);
    let value = extract_byte(mem.next, addr) as u32; // Zero-extend
    let rd = cpu.write_reg(inst.rd, value, tracer);
    cpu.advance_pc();

    let w = compute_load_store_witness(addr, true, false);
    let imm_felt = imm_to_felt(inst.imm);
    let src_msb = (mem.next >> 31) & 1;

    // opcode flags: lb=0, lh=0, lbu=1, lhu=0, lw=0, sb=0, sh=0, sw=0
    // For loads: dst=rd, src=mem, r2_idx=rd_addr
    // src_addr_selector = mem_addr - shift_amount, dst_addr_selector = r2_idx
    let src_addr_selector = addr - w.shift_amount;
    let dst_addr_selector = inst.rd as u32;
    fill_load_store(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &mem,
        inst.rd as u32,
        imm_felt,
        src_msb,
        w.shift_amount,
        src_addr_selector,
        dst_addr_selector,
        w.marker,
        [0, 0, 1, 0, 0, 0, 0, 0],
    );
}

pub fn lhu(cpu: &mut Cpu, memory: &Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let mem = memory.read_u16_traced(addr, tracer);
    let value = extract_halfword(mem.next, addr) as u32; // Zero-extend
    let rd = cpu.write_reg(inst.rd, value, tracer);
    cpu.advance_pc();

    let w = compute_load_store_witness(addr, false, true);
    let imm_felt = imm_to_felt(inst.imm);
    let src_msb = (mem.next >> 31) & 1;

    // opcode flags: lb=0, lh=0, lbu=0, lhu=1, lw=0, sb=0, sh=0, sw=0
    // For loads: dst=rd, src=mem, r2_idx=rd_addr
    // src_addr_selector = mem_addr - shift_amount, dst_addr_selector = r2_idx
    let src_addr_selector = addr - w.shift_amount;
    let dst_addr_selector = inst.rd as u32;
    fill_load_store(
        tracer,
        old_pc,
        &rd,
        &rs1,
        &mem,
        inst.rd as u32,
        imm_felt,
        src_msb,
        w.shift_amount,
        src_addr_selector,
        dst_addr_selector,
        w.marker,
        [0, 0, 0, 1, 0, 0, 0, 0],
    );
}
