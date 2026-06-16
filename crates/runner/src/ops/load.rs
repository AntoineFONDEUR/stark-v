//! Load operations - part of load_store family (airs.md Section 13)

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, Memory};

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
    trace_op!(load_store: tracer, old_pc, rd, rs1, mem,
        inst.rd as u32, imm_felt, src_msb,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        1, 0, 0, 0, 0, 0, 0, 0
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
    trace_op!(load_store: tracer, old_pc, rd, rs1, mem,
        inst.rd as u32, imm_felt, src_msb,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 1, 0, 0, 0, 0, 0, 0
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
    trace_op!(load_store: tracer, old_pc, rd, rs1, mem,
        inst.rd as u32, imm_felt, src_msb,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 0, 0, 1, 0, 0, 0
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
    trace_op!(load_store: tracer, old_pc, rd, rs1, mem,
        inst.rd as u32, imm_felt, src_msb, // needed to reconstruct top byte in AIR
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 1, 0, 0, 0, 0, 0
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
    trace_op!(load_store: tracer, old_pc, rd, rs1, mem,
        inst.rd as u32, imm_felt, src_msb, // needed to reconstruct top byte in AIR
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 0, 1, 0, 0, 0, 0
    );
}
