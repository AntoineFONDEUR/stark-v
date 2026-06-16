//! Store operations - part of load_store family (airs.md Section 13)

use super::utils::imm_to_felt;
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, Memory};

/// Compute load/store witness columns for stores
fn compute_store_witness(addr: u32, is_byte: bool, is_half: bool) -> StoreWitness {
    let byte_offset = addr & 3;
    let shift_amount = if is_byte {
        byte_offset
    } else if is_half {
        byte_offset & 2
    } else {
        0
    };

    // One-hot encoding of byte position
    let mut marker = [0u32; 4];
    if is_byte {
        marker[byte_offset as usize] = 1;
    } else if is_half {
        if byte_offset < 2 {
            marker[0] = 1;
            marker[1] = 1;
        } else {
            marker[2] = 1;
            marker[3] = 1;
        }
    }

    StoreWitness {
        shift_amount,
        marker,
    }
}

struct StoreWitness {
    shift_amount: u32,
    marker: [u32; 4],
}

pub fn sb(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let value = rs2.next as u8;
    let mem = memory.write_u8_traced(addr, value, tracer);
    cpu.advance_pc();

    let w = compute_store_witness(addr, true, false);
    let imm_felt = imm_to_felt(inst.imm);
    let src_msb = (value >> 7) & 1;

    // opcode flags: lb=0, lh=0, lbu=0, lhu=0, lw=0, sb=1, sh=0, sw=0
    // For stores: dst=mem, src=rs2, r2_idx=rs2_idx
    // src_addr_selector = r2_idx, dst_addr_selector = mem_addr - shift_amount
    let src_addr_selector = inst.rs2 as u32;
    let dst_addr_selector = addr - w.shift_amount;
    trace_op!(load_store: tracer, old_pc, mem, rs1, rs2,
        inst.rs2 as u32, imm_felt, src_msb as u32,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 0, 0, 0, 1, 0, 0
    );
}

pub fn sh(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let value = rs2.next as u16;
    let mem = memory.write_u16_traced(addr, value, tracer);
    cpu.advance_pc();

    let w = compute_store_witness(addr, false, true);
    let imm_felt = imm_to_felt(inst.imm);
    let src_msb = (value >> 15) & 1;

    // opcode flags: lb=0, lh=0, lbu=0, lhu=0, lw=0, sb=0, sh=1, sw=0
    // For stores: dst=mem, src=rs2, r2_idx=rs2_idx
    // src_addr_selector = r2_idx, dst_addr_selector = mem_addr - shift_amount
    let src_addr_selector = inst.rs2 as u32;
    let dst_addr_selector = addr - w.shift_amount;
    trace_op!(load_store: tracer, old_pc, mem, rs1, rs2,
        inst.rs2 as u32, imm_felt, src_msb as u32,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 0, 0, 0, 0, 1, 0
    );
}

pub fn sw(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let addr = rs1.next.wrapping_add(inst.imm as u32);
    let value = rs2.next;
    let mem = memory.write_u32_traced(addr, value, tracer);
    cpu.advance_pc();

    let w = compute_store_witness(addr, false, false);
    let imm_felt = imm_to_felt(inst.imm);
    let src_msb = (value >> 31) & 1;

    // opcode flags: lb=0, lh=0, lbu=0, lhu=0, lw=0, sb=0, sh=0, sw=1
    // For stores: dst=mem, src=rs2, r2_idx=rs2_idx
    // src_addr_selector = r2_idx, dst_addr_selector = mem_addr - shift_amount
    let src_addr_selector = inst.rs2 as u32;
    let dst_addr_selector = addr - w.shift_amount;
    trace_op!(load_store: tracer, old_pc, mem, rs1, rs2,
        inst.rs2 as u32, imm_felt, src_msb,
        w.shift_amount,
        src_addr_selector, dst_addr_selector,
        w.marker[0], w.marker[1], w.marker[2], w.marker[3],
        0, 0, 0, 0, 0, 0, 0, 1
    );
}
