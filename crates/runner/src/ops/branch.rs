//! Branch operations.
//!
//! This file contains:
//! - branch_eq family: beq, bne (airs.md Section 7)
//! - branch_lt family: blt, bltu, bge, bgeu (airs.md Section 8)

use super::utils::{compute_lt_reg_witness, imm_to_felt, m31_inverse};
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

// =============================================================================
// Branch Equal (beq/bne) - airs.md Section 7
// =============================================================================

/// Compute witness columns for branch_eq family
fn compute_branch_eq_witness(rs1_val: u32, rs2_val: u32) -> BranchEqWitness {
    let rs1_bytes = rs1_val.to_le_bytes();
    let rs2_bytes = rs2_val.to_le_bytes();

    // diff_inv_marker[i] = (rs1[i] - rs2[i])^-1 if rs1[i] != rs2[i], else 0
    let mut diff_inv_marker = [0u32; 4];
    for i in 0..4 {
        if rs1_bytes[i] != rs2_bytes[i] {
            // Compute the difference in M31 (handling potential wrap-around)
            let diff = if rs1_bytes[i] > rs2_bytes[i] {
                (rs1_bytes[i] - rs2_bytes[i]) as u32
            } else {
                // rs2_bytes[i] > rs1_bytes[i], so diff is negative
                // In M31: P - (rs2_bytes[i] - rs1_bytes[i])
                super::utils::M31_P - (rs2_bytes[i] - rs1_bytes[i]) as u32
            };
            diff_inv_marker[i] = m31_inverse(diff);
            break; // Only need the first difference
        }
    }

    BranchEqWitness { diff_inv_marker }
}

struct BranchEqWitness {
    diff_inv_marker: [u32; 4],
}

pub fn beq(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_result = if rs1.next == rs2.next { 1 } else { 0 };

    let old_pc = cpu.pc;
    if rs1.next == rs2.next {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let w = compute_branch_eq_witness(rs1.next, rs2.next);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: beq=1, bne=0
    trace_op!(branch_eq: tracer, old_pc, rs1, rs2,
        imm_felt, cmp_result,
        w.diff_inv_marker[0], w.diff_inv_marker[1], w.diff_inv_marker[2], w.diff_inv_marker[3],
        1, 0
    );
}

pub fn bne(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_result = if rs1.next != rs2.next { 1 } else { 0 };

    let old_pc = cpu.pc;
    if rs1.next != rs2.next {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let w = compute_branch_eq_witness(rs1.next, rs2.next);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: beq=0, bne=1
    trace_op!(branch_eq: tracer, old_pc, rs1, rs2,
        imm_felt, cmp_result,
        w.diff_inv_marker[0], w.diff_inv_marker[1], w.diff_inv_marker[2], w.diff_inv_marker[3],
        0, 1
    );
}

// =============================================================================
// Branch Less Than (blt/bltu/bge/bgeu) - airs.md Section 8
// =============================================================================

pub fn blt(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_lt = if (rs1.next as i32) < (rs2.next as i32) {
        1
    } else {
        0
    };
    let cmp_result = cmp_lt; // For blt, branch if less than

    let old_pc = cpu.pc;
    if cmp_result == 1 {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let branch_target = cpu.pc;
    let w = compute_lt_reg_witness(rs1.next, rs2.next, true);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: blt=1, bltu=0, bge=0, bgeu=0
    trace_op!(branch_lt: tracer, old_pc, rs1, rs2,
        w.rs1_msl_felt, w.rs2_msl_felt,
        imm_felt, cmp_result, cmp_lt,
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val, branch_target,
        1, 0, 0, 0
    );
}

pub fn bltu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_lt = if rs1.next < rs2.next { 1 } else { 0 };
    let cmp_result = cmp_lt; // For bltu, branch if less than

    let old_pc = cpu.pc;
    if cmp_result == 1 {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let branch_target = cpu.pc;
    let w = compute_lt_reg_witness(rs1.next, rs2.next, false);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: blt=0, bltu=1, bge=0, bgeu=0
    trace_op!(branch_lt: tracer, old_pc, rs1, rs2,
        w.rs1_msl_felt, w.rs2_msl_felt,
        imm_felt, cmp_result, cmp_lt,
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val, branch_target,
        0, 1, 0, 0
    );
}

pub fn bge(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_lt = if (rs1.next as i32) < (rs2.next as i32) {
        1
    } else {
        0
    };
    let cmp_result = if (rs1.next as i32) >= (rs2.next as i32) {
        1
    } else {
        0
    };

    let old_pc = cpu.pc;
    if cmp_result == 1 {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let branch_target = cpu.pc;
    let w = compute_lt_reg_witness(rs1.next, rs2.next, true);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: blt=0, bltu=0, bge=1, bgeu=0
    trace_op!(branch_lt: tracer, old_pc, rs1, rs2,
        w.rs1_msl_felt, w.rs2_msl_felt,
        imm_felt, cmp_result, cmp_lt,
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val, branch_target,
        0, 0, 1, 0
    );
}

pub fn bgeu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let cmp_lt = if rs1.next < rs2.next { 1 } else { 0 };
    let cmp_result = if rs1.next >= rs2.next { 1 } else { 0 };

    let old_pc = cpu.pc;
    if cmp_result == 1 {
        cpu.pc = cpu.pc.wrapping_add(inst.imm as u32);
    } else {
        cpu.advance_pc();
    }

    let branch_target = cpu.pc;
    let w = compute_lt_reg_witness(rs1.next, rs2.next, false);
    let imm_felt = imm_to_felt(inst.imm);

    // opcode flags: blt=0, bltu=0, bge=0, bgeu=1
    trace_op!(branch_lt: tracer, old_pc, rs1, rs2,
        w.rs1_msl_felt, w.rs2_msl_felt,
        imm_felt, cmp_result, cmp_lt,
        w.diff_marker[0], w.diff_marker[1], w.diff_marker[2], w.diff_marker[3],
        w.diff_val, branch_target,
        0, 0, 0, 1
    );
}
