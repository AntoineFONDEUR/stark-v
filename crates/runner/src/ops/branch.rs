//! Branch operations.
//!
//! This file contains:
//! - branch_eq family: beq, bne (airs.md Section 7)
//! - branch_lt family: blt, bltu, bge, bgeu (airs.md Section 8)

use super::utils::{compute_lt_reg_witness, imm_to_felt, m31_inverse};
use crate::trace::Tracer;
use crate::{Cpu, DecodedInst};

/// Fill one branch_eq row from the rs1/rs2 reads, the immediate, the
/// comparison result, the inverse-witness markers, and the beq/bne flags.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_branch_eq(
    tracer: &mut Tracer,
    pc: u32,
    rs1: &crate::trace::Access,
    rs2: &crate::trace::Access,
    imm_felt: u32,
    cmp_result: u32,
    markers: [u32; 4],
    flags: [u32; 2],
) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;
    let clock = tracer.clock;
    let limbs = |a: &crate::trace::Access| {
        [
            f(a.addr),
            f(a.prev & 0xFF),
            f((a.prev >> 8) & 0xFF),
            f((a.prev >> 16) & 0xFF),
            f((a.prev >> 24) & 0xFF),
            f(a.clock_prev),
            f(a.next & 0xFF),
            f((a.next >> 8) & 0xFF),
            f((a.next >> 16) & 0xFF),
            f((a.next >> 24) & 0xFF),
        ]
    };
    let rs1 = limbs(rs1);
    let rs2 = limbs(rs2);
    air::opcodes::branch_eq::branch_eq_fill(
        &mut tracer.branch_eq,
        [
            f(clock),
            f(pc),
            rs1[0],
            rs1[1],
            rs1[2],
            rs1[3],
            rs1[4],
            rs1[5],
            rs1[6],
            rs1[7],
            rs1[8],
            rs1[9],
            rs2[0],
            rs2[1],
            rs2[2],
            rs2[3],
            rs2[4],
            rs2[5],
            rs2[6],
            rs2[7],
            rs2[8],
            rs2[9],
            f(imm_felt),
            f(cmp_result),
            f(markers[0]),
            f(markers[1]),
            f(markers[2]),
            f(markers[3]),
            f(flags[0]),
            f(flags[1]),
        ],
        [],
    );
}

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
    fill_branch_eq(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        imm_felt,
        cmp_result,
        [
            w.diff_inv_marker[0],
            w.diff_inv_marker[1],
            w.diff_inv_marker[2],
            w.diff_inv_marker[3],
        ],
        [1, 0],
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
    fill_branch_eq(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        imm_felt,
        cmp_result,
        [
            w.diff_inv_marker[0],
            w.diff_inv_marker[1],
            w.diff_inv_marker[2],
            w.diff_inv_marker[3],
        ],
        [0, 1],
    );
}

// =============================================================================
// Branch Less Than (blt/bltu/bge/bgeu) - airs.md Section 8
// =============================================================================

/// Fill one branch_lt row from the rs1/rs2 reads, the most-significant-limb
/// witnesses, the immediate, the comparison bits, difference markers, the
/// selected branch target and the blt/bltu/bge/bgeu flags.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fill_branch_lt(
    tracer: &mut Tracer,
    pc: u32,
    rs1: &crate::trace::Access,
    rs2: &crate::trace::Access,
    rs1_msl_felt: u32,
    rs2_msl_felt: u32,
    imm_felt: u32,
    cmp_result: u32,
    cmp_lt: u32,
    diff_marker: [u32; 4],
    diff_val: u32,
    branch_target: u32,
    flags: [u32; 4],
) {
    use stwo::core::fields::m31::BaseField;
    let f = BaseField::from_u32_unchecked;
    let clock = tracer.clock;
    let limbs = |a: &crate::trace::Access| {
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
    let mut args = Vec::with_capacity(37);
    args.extend([clock, pc]);
    args.extend(limbs(rs1));
    args.extend(limbs(rs2));
    args.extend([rs1_msl_felt, rs2_msl_felt, imm_felt, cmp_result, cmp_lt]);
    args.extend(diff_marker);
    args.extend([diff_val, branch_target]);
    args.extend(flags);
    air::opcodes::branch_lt::branch_lt_fill(
        &mut tracer.branch_lt,
        args.into_iter()
            .map(f)
            .collect::<Vec<_>>()
            .try_into()
            .expect("branch_lt fill takes 37 felts"),
        [],
    );
}

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
    fill_branch_lt(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        imm_felt,
        cmp_result,
        cmp_lt,
        w.diff_marker,
        w.diff_val,
        branch_target,
        [1, 0, 0, 0],
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
    fill_branch_lt(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        imm_felt,
        cmp_result,
        cmp_lt,
        w.diff_marker,
        w.diff_val,
        branch_target,
        [0, 1, 0, 0],
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
    fill_branch_lt(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        imm_felt,
        cmp_result,
        cmp_lt,
        w.diff_marker,
        w.diff_val,
        branch_target,
        [0, 0, 1, 0],
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
    fill_branch_lt(
        tracer,
        old_pc,
        &rs1,
        &rs2,
        w.rs1_msl_felt,
        w.rs2_msl_felt,
        imm_felt,
        cmp_result,
        cmp_lt,
        w.diff_marker,
        w.diff_val,
        branch_target,
        [0, 0, 0, 1],
    );
}
