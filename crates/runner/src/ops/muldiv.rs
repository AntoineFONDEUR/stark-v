//! Multiply/Divide operations (M extension).
//!
//! This file contains:
//! - mul family: mul
//! - mulh family: mulh, mulhsu, mulhu
//! - div family: div, divu, rem, remu

use super::utils::{M31_P, m31_inverse};
use air::opcodes::mul::mul_fill;
use air::opcodes::mulh::mulh_fill;
use stwo::core::fields::m31::BaseField;

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, MachineState, Memory};

// =============================================================================
// MUL
// =============================================================================

pub fn mul(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    // Generated execution binds the wrapping product to the traced accesses.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        u32::from(inst.rs2),
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        mul_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

// =============================================================================
// MULH (mulh/mulhsu/mulhu)
// =============================================================================

fn execute_mulh(
    cpu: &mut Cpu,
    memory: &mut Memory,
    inst: &DecodedInst,
    tracer: &mut Tracer,
    flags: [u32; 3],
) {
    // Decoding selects signedness; generated execution owns the wide product.
    let args = [
        tracer.clock,
        cpu.pc,
        u32::from(inst.rd),
        u32::from(inst.rs1),
        u32::from(inst.rs2),
        flags[0],
        flags[1],
        flags[2],
    ]
    .map(BaseField::from_u32_unchecked);
    let [next_pc] = {
        let mut state = MachineState::new(cpu, memory);
        mulh_fill(&mut state, tracer, args, [])
    };
    cpu.pc = next_pc.0;
}

pub fn mulh(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [1, 0, 0]);
}

pub fn mulhsu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [0, 1, 0]);
}

pub fn mulhu(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_mulh(cpu, memory, inst, tracer, [0, 0, 1]);
}

// =============================================================================
// DIV (div/divu/rem/remu)
// =============================================================================

/// Compute division witness columns
fn compute_div_witness(rs1_val: u32, rs2_val: u32, is_signed: bool) -> DivWitness {
    const LIMB_BITS: u32 = 8;
    const LIMB_BASE: u32 = 1 << LIMB_BITS;
    const LIMB_MASK: u32 = LIMB_BASE - 1;
    const MSB_MASK: u32 = 1 << (LIMB_BITS - 1);

    let b_limbs = rs1_val.to_le_bytes().map(|b| b as u32);
    let c_limbs = rs2_val.to_le_bytes().map(|b| b as u32);

    let b_sign = (is_signed && (b_limbs[3] & MSB_MASK) != 0) as u32;
    let c_sign = (is_signed && (c_limbs[3] & MSB_MASK) != 0) as u32;
    let zero_divisor = (rs2_val == 0) as u32;
    let overflow = is_signed && rs1_val == 0x8000_0000 && rs2_val == 0xFFFF_FFFF;

    let (q, r, q_sign) = if zero_divisor == 1 {
        (u32::MAX, rs1_val, is_signed as u32)
    } else if overflow {
        (rs1_val, 0, 0)
    } else if is_signed {
        let a = rs1_val as i32;
        let b = rs2_val as i32;
        let quot = a.wrapping_div(b);
        let rem = a.wrapping_rem(b);
        let q_val = quot as u32;
        let q_sign = (q_val >> 31) & 1;
        (q_val, rem as u32, q_sign)
    } else {
        (
            rs1_val.wrapping_div(rs2_val),
            rs1_val.wrapping_rem(rs2_val),
            0,
        )
    };

    let sign_xor = b_sign ^ c_sign;
    let r_zero = (r == 0 && zero_divisor == 0) as u32;

    let q_limbs = [
        (q & LIMB_MASK),
        ((q >> 8) & LIMB_MASK),
        ((q >> 16) & LIMB_MASK),
        ((q >> 24) & LIMB_MASK),
    ];
    let r_limbs = [
        (r & LIMB_MASK),
        ((r >> 8) & LIMB_MASK),
        ((r >> 16) & LIMB_MASK),
        ((r >> 24) & LIMB_MASK),
    ];

    let r_prime = if sign_xor == 1 {
        negate_limbs(&r_limbs)
    } else {
        r_limbs
    };

    let r_inv = r_prime.map(|limb| m31_inverse(M31_P - LIMB_BASE + limb));

    let (lt_marker, lt_diff) = if zero_divisor == 0 && r_zero == 0 && !overflow {
        let idx = run_sltu_diff_idx(&c_limbs, &r_prime, c_sign == 1);
        let mut marker = [0u32; 4];
        let mut diff = 0u32;
        if idx < 4 {
            marker[idx] = 1;
            diff = if c_sign == 1 {
                r_prime[idx].wrapping_sub(c_limbs[idx])
            } else {
                c_limbs[idx].wrapping_sub(r_prime[idx])
            };
        }
        (marker, diff)
    } else {
        ([0u32; 4], 0)
    };

    let c_sum: u32 = c_limbs.iter().sum();
    let c_sum_inv = if c_sum == 0 { 0 } else { m31_inverse(c_sum) };

    let r_sum: u32 = r_limbs.iter().sum();
    let r_sum_inv = if r_sum == 0 { 0 } else { m31_inverse(r_sum) };

    DivWitness {
        zero_divisor,
        r_zero,
        q: q_limbs,
        r: r_limbs,
        b_sign,
        c_sign,
        q_sign,
        sign_xor,
        c_sum_inv,
        r_sum_inv,
        r_abs: r_prime,
        r_inv,
        lt_marker,
        lt_diff,
    }
}

struct DivWitness {
    zero_divisor: u32,
    r_zero: u32,
    q: [u32; 4],
    r: [u32; 4],
    b_sign: u32,
    c_sign: u32,
    q_sign: u32,
    sign_xor: u32,
    c_sum_inv: u32,
    r_sum_inv: u32,
    r_abs: [u32; 4],
    r_inv: [u32; 4],
    lt_marker: [u32; 4],
    lt_diff: u32,
}

fn negate_limbs(limbs: &[u32; 4]) -> [u32; 4] {
    let mut carry = 1u32;
    let mut out = [0u32; 4];
    for (i, limb) in limbs.iter().enumerate() {
        let val = 256 + carry - 1 - limb;
        carry = val >> 8;
        out[i] = val & 0xFF;
    }
    out
}

fn run_sltu_diff_idx(c: &[u32; 4], r_prime: &[u32; 4], cmp: bool) -> usize {
    for i in (0..4).rev() {
        if c[i] != r_prime[i] {
            debug_assert!((c[i] < r_prime[i]) == cmp);
            return i;
        }
    }
    debug_assert!(!cmp);
    4
}

pub fn div(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let rs1_val = rs1.next as i32;
    let rs2_val = rs2.next as i32;
    let result = if rs2_val == 0 {
        u32::MAX
    } else if rs1_val == i32::MIN && rs2_val == -1 {
        rs1_val as u32
    } else {
        rs1_val.wrapping_div(rs2_val) as u32
    };
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_div_witness(rs1.next, rs2.next, true);

    // opcode flags: div=1, divu=0, rem=0, remu=0
    trace_op!(div: tracer, old_pc, rd, rs1, rs2,
        w.zero_divisor, w.r_zero,
        w.q[0], w.q[1], w.q[2], w.q[3],
        w.r[0], w.r[1], w.r[2], w.r[3],
        w.b_sign, w.c_sign, w.q_sign, w.sign_xor,
        w.c_sum_inv, w.r_sum_inv,
        w.r_abs[0], w.r_abs[1], w.r_abs[2], w.r_abs[3],
        w.r_inv[0], w.r_inv[1], w.r_inv[2], w.r_inv[3],
        w.lt_marker[0], w.lt_marker[1], w.lt_marker[2], w.lt_marker[3],
        w.lt_diff,
        1, 0, 0, 0
    );
}

pub fn divu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = if rs2.next == 0 {
        u32::MAX
    } else {
        rs1.next.wrapping_div(rs2.next)
    };
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_div_witness(rs1.next, rs2.next, false);

    // opcode flags: div=0, divu=1, rem=0, remu=0
    trace_op!(div: tracer, old_pc, rd, rs1, rs2,
        w.zero_divisor, w.r_zero,
        w.q[0], w.q[1], w.q[2], w.q[3],
        w.r[0], w.r[1], w.r[2], w.r[3],
        w.b_sign, w.c_sign, w.q_sign, w.sign_xor,
        w.c_sum_inv, w.r_sum_inv,
        w.r_abs[0], w.r_abs[1], w.r_abs[2], w.r_abs[3],
        w.r_inv[0], w.r_inv[1], w.r_inv[2], w.r_inv[3],
        w.lt_marker[0], w.lt_marker[1], w.lt_marker[2], w.lt_marker[3],
        w.lt_diff,
        0, 1, 0, 0
    );
}

pub fn rem(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let rs1_val = rs1.next as i32;
    let rs2_val = rs2.next as i32;
    let result = if rs2_val == 0 {
        rs1_val as u32
    } else if rs1_val == i32::MIN && rs2_val == -1 {
        0
    } else {
        rs1_val.wrapping_rem(rs2_val) as u32
    };
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_div_witness(rs1.next, rs2.next, true);

    // opcode flags: div=0, divu=0, rem=1, remu=0
    trace_op!(div: tracer, old_pc, rd, rs1, rs2,
        w.zero_divisor, w.r_zero,
        w.q[0], w.q[1], w.q[2], w.q[3],
        w.r[0], w.r[1], w.r[2], w.r[3],
        w.b_sign, w.c_sign, w.q_sign, w.sign_xor,
        w.c_sum_inv, w.r_sum_inv,
        w.r_abs[0], w.r_abs[1], w.r_abs[2], w.r_abs[3],
        w.r_inv[0], w.r_inv[1], w.r_inv[2], w.r_inv[3],
        w.lt_marker[0], w.lt_marker[1], w.lt_marker[2], w.lt_marker[3],
        w.lt_diff,
        0, 0, 1, 0
    );
}

pub fn remu(cpu: &mut Cpu, inst: &DecodedInst, tracer: &mut Tracer) {
    let old_pc = cpu.pc;
    let rs1 = cpu.read_reg(inst.rs1, tracer);
    let rs2 = cpu.read_reg(inst.rs2, tracer);
    let result = if rs2.next == 0 {
        rs1.next
    } else {
        rs1.next.wrapping_rem(rs2.next)
    };
    let rd = cpu.write_reg(inst.rd, result, tracer);
    cpu.advance_pc();

    let w = compute_div_witness(rs1.next, rs2.next, false);

    // opcode flags: div=0, divu=0, rem=0, remu=1
    trace_op!(div: tracer, old_pc, rd, rs1, rs2,
        w.zero_divisor, w.r_zero,
        w.q[0], w.q[1], w.q[2], w.q[3],
        w.r[0], w.r[1], w.r[2], w.r[3],
        w.b_sign, w.c_sign, w.q_sign, w.sign_xor,
        w.c_sum_inv, w.r_sum_inv,
        w.r_abs[0], w.r_abs[1], w.r_abs[2], w.r_abs[3],
        w.r_inv[0], w.r_inv[1], w.r_inv[2], w.r_inv[3],
        w.lt_marker[0], w.lt_marker[1], w.lt_marker[2], w.lt_marker[3],
        w.lt_diff,
        0, 0, 0, 1
    );
}
