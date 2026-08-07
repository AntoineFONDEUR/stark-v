//! Utility functions and structs for ops modules.

/// M31 prime: 2^31 - 1
pub const M31_P: u32 = 2147483647;

/// Convert a signed i32 immediate to its M31 field representation.
/// Uses canonical reduction modulo P to safely handle edge cases like i32::MIN.
#[inline]
pub fn imm_to_felt(imm: i32) -> u32 {
    (imm as i64).rem_euclid(M31_P as i64) as u32
}

/// Compute the multiplicative inverse of a value in M31.
/// Uses Fermat's little theorem: a^(p-2) ≡ a^(-1) (mod p)
/// Returns 0 if the input is 0 (no inverse exists).
#[inline]
pub fn m31_inverse(a: u32) -> u32 {
    if a == 0 {
        return 0;
    }
    // a^(p-2) mod p where p = 2^31 - 1
    mod_pow(a as u64, (M31_P - 2) as u64, M31_P as u64) as u32
}

/// Modular exponentiation: base^exp mod modulus
fn mod_pow(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
    let mut result = 1u64;
    base %= modulus;
    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % modulus;
        }
        exp >>= 1;
        base = (base * base) % modulus;
    }
    result
}

// =============================================================================
// Shift Witness
// =============================================================================

/// Witness columns for shift operations (both register and immediate variants)
pub struct ShiftWitness {
    pub rs1_sign: u32,
    pub bit_shift_marker: [u32; 8],
    pub limb_shift_marker: [u32; 4],
    pub bit_shift_carry: [u32; 4],
}

/// Compute shift witness columns for both shifts_reg and shifts_imm families
pub fn compute_shift_witness(
    rs1_val: u32,
    shamt: u32,
    is_left: bool,
    is_sra: bool,
) -> ShiftWitness {
    let limb_shift = (shamt / 8) as usize;
    let bit_shift = (shamt % 8) as usize;

    // rs1_sign is the sign bit of rs1[3] (most significant byte)
    let rs1_sign = if is_sra { (rs1_val >> 31) & 1 } else { 0 };

    // Compute bit_shift_carry for each limb
    let rs1_bytes = rs1_val.to_le_bytes();
    let mut bit_shift_carry = [0u32; 4];
    for i in 0..4 {
        bit_shift_carry[i] = if bit_shift == 0 {
            0
        } else if is_left {
            // For left shifts, carry is the upper bits that overflow into the next byte
            (rs1_bytes[i] as u32) >> (8 - bit_shift)
        } else {
            // For right shifts, carry is the lower bits that are shifted out
            (rs1_bytes[i] as u32) & ((1 << bit_shift) - 1)
        };
    }

    ShiftWitness {
        rs1_sign,
        bit_shift_marker: create_one_hot_8(bit_shift),
        limb_shift_marker: create_one_hot_4(limb_shift),
        bit_shift_carry,
    }
}

// =============================================================================
// Helper functions
// =============================================================================

/// Create a one-hot array of size 4 with the bit at `index` set to 1.
#[inline]
pub fn create_one_hot_4(index: usize) -> [u32; 4] {
    let mut result = [0u32; 4];
    if index < 4 {
        result[index] = 1;
    }
    result
}

/// Create a one-hot array of size 8 with the bit at `index` set to 1.
#[inline]
pub fn create_one_hot_8(index: usize) -> [u32; 8] {
    let mut result = [0u32; 8];
    if index < 8 {
        result[index] = 1;
    }
    result
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_one_hot_4() {
        assert_eq!(create_one_hot_4(0), [1, 0, 0, 0]);
        assert_eq!(create_one_hot_4(1), [0, 1, 0, 0]);
        assert_eq!(create_one_hot_4(2), [0, 0, 1, 0]);
        assert_eq!(create_one_hot_4(3), [0, 0, 0, 1]);
        assert_eq!(create_one_hot_4(4), [0, 0, 0, 0]); // out of bounds
    }

    #[test]
    fn test_create_one_hot_8() {
        assert_eq!(create_one_hot_8(0), [1, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(create_one_hot_8(7), [0, 0, 0, 0, 0, 0, 0, 1]);
        assert_eq!(create_one_hot_8(8), [0, 0, 0, 0, 0, 0, 0, 0]); // out of bounds
    }

    #[test]
    fn test_shift_witness_left() {
        let w = compute_shift_witness(0x12345678, 5, true, false);
        assert_eq!(w.rs1_sign, 0); // not sra
        assert_eq!(w.bit_shift_marker, [0, 0, 0, 0, 0, 1, 0, 0]); // bit 5
        assert_eq!(w.limb_shift_marker, [1, 0, 0, 0]); // limb 0
    }

    #[test]
    fn test_shift_witness_right_arithmetic() {
        let w = compute_shift_witness(0x80000000, 8, false, true);
        assert_eq!(w.rs1_sign, 1); // sra with negative number
        assert_eq!(w.bit_shift_marker, [1, 0, 0, 0, 0, 0, 0, 0]); // bit 0 (8 % 8)
        assert_eq!(w.limb_shift_marker, [0, 1, 0, 0]); // limb 1 (8 / 8)
    }
}
