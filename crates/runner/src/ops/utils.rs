//! Utility functions and structs for ops modules.

/// M31 prime: 2^31 - 1
pub const M31_P: u32 = 2147483647;

/// Convert a signed i32 immediate to its M31 field representation.
/// Uses canonical reduction modulo P to safely handle edge cases like i32::MIN.
#[inline]
pub fn imm_to_felt(imm: i32) -> u32 {
    (imm as i64).rem_euclid(M31_P as i64) as u32
}
