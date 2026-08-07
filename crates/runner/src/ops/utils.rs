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
