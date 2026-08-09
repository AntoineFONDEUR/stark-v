//! Minimal proof-capable register-comparison guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let lhs = u32::MAX;
    let rhs = 1u32;
    let value: u32;
    unsafe {
        asm!(
            "slt {value}, {lhs}, {rhs}",
            value = out(reg) value,
            lhs = in(reg) lhs,
            rhs = in(reg) rhs,
            options(nostack, nomem),
        );
    }
    value
});
