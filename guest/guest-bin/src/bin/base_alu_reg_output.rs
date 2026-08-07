//! Minimal proof-capable register-ALU guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let lhs = u32::MAX - 1;
    let rhs = 5u32;
    let value: u32;
    unsafe {
        asm!(
            "add {value}, {lhs}, {rhs}",
            value = out(reg) value,
            lhs = in(reg) lhs,
            rhs = in(reg) rhs,
            options(nostack, nomem),
        );
    }
    value
});
