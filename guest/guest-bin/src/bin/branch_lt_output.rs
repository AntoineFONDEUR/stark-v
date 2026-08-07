//! Minimal proof-capable ordered-branch guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let lhs = u32::MAX;
    let rhs = 1u32;
    let value: u32;
    unsafe {
        asm!(
            "blt {lhs}, {rhs}, 2f",
            "li {value}, 0",
            "j 3f",
            "2:",
            "li {value}, 1",
            "3:",
            value = out(reg) value,
            lhs = in(reg) lhs,
            rhs = in(reg) rhs,
            options(nostack, nomem),
        );
    }
    value
});
