//! Minimal proof-capable immediate-ALU guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let lhs = 0u32;
    let value: u32;
    unsafe {
        asm!(
            "addi {value}, {lhs}, -1",
            value = out(reg) value,
            lhs = in(reg) lhs,
            options(nostack, nomem),
        );
    }
    value
});
