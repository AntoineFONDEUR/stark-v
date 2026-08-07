//! Minimal proof-capable immediate-comparison guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let lhs = i32::MIN as u32;
    let value: u32;
    unsafe {
        asm!(
            "slti {value}, {lhs}, -2048",
            value = out(reg) value,
            lhs = in(reg) lhs,
            options(nostack, nomem),
        );
    }
    value
});
