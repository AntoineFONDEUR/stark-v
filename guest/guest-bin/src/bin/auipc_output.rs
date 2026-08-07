//! Minimal proof-capable AUIPC guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let value: u32;
    unsafe {
        asm!(
            "auipc {value}, 0",
            value = out(reg) value,
            options(nostack, nomem),
        );
    }
    value
});
