//! Minimal proof-capable LUI guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let value: u32;
    unsafe {
        asm!(
            "lui {value}, 0x12345",
            value = out(reg) value,
            options(nostack, nomem),
        );
    }
    value
});
