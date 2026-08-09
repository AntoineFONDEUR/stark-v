//! Minimal proof-capable immediate-shift guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let value = 0x8000_0001u32;
    let left: u32;
    let logical: u32;
    let arithmetic: u32;
    unsafe {
        asm!(
            "slli {left}, {value}, 31",
            "srli {logical}, {value}, 31",
            "srai {arithmetic}, {value}, 31",
            left = out(reg) left,
            logical = out(reg) logical,
            arithmetic = out(reg) arithmetic,
            value = in(reg) value,
            options(nostack, nomem),
        );
    }
    left ^ logical ^ arithmetic
});
