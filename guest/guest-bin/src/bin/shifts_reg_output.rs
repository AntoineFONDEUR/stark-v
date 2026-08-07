//! Minimal proof-capable register-shift guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let value = 0x8000_0001u32;
    let amount = 31u32;
    let left: u32;
    let logical: u32;
    let arithmetic: u32;
    unsafe {
        asm!(
            "sll {left}, {value}, {amount}",
            "srl {logical}, {value}, {amount}",
            "sra {arithmetic}, {value}, {amount}",
            left = out(reg) left,
            logical = out(reg) logical,
            arithmetic = out(reg) arithmetic,
            value = in(reg) value,
            amount = in(reg) amount,
            options(nostack, nomem),
        );
    }
    left ^ logical ^ arithmetic
});
