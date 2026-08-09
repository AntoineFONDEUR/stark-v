//! Minimal proof-capable load/store guest.

#![no_std]
#![no_main]

use core::arch::asm;

guest_bin::guest_main!({
    let mut word = 0x1122_3344u32;
    let value: u32;
    // The local word bounds both inline accesses to live aligned storage.
    unsafe {
        asm!(
            "li t0, 0x80",
            "sb t0, 2({address})",
            "lb {value}, 2({address})",
            address = in(reg) &mut word,
            value = lateout(reg) value,
            out("t0") _,
            options(nostack),
        );
    }
    value
});
