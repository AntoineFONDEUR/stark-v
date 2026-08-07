//! Guest fixture for two execution-ordered proof-bound COMMIT calls.

#![no_std]
#![no_main]

#[unsafe(no_mangle)]
pub extern "C" fn __zkvm_start() -> ! {
    // Distinct words make any change in the authenticated order observable.
    guest_lib::commit(0x1122_3344);
    guest_lib::commit(0x5566_7788);
    guest_bin::glue::output_raw(&[])
}
