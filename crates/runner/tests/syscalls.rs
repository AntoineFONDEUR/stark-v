//! End-to-end syscall decoding and runner dispatch rejection.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::{RunError, run};

#[test]
fn unsupported_ecall_reaches_the_internal_dispatcher() {
    ensure_guest_built();
    let elf_path = guest_bin_dir().join("unsupported_ecall");
    let elf = std::fs::read(&elf_path)
        .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));

    assert!(matches!(
        run(&elf, 10_000),
        Err(RunError::UnsupportedSyscall { id: 7, .. })
    ));
}
