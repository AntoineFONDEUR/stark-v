//! The runner rejects stores into the read-only code region rather than
//! silently writing to a location that cannot affect what executes.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::{MemoryFaultKind, RunError, run};

#[test]
fn test_store_into_text_faults() {
    ensure_guest_built();

    let elf_path = guest_bin_dir().join("store_into_text");
    let elf_bytes =
        std::fs::read(&elf_path).unwrap_or_else(|e| panic!("Failed to read {elf_path:?}: {e}"));

    let err = run(&elf_bytes, 10_000_000).expect_err("store into TEXT must fault");
    assert!(matches!(
        err,
        RunError::MemoryFault {
            kind: MemoryFaultKind::StoreIntoText,
            ..
        }
    ));
}
