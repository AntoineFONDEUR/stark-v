//! Capacity segmentation rejects a segment whose finalized tables exceed the budget.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::{RunError, run_segments_by_capacity};

#[test]
fn finalized_segment_cannot_exceed_capacity() {
    ensure_guest_built();

    let elf_path = guest_bin_dir().join("constant");
    let elf_bytes = std::fs::read(&elf_path)
        .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));

    let result = run_segments_by_capacity(&elf_bytes, &[], 64, 10_000);

    assert!(matches!(
        result,
        Err(RunError::FinalizedSegmentCapacityExceeded {
            rows,
            max_rows: 64,
            ..
        }) if rows > 64
    ));
}
