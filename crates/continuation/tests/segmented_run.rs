//! End-to-end proof generation and host verification for a segmented guest run.

use continuation::{prove_segments, verify_segments};
use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::run_segments_with_input;
use stwo::core::pcs::PcsConfig;

#[test_log::test]
fn segmented_run_produces_a_valid_continuation() {
    ensure_guest_built();
    let elf_bytes = std::fs::read(guest_bin_dir().join("mulhu_alias"))
        .expect("the mulhu_alias guest binary is readable");
    let cycles = runner::run(&elf_bytes, 10_000_000)
        .expect("the mulhu_alias guest runs")
        .cycles;
    // Halving the cycle budget exercises at least one internal boundary while
    // keeping the proof count small enough for a focused integration test.
    let segment_cycles = u32::try_from(cycles / 2 + 1).expect("the cycle count fits in u32");
    let segments = run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 10_000_000)
        .expect("the segmented guest run succeeds");
    let config = PcsConfig::default();
    let preprocessing = prover::preprocess(config);
    let proofs = prove_segments(segments, config, &preprocessing);

    assert!(verify_segments(proofs, config, &preprocessing).is_ok());
}
