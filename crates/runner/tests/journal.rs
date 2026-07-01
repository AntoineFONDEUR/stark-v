//! The COMMIT syscall (ECALL) absorbs words into a running Poseidon2 journal
//! sponge whose final digest is the run's committed output, and the sponge
//! state chains correctly across continuation segments.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::ops::system::{Journal, absorb};
use runner::{run, run_segments_with_input};

/// Recompute the journal the `journal` guest should produce: it commits
/// `i * 0x9e3779b9 + 1` for i in 0..8, starting from the all-zero sponge.
fn expected_journal() -> Journal {
    let mut state = [0u32; 16];
    for i in 0..8u32 {
        let word = i.wrapping_mul(0x9e37_79b9).wrapping_add(1);
        state = absorb(&state, word);
    }
    state
}

#[test]
fn test_journal_matches_host_recomputation() {
    ensure_guest_built();
    let elf = std::fs::read(guest_bin_dir().join("journal")).expect("read journal ELF");
    let result = run(&elf, 10_000_000).expect("run journal");
    assert_eq!(result.final_journal, expected_journal());
}

#[test]
fn test_journal_chains_across_segments() {
    ensure_guest_built();
    let elf = std::fs::read(guest_bin_dir().join("journal")).expect("read journal ELF");

    // Force several segments; the last segment's final journal must equal the
    // whole-run digest, and adjacent segments must chain (left.final ==
    // right.initial).
    let whole = run(&elf, 10_000_000).expect("run journal");
    let segment_cycles = u32::try_from(whole.cycles / 4 + 1).expect("fits u32");
    let segments = run_segments_with_input(&elf, &[], Some(segment_cycles), 10_000_000)
        .expect("segmented run");

    assert_eq!(
        segments.last().expect("segments").final_journal,
        whole.final_journal
    );
}

#[test]
fn test_segment_journals_are_contiguous() {
    ensure_guest_built();
    let elf = std::fs::read(guest_bin_dir().join("journal")).expect("read journal ELF");
    let whole = run(&elf, 10_000_000).expect("run journal");
    let segment_cycles = u32::try_from(whole.cycles / 4 + 1).expect("fits u32");
    let segments = run_segments_with_input(&elf, &[], Some(segment_cycles), 10_000_000)
        .expect("segmented run");

    let broken = segments
        .windows(2)
        .any(|pair| pair[0].final_journal != pair[1].initial_journal);
    assert!(
        !broken,
        "journal state must chain across segment boundaries"
    );
}

#[test]
fn test_first_segment_journal_starts_at_genesis() {
    ensure_guest_built();
    let elf = std::fs::read(guest_bin_dir().join("journal")).expect("read journal ELF");
    let segments = run_segments_with_input(&elf, &[], Some(4), 10_000_000).expect("segmented run");
    assert_eq!(segments[0].initial_journal, [0u32; 16]);
}
