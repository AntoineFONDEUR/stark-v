//! End-to-end syscall decoding and runner dispatch rejection.

use prover::e2e::{ensure_guest_built, guest_bin_dir};
use runner::instructions::COMMIT_HASH_DOMAIN;
use runner::poseidon2::{DIGEST_WORDS, T, poseidon2_permutation};
use runner::{RunError, RunResult, run, run_segments_with_input};

/// Execute the one-COMMIT fixture with its proof-facing output word.
fn run_commit_once() -> RunResult {
    ensure_guest_built();
    let elf_path = guest_bin_dir().join("commit_once");
    let elf = std::fs::read(&elf_path)
        .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));
    run(&elf, 10_000).expect("the proof-backed COMMIT call executes")
}

/// Split the fixture tightly enough to exercise journal state persistence.
fn run_commit_once_segmented() -> Vec<RunResult> {
    ensure_guest_built();
    let elf_path = guest_bin_dir().join("commit_once");
    let elf = std::fs::read(&elf_path)
        .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));
    run_segments_with_input(&elf, &[], Some(4), 10_000)
        .expect("the COMMIT fixture splits into provable segments")
}

/// Execute two distinct commits in one segment to expose their clock linkage.
fn run_commit_twice() -> RunResult {
    ensure_guest_built();
    let elf_path = guest_bin_dir().join("commit_twice");
    let elf = std::fs::read(&elf_path)
        .unwrap_or_else(|error| panic!("failed to read {elf_path:?}: {error}"));
    run(&elf, 10_000).expect("the two-COMMIT fixture executes")
}

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

#[test]
fn guest_sdk_commit_records_the_authenticated_register_reads() {
    let result = run_commit_once();

    assert_eq!(
        (
            result.tracer.commit.len(),
            result.tracer.commit.selector_addr[0],
            result.tracer.commit.selector_next[0],
            result.tracer.commit.argument_addr[0],
            result.tracer.commit.argument_next[0],
        ),
        (1, 17, 1, 10, 0x1234_5678),
    );
}

#[test]
fn commit_ecall_updates_the_public_journal_digest() {
    let result = run_commit_once();
    let mut expected = [0_u32; T];
    expected[DIGEST_WORDS..DIGEST_WORDS + 4]
        .copy_from_slice(&0x1234_5678_u32.to_le_bytes().map(u32::from));
    expected[DIGEST_WORDS + 4] = COMMIT_HASH_DOMAIN;
    poseidon2_permutation(&mut expected);

    assert_eq!(
        (
            result.initial_public_io_state,
            result.final_public_io_state,
            result.journal_count,
        ),
        (
            [0; DIGEST_WORDS],
            expected[..DIGEST_WORDS]
                .try_into()
                .expect("journal digest width is fixed"),
            1,
        ),
    );
}

#[test]
fn segmented_commit_execution_has_adjacent_journal_boundaries() {
    let segments = run_commit_once_segmented();
    assert!(
        segments
            .windows(2)
            .all(|pair| pair[0].final_public_io_state == pair[1].initial_public_io_state)
    );
}

#[test]
fn segmented_commit_execution_records_one_journal_transition() {
    let segments = run_commit_once_segmented();
    assert_eq!(
        segments
            .iter()
            .map(|segment| segment.journal_count)
            .sum::<u32>(),
        1
    );
}

#[test]
fn two_commits_link_their_ordinals_to_increasing_execution_clocks() {
    let result = run_commit_twice();
    assert_eq!(
        (
            result.tracer.commit.journal_step.as_slice(),
            result.tracer.commit.journal_prev_clock.as_slice(),
            result.journal_last_clock,
        ),
        (
            [0, 1].as_slice(),
            [0, result.tracer.commit.clock[0]].as_slice(),
            result.tracer.commit.clock[1],
        )
    );
}

#[test]
fn two_commits_produce_the_execution_ordered_digest() {
    let result = run_commit_twice();
    let mut expected = [0_u32; T];
    expected[DIGEST_WORDS..DIGEST_WORDS + 4]
        .copy_from_slice(&0x1122_3344_u32.to_le_bytes().map(u32::from));
    expected[DIGEST_WORDS + 4] = COMMIT_HASH_DOMAIN;
    poseidon2_permutation(&mut expected);
    expected[DIGEST_WORDS..].fill(0);
    expected[DIGEST_WORDS..DIGEST_WORDS + 4]
        .copy_from_slice(&0x5566_7788_u32.to_le_bytes().map(u32::from));
    expected[DIGEST_WORDS + 4] = COMMIT_HASH_DOMAIN;
    poseidon2_permutation(&mut expected);
    let expected_digest: [u32; DIGEST_WORDS] = expected[..DIGEST_WORDS]
        .try_into()
        .expect("journal digest width is fixed");

    assert_eq!(result.final_public_io_state, expected_digest);
}
