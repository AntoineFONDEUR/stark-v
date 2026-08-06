//! End-to-end proof generation and host verification for a segmented guest run.

use std::sync::OnceLock;

use air::poseidon2::poseidon2_traced_state;
use air::trace::Poseidon2Table;
use continuation::{ContinuationError, prove_segments, verify_segments};
use prover::VerificationError;
use prover::e2e::{ensure_guest_built, guest_bin_dir};
use prover::{Preprocessing, SegmentProof};
use runner::run_segments_with_input;
use stwo::core::pcs::PcsConfig;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sMerkleHasher;

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

#[test_log::test]
fn continuation_rejects_a_missing_poseidon2_tuple_set() {
    assert!(matches!(
        invalid_pairing_fixture().verify_missing(),
        Err(ContinuationError::Proof(
            VerificationError::SharedRelationMismatch
        ))
    ));
}

#[test_log::test]
fn continuation_rejects_an_extra_poseidon2_tuple() {
    assert!(matches!(
        invalid_pairing_fixture().verify_extra(),
        Err(ContinuationError::Proof(
            VerificationError::SharedRelationMismatch
        ))
    ));
}

#[test_log::test]
fn continuation_proving_rejects_re_paired_poseidon2_outputs() {
    assert!(std::panic::catch_unwind(prove_re_paired_outputs).is_err());
}

struct InvalidPairingFixture {
    config: PcsConfig,
    preprocessing: Preprocessing,
    missing: SegmentProof<Blake2sMerkleHasher>,
    extra: SegmentProof<Blake2sMerkleHasher>,
}

impl InvalidPairingFixture {
    fn verify_missing(&self) -> Result<(), ContinuationError> {
        verify_segments(vec![self.missing.clone()], self.config, &self.preprocessing)
    }

    fn verify_extra(&self) -> Result<(), ContinuationError> {
        verify_segments(vec![self.extra.clone()], self.config, &self.preprocessing)
    }
}

fn invalid_pairing_fixture() -> &'static InvalidPairingFixture {
    static FIXTURE: OnceLock<InvalidPairingFixture> = OnceLock::new();
    FIXTURE.get_or_init(build_invalid_pairing_fixture)
}

fn build_invalid_pairing_fixture() -> InvalidPairingFixture {
    ensure_guest_built();
    let elf_bytes = std::fs::read(guest_bin_dir().join("constant"))
        .expect("the constant guest binary is readable");
    let mut missing =
        runner::run(&elf_bytes, 10_000_000).expect("the constant guest runs for missing tuples");
    missing.tracer.poseidon2 = Poseidon2Table::new();
    let mut extra =
        runner::run(&elf_bytes, 10_000_000).expect("the constant guest runs for an extra tuple");
    poseidon2_traced_state(&mut extra.tracer.poseidon2, [123; 16], false, true);
    let config = PcsConfig::default();
    let preprocessing = prover::preprocess(config);
    let [missing, extra] = prove_segments(vec![missing, extra], config, &preprocessing)
        .try_into()
        .expect("the two attack traces produce two constituent proof pairs");
    InvalidPairingFixture {
        config,
        preprocessing,
        missing,
        extra,
    }
}

fn prove_re_paired_outputs() {
    ensure_guest_built();
    let elf_bytes = std::fs::read(guest_bin_dir().join("constant"))
        .expect("the constant guest binary is readable");
    let mut segment =
        runner::run(&elf_bytes, 10_000_000).expect("the constant guest runs for re-paired outputs");
    swap_first_two_poseidon2_outputs(&mut segment.tracer.poseidon2);
    let config = PcsConfig::default();
    let preprocessing = prover::preprocess(config);
    let _ = prove_segments(vec![segment], config, &preprocessing);
}

fn swap_first_two_poseidon2_outputs(table: &mut Poseidon2Table) {
    // Pairing attacks change outputs without moving their input rows.
    table.poseidon2_t410.swap(0, 1);
    table.poseidon2_t411.swap(0, 1);
    table.poseidon2_t412.swap(0, 1);
    table.poseidon2_t413.swap(0, 1);
    table.poseidon2_t414.swap(0, 1);
    table.poseidon2_t415.swap(0, 1);
    table.poseidon2_t416.swap(0, 1);
    table.poseidon2_t417.swap(0, 1);
    table.poseidon2_t418.swap(0, 1);
    table.poseidon2_t419.swap(0, 1);
    table.poseidon2_t420.swap(0, 1);
    table.poseidon2_t421.swap(0, 1);
    table.poseidon2_t422.swap(0, 1);
    table.poseidon2_t423.swap(0, 1);
    table.poseidon2_t424.swap(0, 1);
    table.poseidon2_t425.swap(0, 1);
}
