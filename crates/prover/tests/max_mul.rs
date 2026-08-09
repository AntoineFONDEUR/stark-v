//! Arithmetic boundary regressions for maximal multiplication and division.

use prover::{PcsConfig, preprocess, prove_rv32im, verify_rv32im};

#[test]
fn test_full_proof_max_mul_operands() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("max_mul")).expect("max_mul elf");
    let run = runner::run(&elf, 1_000_000).expect("run");
    let preprocessing = preprocess(PcsConfig::default());
    let proof = prove_rv32im(run, PcsConfig::default(), &preprocessing);
    verify_rv32im(proof, PcsConfig::default(), &preprocessing).expect("verify");
}

#[test]
fn test_full_proof_div_edge_cases() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("max_div")).expect("max_div elf");
    let run = runner::run(&elf, 1_000_000).expect("run");
    let preprocessing = preprocess(PcsConfig::default());
    let proof = prove_rv32im(run, PcsConfig::default(), &preprocessing);
    verify_rv32im(proof, PcsConfig::default(), &preprocessing).expect("verify");
}

#[test]
fn test_div_edge_cases_satisfy_aggregate_constraints() {
    prover::e2e::ensure_guest_built();
    let elf = std::fs::read(prover::e2e::guest_bin_dir().join("max_div")).expect("max_div elf");
    let run = runner::run(&elf, 1_000_000).expect("run");
    let traces = prover::components::gen_trace(run.tracer);

    prover::components::Components::assert_constraints_on_polys(
        &traces,
        &prover::relations::Relations::dummy(),
    );
}
