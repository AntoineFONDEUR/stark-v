//! Integration tests for component aggregation.

use air::trace::Tracer;
use num_traits::Zero;
use prover::components::{ClaimedSum, Traces, gen_interaction_trace, gen_trace};
use prover::relations::Relations;
use stwo::core::pcs::PcsConfig;
use stwo::prover::backend::Column;
use tracing::info;

#[test]
fn test_all_components_aggregate() {
    // Create an empty tracer
    let tracer = Tracer::default();

    let traces: Traces = gen_trace(tracer);

    // Generate interaction traces with default relations
    let relations = Relations::dummy();
    let (interaction_columns, claimed_sum): (_, ClaimedSum) =
        gen_interaction_trace(&traces, &relations);

    assert!(!interaction_columns.is_empty());
    assert!(claimed_sum.sum().is_zero());
}

#[test]
fn test_traces_struct_has_all_opcodes() {
    // Create an empty tracer
    let tracer = Tracer::default();

    let traces: Traces = gen_trace(tracer);

    // Verify we can access each opcode family trace (16 families total).
    assert!(!traces.base_alu_reg.is_empty());
    assert!(!traces.base_alu_imm.is_empty());
    assert!(!traces.shifts_reg.is_empty());
    assert!(!traces.shifts_imm.is_empty());
    assert!(!traces.lt_reg.is_empty());
    assert!(!traces.lt_imm.is_empty());
    assert!(!traces.branch_eq.is_empty());
    assert!(!traces.branch_lt.is_empty());
    assert!(!traces.lui.is_empty());
    assert!(!traces.auipc.is_empty());
    assert!(!traces.jalr.is_empty());
    assert!(!traces.jal.is_empty());
    assert!(!traces.load_store.is_empty());
    assert!(!traces.mul.is_empty());
    assert!(!traces.mulh.is_empty());
    assert!(!traces.div.is_empty());
}

/// Test proving a small example (scaffolding - no real constraints yet).
#[test_log::test]
fn test_prove_fibonacci() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::prove_rv32im;
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("fib");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run fib");

    // Generate proof
    let _proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
}

/// Ensure proving works for the standalone MUL opcode guest.
#[test_log::test]
fn test_prove_opcode_mul() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::prove_rv32im;
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mul_output");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mul_output");

    let _proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
}

/// Ensure proving works for the standalone MULH opcode guest.
#[test_log::test]
fn test_prove_opcode_mulh() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::prove_rv32im;
    use runner::run_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_output_many");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_output_many ELF");
    let input = 0x1234_5678u32.to_le_bytes();

    let run_result =
        run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run mulhu_output_many");

    let _proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
}

/// Full end-to-end proof + verification for a single MULHU with rd = rs2.
#[test_log::test]
fn test_prove_verify_mulhu_alias() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// The supplied preprocessing commitment is part of the verifier-owned statement.
#[test_log::test]
fn test_verify_rejects_mismatched_preprocessing_commitment() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_bytes =
        std::fs::read(guest_bin_dir().join("mulhu_alias")).expect("Failed to read mulhu_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");
    let config = PcsConfig::default();
    let preprocessing = prover::preprocess(config);
    let proof = prove_rv32im(run_result, config, &preprocessing);

    let mut supplied_preprocessing = preprocessing.clone();
    let mut mismatched_root = proof.vm.stark_proof.commitments[0];
    mismatched_root.0[0] ^= 1;
    supplied_preprocessing.merkle_layers[0][0] = mismatched_root;

    let result = verify_rv32im(proof, config, &supplied_preprocessing);

    assert!(matches!(
        result,
        Err(prover::VerificationError::PreprocessingCommitmentMismatch)
    ));
}

/// Every program-root limb is part of the public statement.
#[test_log::test]
fn test_verify_rejects_tampered_program_root_tail() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_bytes =
        std::fs::read(guest_bin_dir().join("mulhu_alias")).expect("Failed to read mulhu_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");
    let config = PcsConfig::default();
    let preprocessing = prover::preprocess(config);
    let mut proof = prove_rv32im(run_result, config, &preprocessing);
    proof
        .vm
        .public_data
        .program_root
        .as_mut()
        .expect("program root is present")[7] ^= 1;

    let result = verify_rv32im(proof, config, &preprocessing);

    assert!(result.is_err());
}

/// Full end-to-end proof + verification for a single MULHU with rd != rs2.
#[test_log::test]
fn test_prove_verify_mulhu_no_alias() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_no_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_no_alias ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_no_alias");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Full end-to-end proof + verification for a single MUL.
#[test_log::test]
fn test_prove_verify_mul_output() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mul_output");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mul_output");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Constraint-only check for single MUL output repro using drawn relations.
#[test_log::test]
fn test_mul_output_constraints_drawn_relations() {
    use prover::components::{self, Claim, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::public_data::PublicData;
    use prover::relations::{INTERACTION_POW_BITS, Relations};
    use runner::run;
    use stwo::core::channel::{Blake2sChannel, Channel};
    use stwo::core::proof_of_work::GrindOps;
    use stwo::prover::backend::simd::SimdBackend;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mul_output");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mul_output");

    let public_data = PublicData::new(&run_result);
    let traces = components::gen_trace(run_result.tracer);
    let claim: Claim = (&traces).into();

    let channel = &mut Blake2sChannel::default();
    public_data.mix_into(channel);
    claim.mix_into(channel);
    let interaction_pow = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow);
    let relations = Relations::draw(channel);

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Constraint-only check for single MULHU output repro using drawn relations.
#[test_log::test]
fn test_mulhu_no_alias_constraints_drawn_relations() {
    use prover::components::{self, Claim, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::public_data::PublicData;
    use prover::relations::{INTERACTION_POW_BITS, Relations};
    use runner::run;
    use stwo::core::channel::{Blake2sChannel, Channel};
    use stwo::core::proof_of_work::GrindOps;
    use stwo::prover::backend::simd::SimdBackend;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_no_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_no_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_no_alias");

    let public_data = PublicData::new(&run_result);
    let traces = components::gen_trace(run_result.tracer);
    let claim: Claim = (&traces).into();

    let channel = &mut Blake2sChannel::default();
    public_data.mix_into(channel);
    claim.mix_into(channel);
    let interaction_pow = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow);
    let relations = Relations::draw(channel);

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Full end-to-end proof + verification for many MUL instructions.
#[test_log::test]
fn test_prove_verify_mul_output_many() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mul_output_many");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output_many ELF");

    let input = 0x1234_5678u32.to_le_bytes();
    let run_result =
        run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run mul_output_many");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

#[test_log::test]
fn test_mul_interaction_trace_prev_cur_deltas() {
    use prover::components;
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::{run, run_with_input};

    ensure_guest_built();

    let elf_single_path = guest_bin_dir().join("mul_output");
    let elf_single = std::fs::read(&elf_single_path).expect("Failed to read mul_output ELF");
    let single_run = run(&elf_single, 10_000_000).expect("Failed to run mul_output");
    let single_traces = components::gen_trace(single_run.tracer);
    let single_rel = Relations::dummy();
    let (single_interaction, _) =
        prover::components::mul::witness::gen_interaction_trace(&single_traces.mul, &single_rel);

    let elf_many_path = guest_bin_dir().join("mul_output_many");
    let elf_many = std::fs::read(&elf_many_path).expect("Failed to read mul_output_many ELF");
    let input = 0x1234_5678u32.to_le_bytes();
    let many_run =
        run_with_input(&elf_many, &input, 10_000_000).expect("Failed to run mul_output_many");
    let many_traces = components::gen_trace(many_run.tracer);
    let many_rel = Relations::dummy();
    let (many_interaction, _) =
        prover::components::mul::witness::gen_interaction_trace(&many_traces.mul, &many_rel);

    for (name, cols) in [("single", &single_interaction), ("many", &many_interaction)] {
        eprintln!(
            "{name}: interaction cols={}, log_size={}",
            cols.len(),
            cols[0].domain.log_size()
        );
        for (col_idx, column) in cols.iter().enumerate() {
            let values = column.values.to_cpu();
            let mut diff_count = 0usize;
            for row in 0..values.len() {
                let prev = values[(row + values.len() - 1) % values.len()];
                if prev != values[row] {
                    diff_count += 1;
                }
            }
            eprintln!("  {name}: col={col_idx} prev!=cur rows={diff_count}");
        }

        let max_log = 20u32;
        let point =
            stwo::core::circle::CirclePoint::<stwo::core::fields::qm31::SecureField>::get_point(
                1337,
            );
        let step = stwo::core::poly::circle::CanonicCoset::new(max_log).step();
        let shifted = point + step.mul_signed(-1).into_ef();
        for (col_idx, column) in cols.iter().enumerate().take(32).skip(28) {
            let poly = column.clone().interpolate();
            let fold = max_log - column.domain.log_size();
            let v_cur = poly.eval_at_point(point.repeated_double(fold));
            let v_prev = poly.eval_at_point(shifted.repeated_double(fold));
            eprintln!(
                "  {name}: col={col_idx} sampled_prev_eq_cur={}",
                v_prev == v_cur
            );
        }
    }
}

#[test]
fn test_offset_index_matches_translation_large_lift_in_prover_context() {
    let domain_log_size = 6;
    let eval_log_size = 20;
    let offset = -1isize;

    let eval_domain = stwo::core::poly::circle::CanonicCoset::new(eval_log_size).circle_domain();
    let trace_step = stwo::core::poly::circle::CanonicCoset::new(domain_log_size).step();
    let sample_count = 4096usize;
    let stride = (1usize << eval_log_size) / sample_count;
    for k in 0..sample_count {
        let i = k * stride;
        let shifted_index = stwo::core::utils::offset_bit_reversed_circle_domain_index(
            i,
            domain_log_size,
            eval_log_size,
            offset,
        );
        let point_from_index = eval_domain.at(stwo::core::utils::bit_reverse_index(
            shifted_index,
            eval_log_size,
        ));
        let point_from_translation = eval_domain
            .at(stwo::core::utils::bit_reverse_index(i, eval_log_size))
            + trace_step.mul_signed(offset).into_ef();
        assert_eq!(point_from_index, point_from_translation);
    }
}

#[test_log::test]
fn test_mul_offset_sampling_matches_domain_extension() {
    use prover::components;
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::run;
    use stwo::core::poly::circle::CanonicCoset;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mul_output");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mul_output ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mul_output");
    let traces = components::gen_trace(run_result.tracer);
    let relations = Relations::dummy();
    let (interaction_trace, _) =
        prover::components::mul::witness::gen_interaction_trace(&traces.mul, &relations);

    let eval = prover::components::mul::air::Eval {
        log_size: traces.mul[0].domain.log_size(),
        relations,
    };
    let info = stwo_constraint_framework::FrameworkEval::evaluate(
        &eval,
        stwo_constraint_framework::InfoEvaluator::new(
            eval.log_size,
            vec![],
            stwo::core::fields::qm31::SecureField::zero(),
        ),
    );
    let interaction_offsets = &info.mask_offsets[2];

    let interaction_log_size = eval.log_size + 1;
    let eval_domain_7 = CanonicCoset::new(interaction_log_size).circle_domain();
    let eval_domain_20 = CanonicCoset::new(20).circle_domain();
    let step_20 = CanonicCoset::new(20).step();
    let fold_to_interaction = 20 - interaction_log_size;
    let rows_7_points: Vec<_> = (0..(1usize << (eval.log_size + 1)))
        .map(|row| {
            let p = eval_domain_7.at(stwo::core::utils::bit_reverse_index(row, eval.log_size + 1));
            (row, p)
        })
        .collect();

    let mut matched_columns = 0usize;
    for (col_idx, offsets) in interaction_offsets.iter().enumerate() {
        if offsets.as_slice() != [-1, 0] {
            continue;
        }
        matched_columns += 1;
        let poly = interaction_trace[col_idx].clone().interpolate();

        let mut checked = 0usize;
        for i in (0usize..(1usize << 20)).step_by(4096).take(128) {
            let point_20 = eval_domain_20.at(stwo::core::utils::bit_reverse_index(i, 20));
            let point_7 = point_20.repeated_double(fold_to_interaction);
            let _row_7 = rows_7_points
                .iter()
                .find_map(|(row, p)| if *p == point_7 { Some(*row) } else { None })
                .expect("point_7 must be on eval_domain_7");

            let _sampled_prev = poly.eval_at_point(
                (point_20.into_ef() + step_20.mul_signed(-1).into_ef())
                    .repeated_double(fold_to_interaction),
            );
            checked += 1;
        }
        assert!(checked > 0);
        eprintln!("checked col {col_idx} for {checked} lifted points");
    }
    assert!(
        matched_columns > 0,
        "expected at least one [-1, 0] mask-offset column"
    );
}

#[test]
fn test_repeated_double_shift_relation_for_mul_offsets() {
    let max_log = 20u32;
    let trace_log = 6u32;
    let fold = max_log - trace_log;
    let domain_max = stwo::core::poly::circle::CanonicCoset::new(max_log).circle_domain();
    let step_max = stwo::core::poly::circle::CanonicCoset::new(max_log).step();
    let step_trace = stwo::core::poly::circle::CanonicCoset::new(trace_log).step();

    for i in (0usize..(1usize << max_log)).step_by(4096).take(512) {
        let point: stwo::core::circle::CirclePoint<stwo::core::fields::qm31::SecureField> =
            domain_max
                .at(stwo::core::utils::bit_reverse_index(i, max_log))
                .into_ef();
        let lhs = (point + step_max.mul_signed(-1).into_ef()).repeated_double(fold);
        let rhs = point.repeated_double(fold) + step_trace.mul_signed(-1).into_ef();
        assert_eq!(lhs, rhs);
    }
}

/// Full end-to-end proof + verification for many MULHU instructions.
#[test_log::test]
fn test_prove_verify_mulhu_output_many() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_output_many");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_output_many ELF");

    let input = 0x1234_5678u32.to_le_bytes();
    let run_result =
        run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run mulhu_output_many");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Full end-to-end proof + verification for Fibonacci.
#[test_log::test]
fn test_prove_verify_fibonacci() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("fib");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run fib");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Full end-to-end proof + verification for SHA256 (without input).
#[test_log::test]
fn test_prove_verify_sha2() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("sha2");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read sha2 ELF");

    let run_result = run(&elf_bytes, 100_000_000).expect("Failed to run sha2");

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// End-to-end benchmark for Fibonacci with input.
#[test_log::test]
fn test_e2e_fibonacci_benchmark() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run_with_input;
    use serde::Deserialize;
    use std::time::Instant;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct FibResult {
        n: u32,
        value: u32,
    }

    fn fib_value(n: u32) -> u32 {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return 1;
        }
        let mut a = 0u32;
        let mut b = 1u32;
        let mut i = 2u32;
        while i <= n {
            let tmp = a.wrapping_add(b);
            a = b;
            b = tmp;
            i += 1;
        }
        b
    }

    ensure_guest_built();

    let n: u32 = std::env::var("STARKV_FIB_N")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(1_000);
    let input = n.to_le_bytes();

    let elf_path = guest_bin_dir().join("fib_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib_input ELF");

    let run_start = Instant::now();
    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run fib_input");
    let run_elapsed = run_start.elapsed();

    let output_bytes = run_result
        .output
        .as_ref()
        .expect("No output from fib_input");
    let output: FibResult =
        postcard::from_bytes(output_bytes).expect("Failed to decode fib output");
    assert_eq!(output.n, n);
    assert_eq!(output.value, fib_value(n));

    let cycles = run_result.cycles;
    assert!(cycles > 0, "No cycles reported");

    let prove_start = Instant::now();
    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    let prove_elapsed = prove_start.elapsed();

    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");

    let run_prove_elapsed = run_elapsed + prove_elapsed;
    let cycles_f = cycles as f64;
    let run_secs = run_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let run_hz = (cycles_f / run_secs).ceil() as u64;
    let run_khz = run_hz as f64 / 1_000.0;
    let run_prove_secs = run_prove_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let prove_secs = prove_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let run_prove_hz = (cycles_f / run_prove_secs).ceil() as u64;
    let prove_hz = (cycles_f / prove_secs).ceil() as u64;
    let run_prove_khz = run_prove_hz as f64 / 1_000.0;
    let prove_khz = prove_hz as f64 / 1_000.0;

    info!("fib_input benchmark");
    info!("  n: {n}");
    info!("  cycles: {cycles}");
    info!("  run:     {run_khz:>10.3} kHz  ({run_secs:.3}s)",);
    info!("  run+prove: {run_prove_khz:>10.3} kHz  ({run_prove_secs:.3}s)",);
    info!("  prove:     {prove_khz:>10.3} kHz  ({prove_secs:.3}s)",);
}

/// Test constraint satisfaction using assert_constraints_on_polys for each component.
/// This helps identify which specific component's constraints are failing.
#[test_log::test]
fn test_fibonacci_constraints() {
    use prover::components::{self, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("fib");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib ELF");

    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run fib");

    let traces = components::gen_trace(run_result.tracer);
    let relations = Relations::dummy();

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Test constraint satisfaction for Fibonacci with explicit input.
#[test_log::test]
fn test_fibonacci_input_constraints() {
    use prover::components::{self, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::run_with_input;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("fib_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read fib_input ELF");

    let input = 20u32.to_le_bytes();
    let run_result =
        run_with_input(&elf_bytes, &input, 10_000_000).expect("Failed to run fib_input");

    let traces = components::gen_trace(run_result.tracer);
    let relations = Relations::dummy();

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Test constraint satisfaction for SHA256 with explicit input.
#[test_log::test]
fn test_sha2_constraints() {
    use prover::components::{self, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::run_with_input;

    ensure_guest_built();

    // Create a small test message
    let message: Vec<u8> = (0..44).map(|i| (i % 256) as u8).collect();
    let len = message.len() as u32;
    let mut input = len.to_le_bytes().to_vec();
    input.extend_from_slice(&message);

    let elf_path = guest_bin_dir().join("sha2_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read sha2_input ELF");

    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run sha2_input");

    let traces = components::gen_trace(run_result.tracer);
    let relations = Relations::dummy();

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// End-to-end benchmark for SHA256 with variable-length input.
#[test_log::test]
fn test_e2e_sha2_benchmark() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run_with_input;
    use serde::Deserialize;
    use std::time::Instant;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct Sha2Result {
        input_len: u32,
        hash: [u8; 32],
    }

    ensure_guest_built();

    // Message size can be configured via environment variable
    let msg_len: usize = std::env::var("STARKV_SHA2_LEN")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(44);

    // Create message of specified length
    let message: Vec<u8> = (0..msg_len).map(|i| (i % 256) as u8).collect();

    // Input format: 4-byte length prefix + message bytes
    let len = message.len() as u32;
    let mut input = len.to_le_bytes().to_vec();
    input.extend_from_slice(&message);

    let elf_path = guest_bin_dir().join("sha2_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read sha2_input ELF");

    let run_start = Instant::now();
    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run sha2_input");
    let run_elapsed = run_start.elapsed();

    // Verify output
    let output_bytes = run_result
        .output
        .as_ref()
        .expect("No output from sha2_input");
    let output: Sha2Result =
        postcard::from_bytes(output_bytes).expect("Failed to decode sha2 output");
    assert_eq!(output.input_len, msg_len as u32);

    // Verify the hash matches expected value computed with sha2 crate
    use sha2::{Digest, Sha256};
    let expected_hash: [u8; 32] = Sha256::digest(&message).into();
    assert_eq!(output.hash, expected_hash, "SHA256 hash mismatch");

    let cycles = run_result.cycles;
    assert!(cycles > 0, "No cycles reported");

    let prove_start = Instant::now();
    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    let prove_elapsed = prove_start.elapsed();

    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");

    let run_prove_elapsed = run_elapsed + prove_elapsed;
    let cycles_f = cycles as f64;
    let run_secs = run_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let run_hz = (cycles_f / run_secs).ceil() as u64;
    let run_khz = run_hz as f64 / 1_000.0;
    let run_prove_secs = run_prove_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let prove_secs = prove_elapsed.as_secs_f64().max(f64::MIN_POSITIVE);
    let run_prove_hz = (cycles_f / run_prove_secs).ceil() as u64;
    let prove_hz = (cycles_f / prove_secs).ceil() as u64;
    let run_prove_khz = run_prove_hz as f64 / 1_000.0;
    let prove_khz = prove_hz as f64 / 1_000.0;

    info!("sha2_input benchmark");
    info!("  message_len: {msg_len}");
    info!("  cycles: {cycles}");
    info!("  run:       {run_khz:>10.3} kHz  ({run_secs:.3}s)");
    info!("  prove:     {prove_khz:>10.3} kHz  ({prove_secs:.3}s)");
    info!("  run+prove: {run_prove_khz:>10.3} kHz  ({run_prove_secs:.3}s)");
}

/// Full end-to-end proof + verification for Keccak-256.
#[test_log::test]
fn test_prove_verify_keccak() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run;
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct KeccakResult {
        input_len: u32,
        hash: [u8; 32],
    }

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("keccak");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read keccak ELF");

    let run_result = run(&elf_bytes, 100_000_000).expect("Failed to run keccak");

    let output_bytes = run_result.output.as_ref().expect("No output from keccak");
    let output: KeccakResult =
        postcard::from_bytes(output_bytes).expect("Failed to decode keccak output");
    assert_eq!(output.input_len, 11);
    assert_eq!(
        output.hash,
        [
            0x47, 0x17, 0x32, 0x85, 0xa8, 0xd7, 0x34, 0x1e, 0x5e, 0x97, 0x2f, 0xc6, 0x77, 0x28,
            0x63, 0x84, 0xf8, 0x02, 0xf8, 0xef, 0x42, 0xa5, 0xec, 0x5f, 0x03, 0xbb, 0xfa, 0x25,
            0x4c, 0xb0, 0x1f, 0xad,
        ],
    );

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Validates proving succeeds at the first sponge-rate boundary.
#[test_log::test]
fn test_prove_verify_keccak_input_len_136() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::{prove_rv32im, verify_rv32im};
    use runner::run_with_input;
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct KeccakResult {
        input_len: u32,
        hash: [u8; 32],
    }

    ensure_guest_built();

    let msg_len: usize = std::env::var("STARKV_KECCAK_LEN")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(136);
    let message: Vec<u8> = (0..msg_len).map(|i| (i % 256) as u8).collect();
    let mut input = (msg_len as u32).to_le_bytes().to_vec();
    input.extend_from_slice(&message);

    let elf_path = guest_bin_dir().join("keccak_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read keccak_input ELF");
    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run keccak_input");

    let output_bytes = run_result
        .output
        .as_ref()
        .expect("No output from keccak_input");
    let output: KeccakResult =
        postcard::from_bytes(output_bytes).expect("Failed to decode keccak output");
    assert_eq!(output.input_len, msg_len as u32);

    let proof = prove_rv32im(
        run_result,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    );
    verify_rv32im(
        proof,
        PcsConfig::default(),
        &prover::preprocess(PcsConfig::default()),
    )
    .expect("Verification failed");
}

/// Constraint-only reproducer for Keccak input crossing the sponge-rate boundary.
#[test_log::test]
fn test_keccak_input_constraints_len_136() {
    use prover::components::{self, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::relations::Relations;
    use runner::run_with_input;
    use serde::Deserialize;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct KeccakResult {
        input_len: u32,
        hash: [u8; 32],
    }

    ensure_guest_built();

    let msg_len: usize = std::env::var("STARKV_KECCAK_LEN")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(136);
    let message: Vec<u8> = (0..msg_len).map(|i| (i % 256) as u8).collect();
    let mut input = (msg_len as u32).to_le_bytes().to_vec();
    input.extend_from_slice(&message);

    let elf_path = guest_bin_dir().join("keccak_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read keccak_input ELF");
    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run keccak_input");

    let output_bytes = run_result
        .output
        .as_ref()
        .expect("No output from keccak_input");
    let output: KeccakResult =
        postcard::from_bytes(output_bytes).expect("Failed to decode keccak output");
    assert_eq!(output.input_len, msg_len as u32);

    let traces = components::gen_trace(run_result.tracer);
    let relations = Relations::dummy();

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Constraint-only reproducer using drawn relations (same challenge flow as proving).
#[test_log::test]
fn test_keccak_input_constraints_len_136_drawn_relations() {
    use prover::components::{self, Claim, Components};
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::public_data::PublicData;
    use prover::relations::{INTERACTION_POW_BITS, Relations};
    use runner::run_with_input;
    use serde::Deserialize;
    use stwo::core::channel::{Blake2sChannel, Channel};
    use stwo::core::proof_of_work::GrindOps;
    use stwo::prover::backend::simd::SimdBackend;

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct KeccakResult {
        input_len: u32,
        hash: [u8; 32],
    }

    ensure_guest_built();

    let msg_len: usize = std::env::var("STARKV_KECCAK_LEN")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(136);
    let message: Vec<u8> = (0..msg_len).map(|i| (i % 256) as u8).collect();
    let mut input = (msg_len as u32).to_le_bytes().to_vec();
    input.extend_from_slice(&message);

    let elf_path = guest_bin_dir().join("keccak_input");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read keccak_input ELF");
    let run_result =
        run_with_input(&elf_bytes, &input, 100_000_000).expect("Failed to run keccak_input");

    let output_bytes = run_result
        .output
        .as_ref()
        .expect("No output from keccak_input");
    let output: KeccakResult =
        postcard::from_bytes(output_bytes).expect("Failed to decode keccak output");
    assert_eq!(output.input_len, msg_len as u32);

    let public_data = PublicData::new(&run_result);
    let traces = components::gen_trace(run_result.tracer);
    let claim: Claim = (&traces).into();

    let channel = &mut Blake2sChannel::default();
    public_data.mix_into(channel);
    claim.mix_into(channel);
    let interaction_pow = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow);
    let relations = Relations::draw(channel);

    Components::assert_constraints_on_polys(&traces, &relations);
}

/// Output anchoring consumes each output word's access within the final
/// segment's trace, so the runner must place the whole output tail there no
/// matter where the cycle budget would have cut: the first output-region
/// store forces a boundary just before it. One test per split factor.
macro_rules! output_tail_test {
    ($name:ident, $divisor:expr) => {
        #[test_log::test]
        fn $name() {
            use prover::e2e::{ensure_guest_built, guest_bin_dir};
            ensure_guest_built();
            let elf_bytes = std::fs::read(guest_bin_dir().join("fib")).expect("read fib ELF");
            let cycles = runner::run(&elf_bytes, 10_000_000).expect("run fib").cycles;
            let segment_cycles = u32::try_from(cycles / $divisor + 1).expect("fits u32");
            let segments =
                runner::run_segments_with_input(&elf_bytes, &[], Some(segment_cycles), 10_000_000)
                    .expect("segmented run failed");
            let last = segments.last().expect("at least one segment");
            assert!(
                last.output_words
                    .iter()
                    .all(|w| last.tracer.mem_clock.contains_key(&w.addr)),
                "an output word was written outside the final segment"
            );
        }
    };
}

output_tail_test!(test_output_tail_lands_in_final_segment_split_5, 5);
output_tail_test!(test_output_tail_lands_in_final_segment_split_7, 7);

/// Full VM proof over the Poseidon2-M31 channel:
/// the entire stark-v pipeline — preprocessing, proving, verification —
/// committed with the hash the recursion verifier AIR proves.
#[test_log::test]
fn test_prove_verify_poseidon2_channel() {
    use prover::e2e::{ensure_guest_built, guest_bin_dir};
    use prover::poseidon2_channel::Poseidon2M31MerkleChannel;
    use prover::{preprocess_with_channel, prove_rv32im_with_channel, verify_rv32im_with_channel};
    use runner::run;

    ensure_guest_built();

    let elf_path = guest_bin_dir().join("mulhu_alias");
    let elf_bytes = std::fs::read(&elf_path).expect("Failed to read mulhu_alias ELF");
    let run_result = run(&elf_bytes, 10_000_000).expect("Failed to run mulhu_alias");

    let preprocessing = preprocess_with_channel::<Poseidon2M31MerkleChannel>(PcsConfig::default());
    let proof = prove_rv32im_with_channel::<Poseidon2M31MerkleChannel>(
        run_result,
        PcsConfig::default(),
        &preprocessing,
    );
    assert!(proof.vm.stark_aux.is_none() && proof.poseidon2.stark_aux.is_none());
    verify_rv32im_with_channel::<Poseidon2M31MerkleChannel>(
        proof,
        PcsConfig::default(),
        &preprocessing,
    )
    .expect("poseidon2-channel verification failed");
}
