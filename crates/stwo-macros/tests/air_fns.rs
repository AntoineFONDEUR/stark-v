//! End-to-end coverage for `define_air_fns!`: standalone AIR generation,
//! witness filling, relation cancellation, and Poseidon2 equivalence.

#![allow(clippy::possible_missing_comma, clippy::too_many_arguments)]

use stwo::core::fields::m31::BaseField;
use stwo::core::pcs::PcsConfig;

mod examples {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        fn cube(x) {
            let x2 = x * x;
            return x2 * x;
        }

        fn quint(x) {
            return x ** 5;
        }

        fn affine(a, b, c) {
            return a + 2 * b + 3 * c + 7;
        }

        fn poly(a, b) {
            let c = cube(a);
            let q = quint(b);
            let s = affine(a, b, c);
            assert (a + b) * (a + b) == a * a + 2 * a * b + b * b;
            return (c + q, s * s);
        }
    }
}

mod poseidon {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        inline fn m4(x0, x1, x2, x3) {
            let t0 = x0 + x1;
            let t1 = x2 + x3;
            let t2 = 2 * x1 + t1;
            let t3 = 2 * x3 + t0;
            let t4 = 4 * t1 + t3;
            let t5 = 4 * t0 + t2;
            let t6 = t3 + t5;
            let t7 = t2 + t4;
            return (t6, t5, t7, t4);
        }

        inline fn external_matrix(state: [felt; 16]) {
            let (b0, b1, b2, b3) = m4(state[0], state[1], state[2], state[3]);
            let (b4, b5, b6, b7) = m4(state[4], state[5], state[6], state[7]);
            let (b8, b9, b10, b11) = m4(state[8], state[9], state[10], state[11]);
            let (b12, b13, b14, b15) = m4(state[12], state[13], state[14], state[15]);
            let mixed = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15];
            let sums = map(j, 0..4, mixed[j] + mixed[j + 4] + mixed[j + 8] + mixed[j + 12]);
            let out = map(k, 0..16, mixed[k] + sums[k % 4]);
            return out;
        }

        fn permute(state: [felt; 16]) {
            let state = external_matrix(state);
            for r in 0..4 {
                let state = map(j, 0..16, (state[j] + constant(runner::poseidon2::EXTERNAL_ROUND_CONSTS[r][j])) ** 5);
                let state = external_matrix(state);
            }
            for r in 0..14 {
                let state = update(state, 0, (state[0] + constant(runner::poseidon2::INTERNAL_ROUND_CONSTS[r])) ** 5);
                let total = sum(j, 0..16, state[j]);
                let state = map(j, 0..16, state[j] * constant(runner::poseidon2::INTERNAL_MATRIX[j]) + total);
            }
            for r in 4..8 {
                let state = map(j, 0..16, (state[j] + constant(runner::poseidon2::EXTERNAL_ROUND_CONSTS[r][j])) ** 5);
                let state = external_matrix(state);
            }
            return state;
        }
    }
}

fn felt(value: u32) -> BaseField {
    BaseField::from_u32_unchecked(value)
}

#[test]
fn test_air_fns_roundtrip() {
    let mut tables = examples::Tables::default();
    let inputs = [felt(3), felt(5)];
    let outputs = examples::call_poly(&mut tables, inputs);

    // cube(3) = 27, quint(5) = 3125, affine(3, 5, 27) = 3 + 10 + 81 + 7 = 101.
    assert_eq!(outputs[0], felt(27 + 3125));
    assert_eq!(outputs[1], felt(101 * 101));
    assert_eq!(tables.poly.len(), 1);
    assert_eq!(tables.cube.len(), 1);
    assert_eq!(tables.quint.len(), 1);
    assert_eq!(tables.affine.len(), 1);

    let activations = vec![examples::Activation::Poly { inputs, outputs }];
    let proof = examples::prove_air_fns(tables, activations, PcsConfig::default());
    examples::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_air_fns_repeated_activations_balance_by_multiplicity() {
    let mut tables = examples::Tables::default();
    let first = examples::call_cube(&mut tables, [felt(2)]);
    let second = examples::call_cube(&mut tables, [felt(2)]);
    assert_eq!(first, second);

    let activations = vec![
        examples::Activation::Cube {
            inputs: [felt(2)],
            outputs: first,
        },
        examples::Activation::Cube {
            inputs: [felt(2)],
            outputs: second,
        },
    ];
    let proof = examples::prove_air_fns(tables, activations, PcsConfig::default());
    examples::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_air_fns_rejects_forged_output() {
    let mut tables = examples::Tables::default();
    let inputs = [felt(3), felt(5)];
    let outputs = examples::call_poly(&mut tables, inputs);

    let mut forged = outputs;
    forged[0] += felt(1);
    let activations = vec![examples::Activation::Poly {
        inputs,
        outputs: forged,
    }];
    let proof = examples::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(examples::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_air_fns_rejects_missing_internal_activation() {
    let mut tables = examples::Tables::default();
    let outputs = examples::call_cube(&mut tables, [felt(3)]);
    let activations = vec![examples::Activation::Poly {
        inputs: [felt(3), felt(5)],
        outputs: [outputs[0], felt(0)],
    }];
    let proof = examples::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(examples::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_degree_budget_materializes_quint_chain() {
    use examples::prover_columns::{CubeColumns, QuintColumns};

    // cube: enabler + x + one materialized square (x2 * x at budget 2
    // forces x2 into a column).
    assert_eq!(CubeColumns::<()>::SIZE, 3);
    // quint: enabler + x + two materialized cells from exponentiation by
    // squaring under the degree budget.
    assert_eq!(QuintColumns::<()>::SIZE, 4);
}

#[test]
fn test_constraint_degrees_within_bound() {
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    let relations = examples::AirFnRelations::dummy();
    for (name, degrees) in [
        (
            "cube",
            examples::cube::air::Eval {
                log_size: 4,
                relations: relations.clone(),
            }
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds(),
        ),
        (
            "quint",
            examples::quint::air::Eval {
                log_size: 4,
                relations: relations.clone(),
            }
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds(),
        ),
        (
            "poly",
            examples::poly::air::Eval {
                log_size: 4,
                relations: relations.clone(),
            }
            .evaluate(ExprEvaluator::new())
            .constraint_degree_bounds(),
        ),
    ] {
        let max = degrees.iter().max().copied().unwrap_or(0);
        assert!(max <= 3, "{name} breaches the degree bound: {degrees:?}");
    }
}

fn run_poseidon_both(state: [u32; 16]) -> ([u32; 16], [u32; 16]) {
    let mut tables = poseidon::Tables::default();
    let outputs = poseidon::call_permute(&mut tables, state.map(BaseField::from_u32_unchecked));
    let mut expected = state;
    runner::poseidon2::poseidon2_permutation(&mut expected);
    (outputs.map(|v| v.0), expected)
}

#[test]
fn test_permute_matches_runner_on_zero_state() {
    let (actual, expected) = run_poseidon_both([0; 16]);
    assert_eq!(actual, expected);
}

#[test]
fn test_permute_matches_runner_on_counting_state() {
    let (actual, expected) = run_poseidon_both(std::array::from_fn(|i| 1 + i as u32));
    assert_eq!(actual, expected);
}

#[test]
fn test_permute_matches_runner_on_random_states() {
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    let mut rng = SmallRng::seed_from_u64(42);
    for _ in 0..16 {
        let state: [u32; 16] = std::array::from_fn(|_| rng.gen_range(0..(1u32 << 31) - 1));
        let (actual, expected) = run_poseidon_both(state);
        assert_eq!(actual, expected);
    }
}

#[test]
fn test_permute_activation_proves_and_verifies() {
    let mut tables = poseidon::Tables::default();
    let inputs: [BaseField; 16] =
        std::array::from_fn(|i| BaseField::from_u32_unchecked(7 * i as u32 + 3));
    let outputs = poseidon::call_permute(&mut tables, inputs);

    let activations = vec![poseidon::Activation::Permute { inputs, outputs }];
    let proof = poseidon::prove_air_fns(tables, activations, PcsConfig::default());
    poseidon::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_permute_rejects_forged_output() {
    let mut tables = poseidon::Tables::default();
    let inputs: [BaseField; 16] =
        std::array::from_fn(|i| BaseField::from_u32_unchecked(11 * i as u32));
    let mut outputs = poseidon::call_permute(&mut tables, inputs);
    outputs[0] += BaseField::from_u32_unchecked(1);

    let activations = vec![poseidon::Activation::Permute { inputs, outputs }];
    let proof = poseidon::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(poseidon::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_compiled_poseidon_layout_matches_hand_flattened_scale() {
    use poseidon::prover_columns::PermuteColumns;

    let size = PermuteColumns::<()>::SIZE;
    // enabler + 16 inputs + 16*(2 + 3*7) cells (full rounds) + 3*14 (partial).
    assert_eq!(size, 1 + 16 + 16 * (2 + 3 * 7) + 3 * 14);
}

// External relations: two functions sharing one declared relation. `source`
// emits `pass(x)`, `sink` consumes it. The relation balances across the two
// tables within one proof, exactly like a host/precompile split would across
// two proofs.
mod shared {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        relation pass(1);

        fn source(x) {
            emit pass(x);
            return x;
        }

        fn sink(x) {
            consume pass(x);
            return x;
        }
    }
}

mod inline_relation_degree {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        logup_batch: 2,

        relation product(1);

        inline fn multiply(lhs, rhs) {
            return lhs * rhs;
        }

        fn host(a, b, c, d) {
            let first = multiply(a, b);
            let second = multiply(c, d);
            consume product(first);
            consume product(second);
            return first + second;
        }
    }
}

#[test]
fn test_inline_relation_arguments_fit_the_degree_bound() {
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    let evaluated = inline_relation_degree::host::air::Eval {
        log_size: 4,
        relations: inline_relation_degree::AirFnRelations::dummy(),
    }
    .evaluate(ExprEvaluator::new());
    let degrees = evaluated.constraint_degree_bounds();

    assert!(degrees.iter().all(|degree| *degree <= 3), "{degrees:?}");
}

mod derived_bitwise_degree {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        logup_batch: 2,

        relation bitwise(4);

        fn host(value, a, b, c, d) {
            let first_mask = a * b;
            let second_mask = c * d;
            let first = bitand(value, first_mask);
            let second = bitand(value, second_mask);
            return first + second;
        }
    }
}

#[test]
fn test_derived_bitwise_inputs_fit_the_degree_bound() {
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    let evaluated = derived_bitwise_degree::host::air::Eval {
        log_size: 4,
        relations: derived_bitwise_degree::AirFnRelations::dummy(),
    }
    .evaluate(ExprEvaluator::new());
    let degrees = evaluated.constraint_degree_bounds();

    assert!(degrees.iter().all(|degree| *degree <= 3), "{degrees:?}");
}

mod embedded_relation_bundle {
    stwo_constraint_framework::relation!(PassRelation, 1);
    stwo_constraint_framework::relation!(RecordRelation, 1);

    /// Relation instances owned by the host system embedding this AIR.
    #[derive(Clone)]
    pub struct Relations {
        pub pass: PassRelation,
        pub record: RecordRelation,
    }

    impl Relations {
        pub fn dummy() -> Self {
            Self {
                pass: PassRelation::dummy(),
                record: RecordRelation::dummy(),
            }
        }
    }

    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::embedded_relation_bundle::Relations,
        logup_batch: 2,

        relation pass(1);
        relation record(1);

        fn guarded(value, active) {
            constrain active * (1 - active);
            constrain active * (1 - enabler);
            emit(active) pass(value);
            consume(active) record(value);
            return value;
        }
    }
}

mod unbatched_tail_bundle {
    stwo_constraint_framework::relation!(PassRelation, 1);
    stwo_constraint_framework::relation!(RecordRelation, 1);

    /// Relation instances owned by the host system embedding this AIR.
    #[derive(Clone)]
    pub struct Relations {
        pub pass: PassRelation,
        pub record: RecordRelation,
    }

    impl Relations {
        pub fn dummy() -> Self {
            Self {
                pass: PassRelation::dummy(),
                record: RecordRelation::dummy(),
            }
        }
    }

    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::unbatched_tail_bundle::Relations,
        logup_batch: 2,
        logup_unbatched_tail: 2,

        relation pass(1);
        relation record(1);

        fn guarded(value, active) {
            emit(active) pass(value);
            consume(active) record(value);
            emit(active) pass(value + 1);
            consume(active) record(value + 1);
            return value;
        }
    }
}

mod preprocessed_schedule {
    stwo_constraint_framework::relation!(PassRelation, 1);

    /// Relation instances used by the generated schedule component.
    #[derive(Clone)]
    pub struct Relations {
        pub pass: PassRelation,
    }

    impl Relations {
        pub fn dummy() -> Self {
            Self {
                pass: PassRelation::dummy(),
            }
        }
    }

    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_relations: crate::preprocessed_schedule::Relations,
        embedded_preprocessed: {
            row_mask: "test_schedule_row_mask",
            value: "test_schedule_value",
        },
        embedded_params: [active],

        relation pass(1);

        fn schedule(row_mask, value, active) {
            emit(row_mask * active) pass(value);
            return value;
        }
    }
}

mod mixed_preprocessed_schedule {
    stwo_constraint_framework::relation!(PassRelation, 1);

    /// Relation instances used by the mixed committed/preprocessed component.
    #[derive(Clone)]
    pub struct Relations {
        pub pass: PassRelation,
    }

    impl Relations {
        pub fn dummy() -> Self {
            Self {
                pass: PassRelation::dummy(),
            }
        }
    }

    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        embedded_component: true,
        embedded_enabler_boolean: false,
        embedded_relations: crate::mixed_preprocessed_schedule::Relations,
        embedded_preprocessed: {
            row_mask: "test_mixed_schedule_row_mask",
            expected: "test_mixed_schedule_expected",
        },
        embedded_params: [active],

        relation pass(1);

        fn mixed_schedule(value, row_mask, expected, active) {
            constrain enabler - row_mask;
            constrain enabler * active * (value - expected);
            emit(enabler * active) pass(value);
            return value;
        }
    }
}

#[test]
fn test_embedded_component_uses_custom_relation_bundle() {
    use embedded_relation_bundle::component::air::Eval;
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    let evaluated = Eval {
        log_size: 4,
        relations: embedded_relation_bundle::Relations::dummy(),
    }
    .evaluate(ExprEvaluator::new());

    assert_eq!(evaluated.logup.fracs.len(), 2);
}

#[test]
fn test_embedded_component_batches_relation_pairs() {
    let mut table = embedded_relation_bundle::GuardedTable::new();
    embedded_relation_bundle::guarded_fill(&mut table, [felt(7), felt(1)], []);
    let trace = table.into_witness();
    let (interaction, _) = embedded_relation_bundle::component::witness::gen_interaction_trace(
        &trace,
        &embedded_relation_bundle::Relations::dummy(),
    );

    // One QM31 interaction column is represented by four base-field columns.
    assert_eq!(interaction.len(), 4);
}

#[test]
fn test_embedded_component_keeps_the_declared_tail_unbatched() {
    let mut table = unbatched_tail_bundle::GuardedTable::new();
    unbatched_tail_bundle::guarded_fill(&mut table, [felt(7), felt(1)], []);
    let trace = table.into_witness();
    let (interaction, _) = unbatched_tail_bundle::component::witness::gen_interaction_trace(
        &trace,
        &unbatched_tail_bundle::Relations::dummy(),
    );

    // One pair and two singletons produce three QM31 interaction columns.
    assert_eq!(interaction.len(), 12);
}

#[test]
fn test_preprocessed_component_shares_air_and_interaction_frame() {
    use simd::AlignedVec;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::poly::BitReversedOrder;
    use stwo::prover::poly::circle::CircleEvaluation;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    let log_size = 4;
    let domain = CanonicCoset::new(log_size).circle_domain();
    let make_column = |value| {
        let mut data = AlignedVec::with_capacity(1 << log_size);
        data.resize(1 << log_size, value);
        CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(
            domain,
            BaseColumn::from(data),
        )
    };
    let preprocessed = vec![make_column(1), make_column(7)];
    let relations = preprocessed_schedule::Relations::dummy();
    let (interaction, claimed_sum) =
        preprocessed_schedule::component::witness::gen_interaction_trace(
            &preprocessed,
            felt(1),
            &relations,
        );
    let traces = TreeVec::new(vec![preprocessed, vec![], interaction]);
    let trace_polys = traces.map_cols(|column| column.interpolate());
    let eval = preprocessed_schedule::component::air::Eval {
        log_size,
        active: felt(1),
        relations,
    };
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |row| {
            eval.evaluate(row);
        },
        claimed_sum,
    );
}

#[test]
fn test_mixed_component_commits_only_witness_columns() {
    let mut table = mixed_preprocessed_schedule::MixedScheduleTable::new();
    table.push(7);

    assert_eq!(table.into_witness().len(), 2);
}

#[test]
fn test_mixed_component_uses_trusted_enabler_profile() {
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    let constraints = mixed_preprocessed_schedule::component::air::Eval {
        log_size: 4,
        active: felt(1),
        relations: mixed_preprocessed_schedule::Relations::dummy(),
    }
    .evaluate(ExprEvaluator::new())
    .constraint_degree_bounds();

    assert_eq!(constraints.len(), 3);
}

#[test]
fn test_mixed_component_shares_air_and_interaction_frame() {
    use simd::AlignedVec;
    use stwo::core::pcs::TreeVec;
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::poly::BitReversedOrder;
    use stwo::prover::poly::circle::CircleEvaluation;
    use stwo_constraint_framework::{FrameworkEval, assert_constraints_on_polys};

    let log_size = 4;
    let domain = CanonicCoset::new(log_size).circle_domain();
    let make_column = |value, first_row_only| {
        let mut data = AlignedVec::with_capacity(1 << log_size);
        data.resize(1 << log_size, if first_row_only { 0 } else { value });
        if first_row_only {
            data[0] = value;
        }
        CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(
            domain,
            BaseColumn::from(data),
        )
    };
    let preprocessed = vec![make_column(1, true), make_column(7, false)];
    let mut table = mixed_preprocessed_schedule::MixedScheduleTable::new();
    table.push(7);
    let trace = table.into_witness();
    let relations = mixed_preprocessed_schedule::Relations::dummy();
    let (interaction, claimed_sum) =
        mixed_preprocessed_schedule::component::witness::gen_interaction_trace(
            &trace,
            &preprocessed,
            felt(1),
            &relations,
        );
    let traces = TreeVec::new(vec![preprocessed, trace, interaction]);
    let trace_polys = traces.map_cols(|column| column.interpolate());
    let eval = mixed_preprocessed_schedule::component::air::Eval {
        log_size,
        active: felt(1),
        relations,
    };
    assert_constraints_on_polys(
        &trace_polys,
        CanonicCoset::new(log_size),
        |row| {
            eval.evaluate(row);
        },
        claimed_sum,
    );
}

#[test]
fn test_external_relation_balances_across_functions() {
    let mut tables = shared::Tables::default();
    let produced = shared::call_source(&mut tables, [felt(9)]);
    let consumed = shared::call_sink(&mut tables, [felt(9)]);
    assert_eq!(produced, consumed);

    let activations = vec![
        shared::Activation::Source {
            inputs: [felt(9)],
            outputs: produced,
        },
        shared::Activation::Sink {
            inputs: [felt(9)],
            outputs: consumed,
        },
    ];
    let proof = shared::prove_air_fns(tables, activations, PcsConfig::default());
    shared::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_external_relation_rejects_unbalanced_emit() {
    // `source` emits `pass(9)` but `sink` consumes `pass(7)`: the relation
    // does not close, so the claimed sums do not cancel.
    let mut tables = shared::Tables::default();
    let produced = shared::call_source(&mut tables, [felt(9)]);
    let consumed = shared::call_sink(&mut tables, [felt(7)]);

    let activations = vec![
        shared::Activation::Source {
            inputs: [felt(9)],
            outputs: produced,
        },
        shared::Activation::Sink {
            inputs: [felt(7)],
            outputs: consumed,
        },
    ];
    let proof = shared::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(shared::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_external_relation_adds_one_column_per_side() {
    use shared::prover_columns::{SinkColumns, SourceColumns};

    // source: enabler + x. The emitted `pass(x)` references the existing
    // column x, so no extra committed column is needed.
    assert_eq!(SourceColumns::<()>::SIZE, 2);
    assert_eq!(SinkColumns::<()>::SIZE, 2);
}

// Hints: a prover-chosen committed column, free in the AIR, constrained by
// the body. Opcodes use these for carries / sign bits / inverse markers.
mod hints {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        fn double_it(x) {
            hint y = x + x;
            assert y == x + x;
            return y;
        }
    }
}

mod word_intrinsics {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        relation range_check_8_8(2);
        relation range_check_m31(2);
        relation bitwise(4);

        fn split_and_combine(value) {
            let limbs = split_m31(value);
            let low_nibble = bitand(limbs[0], 15, enabler);
            let high_bit = bitor(limbs[0], 128);
            let flipped_nibble = bitxor(limbs[0], 15);
            return (limbs[0], limbs[1], limbs[2], limbs[3], low_nibble, high_bit, flipped_nibble);
        }

        fn wrapping_math(lhs: [felt; 4], rhs: [felt; 4]) {
            let (sum, carry) = add_u32(lhs, rhs, enabler);
            let (difference, borrow) = sub_u32(lhs, rhs);
            return (sum, carry, difference, borrow);
        }

        fn divide_words(lhs: [felt; 4], rhs: [felt; 4], signed) {
            let (
                quotient,
                remainder,
                zero_divisor,
                zero_remainder,
                overflow,
                divisor_sum_inverse,
                remainder_sum_inverse,
            ) = divrem_u32(lhs, rhs, signed);
            return (
                quotient,
                remainder,
                zero_divisor,
                zero_remainder,
                overflow,
                divisor_sum_inverse,
                remainder_sum_inverse,
            );
        }
    }
}

#[rstest::rstest]
#[case(0, 0x78)]
#[case(1, 0x56)]
#[case(2, 0x34)]
#[case(3, 0x12)]
#[case(4, 0x08)]
#[case(5, 0xf8)]
#[case(6, 0x77)]
fn word_intrinsic_binds_expected_output(#[case] position: usize, #[case] expected: u32) {
    let mut tables = word_intrinsics::Tables::default();
    let outputs = word_intrinsics::call_split_and_combine(&mut tables, [felt(0x1234_5678)]);

    assert_eq!(outputs[position], felt(expected));
}

#[test]
fn word_intrinsic_commits_split_and_bitwise_outputs() {
    use word_intrinsics::prover_columns::SplitAndCombineColumns;

    assert_eq!(SplitAndCombineColumns::<()>::SIZE, 9);
}

#[rstest::rstest]
#[case(0, 3)]
#[case(1, 0)]
#[case(2, 0)]
#[case(3, 0)]
#[case(4, 1)]
#[case(5, 0xf9)]
#[case(6, 0xff)]
#[case(7, 0xff)]
#[case(8, 0xff)]
#[case(9, 0)]
fn word_arithmetic_binds_wrapping_limbs_and_terminal_flag(
    #[case] position: usize,
    #[case] expected: u32,
) {
    let mut tables = word_intrinsics::Tables::default();
    let lhs = (u32::MAX - 1).to_le_bytes().map(|limb| felt(limb.into()));
    let rhs = 5u32.to_le_bytes().map(|limb| felt(limb.into()));
    let inputs = [
        lhs[0], lhs[1], lhs[2], lhs[3], rhs[0], rhs[1], rhs[2], rhs[3],
    ];
    let outputs = word_intrinsics::call_wrapping_math(&mut tables, inputs);

    assert_eq!(outputs[position], felt(expected));
}

#[test]
fn word_arithmetic_sets_terminal_borrow_on_underflow() {
    let mut tables = word_intrinsics::Tables::default();
    let lhs = 1u32.to_le_bytes().map(|limb| felt(limb.into()));
    let rhs = 2u32.to_le_bytes().map(|limb| felt(limb.into()));
    let inputs = [
        lhs[0], lhs[1], lhs[2], lhs[3], rhs[0], rhs[1], rhs[2], rhs[3],
    ];
    let outputs = word_intrinsics::call_wrapping_math(&mut tables, inputs);

    assert_eq!(outputs[9], felt(1));
}

fn divide_word_outputs(lhs: u32, rhs: u32, signed: u32) -> [BaseField; 13] {
    let mut tables = word_intrinsics::Tables::default();
    let lhs = lhs.to_le_bytes().map(|limb| felt(limb.into()));
    let rhs = rhs.to_le_bytes().map(|limb| felt(limb.into()));
    word_intrinsics::call_divide_words(
        &mut tables,
        [
            lhs[0],
            lhs[1],
            lhs[2],
            lhs[3],
            rhs[0],
            rhs[1],
            rhs[2],
            rhs[3],
            felt(signed),
        ],
    )
}

fn output_word(outputs: &[BaseField], start: usize) -> u32 {
    u32::from_le_bytes(std::array::from_fn(|position| {
        outputs[start + position].0 as u8
    }))
}

#[rstest::rstest]
#[case(7, (-3i32) as u32, 1, 0, (-2i32) as u32)]
#[case((-7i32) as u32, 3, 1, 4, (-1i32) as u32)]
#[case(u32::MAX, 2, 0, 0, u32::MAX / 2)]
fn division_witness_binds_expected_word(
    #[case] lhs: u32,
    #[case] rhs: u32,
    #[case] signed: u32,
    #[case] start: usize,
    #[case] expected: u32,
) {
    let outputs = divide_word_outputs(lhs, rhs, signed);

    assert_eq!(output_word(&outputs, start), expected);
}

#[rstest::rstest]
#[case(5, 0, 1, 8, 1)]
#[case(5, 0, 1, 9, 0)]
#[case(0x8000_0000, u32::MAX, 1, 9, 1)]
#[case(0x8000_0000, u32::MAX, 1, 10, 1)]
fn division_witness_binds_exception_flag(
    #[case] lhs: u32,
    #[case] rhs: u32,
    #[case] signed: u32,
    #[case] position: usize,
    #[case] expected: u32,
) {
    let outputs = divide_word_outputs(lhs, rhs, signed);

    assert_eq!(outputs[position], felt(expected));
}

#[test]
fn test_hint_roundtrips_and_verifies() {
    let mut tables = hints::Tables::default();
    let out = hints::call_double_it(&mut tables, [felt(5)]);
    assert_eq!(out, [felt(10)]);

    let activations = vec![hints::Activation::DoubleIt {
        inputs: [felt(5)],
        outputs: out,
    }];
    let proof = hints::prove_air_fns(tables, activations, PcsConfig::default());
    hints::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_hint_is_a_committed_column() {
    use hints::prover_columns::DoubleItColumns;
    // enabler + x + the committed hint y = 3. (A plain `let y = x + x` would
    // make y a derived cell, not a column, leaving SIZE = 2.)
    assert_eq!(DoubleItColumns::<()>::SIZE, 3);
}

// A faithful miniature of the opcode-migration target (docs/felt-air-compiler.md
// step 4): opcodes as functions, the register/pc state carried by an external
// relation that telescopes across rows, a boundary closing the chain, and a
// prover-chosen hint constrained in-row — the same shape the rv32im opcode
// tables have, expressed entirely in the fn DSL.
mod mini_vm {
    stwo_macros::define_air_fns! {
        max_degree: 3,

        // (pc, clock) — the machine state between steps.
        relation reg_state(2);

        // One opcode: advance pc by 4 and the clock by 1.
        fn step(pc, clock) {
            consume reg_state(pc, clock);
            hint next_pc = pc + 4;
            assert next_pc == pc + 4;
            emit reg_state(next_pc, clock + 1);
            return next_pc;
        }

        // The program boundary: emit the entry state, consume the exit state.
        // Its activation is public, so closing the reg_state chain reduces to
        // the requested (entry, exit).
        fn boundary(entry_pc, entry_clock, exit_pc, exit_clock) {
            emit reg_state(entry_pc, entry_clock);
            consume reg_state(exit_pc, exit_clock);
            return entry_pc;
        }
    }
}

#[test]
fn test_mini_vm_two_steps_balance_through_boundary() {
    let mut tables = mini_vm::Tables::default();
    // Run two steps from (pc=0, clock=0): 0 -> 4 -> 8.
    let pc1 = mini_vm::call_step(&mut tables, [felt(0), felt(0)]);
    assert_eq!(pc1, [felt(4)]);
    let pc2 = mini_vm::call_step(&mut tables, [felt(4), felt(1)]);
    assert_eq!(pc2, [felt(8)]);
    let boundary = mini_vm::call_boundary(&mut tables, [felt(0), felt(0), felt(8), felt(2)]);

    let activations = vec![
        mini_vm::Activation::Step {
            inputs: [felt(0), felt(0)],
            outputs: pc1,
        },
        mini_vm::Activation::Step {
            inputs: [felt(4), felt(1)],
            outputs: pc2,
        },
        mini_vm::Activation::Boundary {
            inputs: [felt(0), felt(0), felt(8), felt(2)],
            outputs: boundary,
        },
    ];
    let proof = mini_vm::prove_air_fns(tables, activations, PcsConfig::default());
    mini_vm::verify_air_fns(proof, PcsConfig::default()).expect("verification failed");
}

#[test]
fn test_mini_vm_broken_chain_is_rejected() {
    // A boundary claiming the wrong exit state leaves the reg_state chain
    // open: the multiset does not cancel.
    let mut tables = mini_vm::Tables::default();
    let pc1 = mini_vm::call_step(&mut tables, [felt(0), felt(0)]);
    let pc2 = mini_vm::call_step(&mut tables, [felt(4), felt(1)]);
    let boundary = mini_vm::call_boundary(&mut tables, [felt(0), felt(0), felt(12), felt(3)]);

    let activations = vec![
        mini_vm::Activation::Step {
            inputs: [felt(0), felt(0)],
            outputs: pc1,
        },
        mini_vm::Activation::Step {
            inputs: [felt(4), felt(1)],
            outputs: pc2,
        },
        mini_vm::Activation::Boundary {
            inputs: [felt(0), felt(0), felt(12), felt(3)],
            outputs: boundary,
        },
    ];
    let proof = mini_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(mini_vm::verify_air_fns(proof, PcsConfig::default()).is_err());
}

trait AccessState {
    fn read_register(&self, index: u8) -> u32;
    fn write_register(&mut self, index: u8, value: u32);
    fn read_memory_word(&self, address: u32) -> u32;
    fn write_memory_word(&mut self, address: u32, value: u32);
}

struct AccessMachine {
    cpu: runner::Cpu,
    memory: runner::Memory,
}

impl AccessMachine {
    fn new() -> Self {
        Self {
            cpu: runner::Cpu::new(0, 0, 0),
            memory: runner::Memory::new(),
        }
    }
}

impl AccessState for AccessMachine {
    fn read_register(&self, index: u8) -> u32 {
        self.cpu.reg(index)
    }

    fn write_register(&mut self, index: u8, value: u32) {
        self.cpu.set_reg(index, value);
    }

    fn read_memory_word(&self, address: u32) -> u32 {
        self.memory.read_u32(address)
    }

    fn write_memory_word(&mut self, address: u32, value: u32) {
        self.memory.write_u32(address, value);
    }
}

mod access_vm {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        vm_access: {
            state: crate::AccessState,
            tracer: runner::Tracer,
        },

        relation memory_access(7);
        relation range_check_20(1);

        fn write_register_word(clock, addr, requested: [felt; 4]) {
            write_reg rd(clock, addr, requested);
            return rd_next;
        }

        fn read_register_word(clock, addr) {
            read_reg rs(clock, addr);
            return rs_next;
        }

        fn write_memory_word(clock, addr, requested: [felt; 4]) {
            write_mem dst(clock, addr, requested);
            return dst_next;
        }

        fn read_memory_word(clock, addr) {
            read_mem src(clock, addr);
            return src_next;
        }

        fn read_addressed_word(clock, addr_space, addr) {
            read_word src(clock, addr_space, addr);
            return src_next;
        }

        fn write_addressed_word(clock, addr_space, addr, requested: [felt; 4]) {
            write_word dst(clock, addr_space, addr, requested);
            return dst_next;
        }

        fn close_access(
            addr,
            before_clock,
            before: [felt; 4],
            after_clock,
            after: [felt; 4],
            diff,
        ) {
            emit memory_access(0, addr, before_clock, before);
            consume memory_access(0, addr, after_clock, after);
            emit range_check_20(diff);
            return addr;
        }

        fn close_memory_access(
            addr,
            before_clock,
            before: [felt; 4],
            after_clock,
            after: [felt; 4],
            diff,
        ) {
            emit memory_access(1, addr, before_clock, before);
            consume memory_access(1, addr, after_clock, after);
            emit range_check_20(diff);
            return addr;
        }

        fn close_word_access(
            addr_space,
            addr,
            before_clock,
            before: [felt; 4],
            after_clock,
            after: [felt; 4],
            diff,
        ) {
            emit memory_access(addr_space, addr, before_clock, before);
            consume memory_access(addr_space, addr, after_clock, after);
            emit range_check_20(diff);
            return addr;
        }
    }
}

mod embedded_access_vm {
    stwo_macros::define_air_fns! {
        max_degree: 3,
        embedded: [],
        vm_access: {
            state: crate::AccessState,
            tracer: crate::EmbeddedAccessTracer,
        },

        relation memory_access(7);
        relation range_check_20(1);

        fn embedded_write(clock, addr, requested: [felt; 4]) {
            write_reg rd(clock, addr, requested);
            return rd_next;
        }
    }
}

struct EmbeddedAccessTracer {
    clock: u32,
    embedded_write: embedded_access_vm::EmbeddedWriteTable,
    access: runner::Tracer,
}

impl EmbeddedAccessTracer {
    fn new(clock: u32) -> Self {
        let access = runner::Tracer {
            clock,
            ..Default::default()
        };
        Self {
            clock,
            embedded_write: embedded_access_vm::EmbeddedWriteTable::new(),
            access,
        }
    }

    fn trace_reg_access(&mut self, index: u8, prev: u32, next: u32) -> runner::Access {
        self.access.trace_reg_access(index, prev, next)
    }
}

#[test]
fn test_generated_register_write_mutates_state() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer::with_max_clock_diff(4);
    tracer.clock = 10;

    access_vm::call_write_register_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(5),
            felt(0x78),
            felt(0x56),
            felt(0x34),
            felt(0x12),
        ],
    );

    assert_eq!(state.cpu.reg(5), 0x1234_5678);
}

#[test]
fn test_embedded_access_fill_owns_the_tracer_table() {
    let mut state = AccessMachine::new();
    let mut tracer = EmbeddedAccessTracer::new(1);

    embedded_access_vm::embedded_write_fill(
        &mut state,
        &mut tracer,
        [
            felt(1),
            felt(5),
            felt(0x78),
            felt(0x56),
            felt(0x34),
            felt(0x12),
        ],
        [],
    );

    assert_eq!(
        (state.cpu.reg(5), tracer.embedded_write.len()),
        (0x1234_5678, 1)
    );
}

#[test]
fn test_generated_memory_write_preserves_initial_word() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    access_vm::call_write_memory_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(1),
            felt(0x1000),
            felt(0x88),
            felt(0x77),
            felt(0x66),
            felt(0x55),
        ],
    );

    assert_eq!(
        (state.memory.read_u32(0x1000), tracer.mem_initial[&0x1000]),
        (0x5566_7788, 0x4433_2211),
    );
}

#[test]
fn test_generated_memory_read_returns_aligned_word() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    let output = access_vm::call_read_memory_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [felt(1), felt(0x1000)],
    );

    assert_eq!(output, [felt(0x11), felt(0x22), felt(0x33), felt(0x44)]);
}

#[test]
fn test_generated_addressed_read_selects_registers() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.cpu.set_reg(5, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    let output = access_vm::call_read_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [felt(1), felt(0), felt(5)],
    );

    assert_eq!(output, [felt(0x11), felt(0x22), felt(0x33), felt(0x44)]);
}

#[test]
fn test_generated_addressed_read_selects_memory() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    let output = access_vm::call_read_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [felt(1), felt(1), felt(0x1000)],
    );

    assert_eq!(output, [felt(0x11), felt(0x22), felt(0x33), felt(0x44)]);
}

#[test]
fn test_generated_addressed_write_selects_registers() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    access_vm::call_write_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(1),
            felt(0),
            felt(5),
            felt(0x78),
            felt(0x56),
            felt(0x34),
            felt(0x12),
        ],
    );

    assert_eq!(state.cpu.reg(5), 0x1234_5678);
}

#[test]
fn test_generated_addressed_write_selects_memory() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    access_vm::call_write_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(1),
            felt(1),
            felt(0x1000),
            felt(0x78),
            felt(0x56),
            felt(0x34),
            felt(0x12),
        ],
    );

    assert_eq!(state.memory.read_u32(0x1000), 0x1234_5678);
}

#[test]
fn test_generated_addressed_write_preserves_x0() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 1,
        ..Default::default()
    };

    access_vm::call_write_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(1),
            felt(0),
            felt(0),
            felt(0x78),
            felt(0x56),
            felt(0x34),
            felt(0x12),
        ],
    );

    assert_eq!(state.cpu.reg(0), 0);
}

#[test]
fn test_generated_addressed_access_rejects_unknown_address_space() {
    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut tables = access_vm::Tables::default();
        let mut state = AccessMachine::new();
        let mut tracer = runner::Tracer {
            clock: 1,
            ..Default::default()
        };
        access_vm::call_read_addressed_word(
            &mut tables,
            &mut state,
            &mut tracer,
            [felt(1), felt(2), felt(5)],
        );
    }));

    assert!(rejected.is_err());
}

#[test]
fn test_generated_addressed_access_proves_and_verifies() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let output = access_vm::call_read_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [felt(10), felt(1), felt(0x1000)],
    );
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(1),
        felt(0x1000),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_word_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::ReadAddressedWord {
            inputs: [felt(10), felt(1), felt(0x1000)],
            outputs: output,
        },
        access_vm::Activation::CloseWordAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_ok());
}

#[test]
fn test_generated_addressed_access_rejects_non_boolean_air_row() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let output = access_vm::call_read_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [felt(10), felt(1), felt(0x1000)],
    );
    tables.read_addressed_word.addr_space[0] = 2;
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(2),
        felt(0x1000),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_word_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::ReadAddressedWord {
            inputs: [felt(10), felt(2), felt(0x1000)],
            outputs: output,
        },
        access_vm::Activation::CloseWordAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        access_vm::prove_air_fns(tables, activations, PcsConfig::default())
    }));
    assert!(rejected.is_err());
}

#[test]
fn test_generated_addressed_memory_write_at_zero_proves_and_verifies() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(1), felt(0), felt(0), felt(0)];
    let output = access_vm::call_write_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(1),
            felt(0),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    let before = [felt(0), felt(0), felt(0), felt(0)];
    let boundary_inputs = [
        felt(1),
        felt(0),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_word_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteAddressedWord {
            inputs: [
                felt(10),
                felt(1),
                felt(0),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: output,
        },
        access_vm::Activation::CloseWordAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_ok());
}

#[test]
fn test_generated_addressed_register_write_rejects_nonzero_x0_air_row() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(1), felt(0), felt(0), felt(0)];
    access_vm::call_write_addressed_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(0),
            felt(0),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    tables.write_addressed_word.dst_next_0[0] = 1;
    let zero = [felt(0), felt(0), felt(0), felt(0)];
    let boundary_inputs = [
        felt(0),
        felt(0),
        felt(0),
        zero[0],
        zero[1],
        zero[2],
        zero[3],
        felt(10),
        requested[0],
        requested[1],
        requested[2],
        requested[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_word_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteAddressedWord {
            inputs: [
                felt(10),
                felt(0),
                felt(0),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: requested,
        },
        access_vm::Activation::CloseWordAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        access_vm::prove_air_fns(tables, activations, PcsConfig::default())
    }));
    assert!(rejected.is_err());
}

#[test]
fn test_generated_memory_access_proves_and_verifies() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.memory.write_u32(0x1000, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(0x88), felt(0x77), felt(0x66), felt(0x55)];
    let output = access_vm::call_write_memory_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(0x1000),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(0x1000),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_memory_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteMemoryWord {
            inputs: [
                felt(10),
                felt(0x1000),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: output,
        },
        access_vm::Activation::CloseMemoryAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_ok());
}

#[test]
fn test_generated_access_fills_clock_gaps() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer::with_max_clock_diff(4);
    tracer.clock = 10;

    access_vm::call_read_register_word(&mut tables, &mut state, &mut tracer, [felt(10), felt(5)]);

    assert_eq!(tracer.clock_update.len(), 2);
}

#[test]
fn test_generated_register_access_proves_and_verifies() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.cpu.set_reg(5, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(0x88), felt(0x77), felt(0x66), felt(0x55)];
    let output = access_vm::call_write_register_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(5),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary = access_vm::call_close_access(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(5),
            felt(0),
            before[0],
            before[1],
            before[2],
            before[3],
            felt(10),
            output[0],
            output[1],
            output[2],
            output[3],
            felt(10),
        ],
    );
    let activations = vec![
        access_vm::Activation::WriteRegisterWord {
            inputs: [
                felt(10),
                felt(5),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: output,
        },
        access_vm::Activation::CloseAccess {
            inputs: [
                felt(5),
                felt(0),
                before[0],
                before[1],
                before[2],
                before[3],
                felt(10),
                output[0],
                output[1],
                output[2],
                output[3],
                felt(10),
            ],
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_ok());
}

#[test]
fn test_generated_register_access_rejects_stale_clock() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.cpu.set_reg(5, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(0x88), felt(0x77), felt(0x66), felt(0x55)];
    let output = access_vm::call_write_register_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(5),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    tables.write_register_word.rd_clock_prev[0] = 1;
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(5),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteRegisterWord {
            inputs: [
                felt(10),
                felt(5),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: output,
        },
        access_vm::Activation::CloseAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_generated_register_access_rejects_incorrect_prior_value() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.cpu.set_reg(5, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(0x88), felt(0x77), felt(0x66), felt(0x55)];
    let output = access_vm::call_write_register_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(5),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    tables.write_register_word.rd_prev_0[0] = 0x12;
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(5),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        output[0],
        output[1],
        output[2],
        output[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteRegisterWord {
            inputs: [
                felt(10),
                felt(5),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: output,
        },
        access_vm::Activation::CloseAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let proof = access_vm::prove_air_fns(tables, activations, PcsConfig::default());
    assert!(access_vm::verify_air_fns(proof, PcsConfig::default()).is_err());
}

#[test]
fn test_generated_register_read_rejects_a_write() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    state.cpu.set_reg(5, 0x4433_2211);
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    access_vm::call_read_register_word(&mut tables, &mut state, &mut tracer, [felt(10), felt(5)]);
    tables.read_register_word.rs_next_0[0] = 0x12;
    let before = [felt(0x11), felt(0x22), felt(0x33), felt(0x44)];
    let forged_after = [felt(0x12), felt(0x22), felt(0x33), felt(0x44)];
    let boundary_inputs = [
        felt(5),
        felt(0),
        before[0],
        before[1],
        before[2],
        before[3],
        felt(10),
        forged_after[0],
        forged_after[1],
        forged_after[2],
        forged_after[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::ReadRegisterWord {
            inputs: [felt(10), felt(5)],
            outputs: forged_after,
        },
        access_vm::Activation::CloseAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        access_vm::prove_air_fns(tables, activations, PcsConfig::default())
    }));
    assert!(rejected.is_err());
}

#[test]
fn test_generated_register_write_rejects_nonzero_x0() {
    let mut tables = access_vm::Tables::default();
    let mut state = AccessMachine::new();
    let mut tracer = runner::Tracer {
        clock: 10,
        ..Default::default()
    };
    let requested = [felt(1), felt(0), felt(0), felt(0)];
    access_vm::call_write_register_word(
        &mut tables,
        &mut state,
        &mut tracer,
        [
            felt(10),
            felt(0),
            requested[0],
            requested[1],
            requested[2],
            requested[3],
        ],
    );
    tables.write_register_word.rd_next_0[0] = 1;
    let boundary_inputs = [
        felt(0),
        felt(0),
        felt(0),
        felt(0),
        felt(0),
        felt(0),
        felt(10),
        requested[0],
        requested[1],
        requested[2],
        requested[3],
        felt(10),
    ];
    let boundary =
        access_vm::call_close_access(&mut tables, &mut state, &mut tracer, boundary_inputs);
    let activations = vec![
        access_vm::Activation::WriteRegisterWord {
            inputs: [
                felt(10),
                felt(0),
                requested[0],
                requested[1],
                requested[2],
                requested[3],
            ],
            outputs: requested,
        },
        access_vm::Activation::CloseAccess {
            inputs: boundary_inputs,
            outputs: boundary,
        },
    ];

    let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        access_vm::prove_air_fns(tables, activations, PcsConfig::default())
    }));
    assert!(rejected.is_err());
}
