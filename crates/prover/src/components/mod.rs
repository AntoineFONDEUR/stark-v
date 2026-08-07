//! Component system for tracer-backed and preprocessed AIR components.

// Every bare entry's whole component module (AIR + witness) is generated from
// its `define_air!` table declaration. A `name: module` entry reuses a
// component generated through the AIR DSL in its owning crate.
stwo_macros::components! {
    trace: {
        auipc,
        base_alu_imm,
        base_alu_reg,
        branch_eq,
        branch_lt,
        commit,
        div,
        jal,
        jalr,
        load_store,
        lt_imm,
        lt_reg,
        lui,
        mul,
        mulh,
        shifts_imm,
        shifts_reg,
        program,
        memory,
        merkle,
        clock_update,
    },
    // The segment prover commits this DSL-owned table in its hash instance.
    detached: {
        poseidon2,
    },
    lookup: {
        bitwise,
        range_check_20,
        range_check_8_11,
        range_check_8_8_4,
        range_check_8_8,
        range_check_m31,
    },
}
#[cfg(test)]
mod tests {
    use num_traits::Zero;
    use stwo::core::fields::m31::BaseField;
    use stwo::core::fields::qm31::SecureField;
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

    #[test]
    fn component_claim_positional_layout_round_trips() {
        let log_sizes = core::array::from_fn(|index| index as u32 + 4);
        assert_eq!(
            super::Claim::from_component_log_sizes(log_sizes).component_log_sizes(),
            log_sizes
        );
    }

    #[test]
    fn component_claimed_sum_positional_layout_round_trips() {
        let values =
            core::array::from_fn(|index| SecureField::from(BaseField::from(index as u32 + 1)));
        assert_eq!(
            super::ClaimedSum::from_component_values(values).component_values(),
            values
        );
    }

    #[test]
    fn fixed_trace_generation_pads_to_the_requested_component_layout() {
        let natural = super::gen_trace(air::trace::Tracer::default());
        let mut log_sizes = super::Claim::from(&natural).component_log_sizes();
        log_sizes[0] += 1;
        let fixed = super::gen_trace_at_log_sizes(air::trace::Tracer::default(), log_sizes)
            .expect("the larger fixed layout contains every trace row");
        assert_eq!(super::Claim::from(&fixed).component_log_sizes(), log_sizes);
    }

    #[test]
    fn fixed_trace_generation_rejects_a_component_below_the_minimum_layout() {
        let natural = super::gen_trace(air::trace::Tracer::default());
        let mut log_sizes = super::Claim::from(&natural).component_log_sizes();
        log_sizes[0] = 3;
        assert!(matches!(
            super::gen_trace_at_log_sizes(air::trace::Tracer::default(), log_sizes),
            Err(super::FixedTraceError::ComponentCapacityExceeded {
                component: "auipc",
                rows: 0,
                log_size: 3,
            })
        ));
    }

    // One end-to-end proof per opcode guest binary.
    crate::test_bin_e2e!(auipc, auipc);
    crate::test_bin_e2e!(base_alu_imm, addi);
    crate::test_bin_e2e!(base_alu_imm, xori);
    crate::test_bin_e2e!(base_alu_imm, ori);
    crate::test_bin_e2e!(base_alu_imm, andi);
    crate::test_bin_e2e!(base_alu_reg, add);
    crate::test_bin_e2e!(base_alu_reg, sub);
    crate::test_bin_e2e!(base_alu_reg, xor);
    crate::test_bin_e2e!(base_alu_reg, or);
    crate::test_bin_e2e!(base_alu_reg, and);
    crate::test_bin_e2e!(branch_eq, beq);
    crate::test_bin_e2e!(branch_eq, bne);
    crate::test_bin_e2e!(branch_lt, blt);
    crate::test_bin_e2e!(branch_lt, bge);
    crate::test_bin_e2e!(branch_lt, bltu);
    crate::test_bin_e2e!(branch_lt, bgeu);
    crate::test_bin_e2e!(div, div);
    crate::test_bin_e2e!(div, divu);
    crate::test_bin_e2e!(div, rem);
    crate::test_bin_e2e!(div, remu);
    crate::test_bin_e2e!(jal, jal);
    crate::test_bin_e2e!(jalr, jalr);
    crate::test_bin_e2e!(load_store, lb);
    crate::test_bin_e2e!(load_store, lh);
    crate::test_bin_e2e!(load_store, lw);
    crate::test_bin_e2e!(load_store, lbu);
    crate::test_bin_e2e!(load_store, lhu);
    crate::test_bin_e2e!(load_store, sb);
    crate::test_bin_e2e!(load_store, sh);
    crate::test_bin_e2e!(load_store, sw);
    crate::test_bin_e2e!(lt_imm, slti);
    crate::test_bin_e2e!(lt_imm, sltiu);
    crate::test_bin_e2e!(lt_reg, slt);
    crate::test_bin_e2e!(lt_reg, sltu);
    crate::test_bin_e2e!(lui, lui);
    crate::test_bin_e2e!(mul, mul);
    crate::test_bin_e2e!(mulh, mulh);
    crate::test_bin_e2e!(mulh, mulhsu);
    crate::test_bin_e2e!(mulh, mulhu);
    crate::test_bin_e2e!(shifts_imm, slli);
    crate::test_bin_e2e!(shifts_imm, srli);
    crate::test_bin_e2e!(shifts_imm, srai);
    crate::test_bin_e2e!(shifts_reg, sll);
    crate::test_bin_e2e!(shifts_reg, srl);
    crate::test_bin_e2e!(shifts_reg, sra);

    // The quadratic carry denominators keep mul/mulh at fixed constraint
    // counts; a change here means the degree-bound analysis must be redone.
    #[test]
    fn test_mul_constraint_degree_bounds() {
        let eval = super::mul::air::Eval {
            log_size: 6,
            relations: crate::relations::Relations::dummy(),
        };
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        assert_eq!(degrees.len(), 17);
    }

    #[test]
    fn test_mulh_constraint_degree_bounds() {
        let eval = super::mulh::air::Eval {
            log_size: 6,
            relations: crate::relations::Relations::dummy(),
        };
        let expr_eval = eval.evaluate(ExprEvaluator::new());
        let degrees = expr_eval.constraint_degree_bounds();
        assert_eq!(degrees.len(), 28);
    }

    #[test]
    fn test_mul_info_offsets() {
        let eval = super::mul::air::Eval {
            log_size: 6,
            relations: crate::relations::Relations::dummy(),
        };
        let info = eval.evaluate(stwo_constraint_framework::InfoEvaluator::new(
            eval.log_size,
            vec![],
            stwo::core::fields::qm31::SecureField::zero(),
        ));
        assert!(!info.mask_offsets.is_empty());
    }

    crate::test_lookup_e2e!(base_alu_reg, bitwise, and);
    crate::test_lookup_e2e!(base_alu_reg, bitwise, or);
    crate::test_lookup_e2e!(base_alu_reg, bitwise, xor);

    crate::test_lookup_e2e!(base_alu_imm, range_check_8_8, addi);
    crate::test_lookup_e2e!(base_alu_reg, range_check_8_8, add);
    crate::test_lookup_e2e!(base_alu_reg, range_check_8_8, sub);

    crate::test_lookup_e2e!(shifts_reg, range_check_8_11, sll);
    crate::test_lookup_e2e!(shifts_reg, range_check_8_11, srl);

    crate::test_lookup_e2e!(load_store, range_check_8_8_4, lb);
    crate::test_lookup_e2e!(load_store, range_check_8_8_4, sb);

    crate::test_lookup_e2e!(div, range_check_m31, div);

    crate::test_lookup_e2e!(base_alu_reg, range_check_20, add);
    crate::test_lookup_e2e!(load_store, range_check_20, lw);
}
