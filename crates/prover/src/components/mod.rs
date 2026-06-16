//! Component system for tracer-backed and preprocessed AIR components.

// Every bare entry's whole component module (air + witness) is generated
// from its `define_trace_tables!` declaration; `name: module` entries point
// at a hand-written or macro-generated module instead.
stwo_macros::components! {
    trace: {
        auipc,
        base_alu_imm,
        base_alu_reg,
        branch_eq,
        branch_lt,
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
        poseidon2: air::poseidon2::component,
        clock_update,
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
    use stwo_constraint_framework::FrameworkEval;
    use stwo_constraint_framework::expr::ExprEvaluator;

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
