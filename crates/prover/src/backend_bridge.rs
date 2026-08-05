//! Representation-preserving trace conversion between prover backends.

use stwo::core::fields::m31::{BaseField, P};
use stwo::prover::backend::CpuBackend;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::CircleEvaluation;

pub(crate) fn checked_m31_from_raw(raw: u32) -> BaseField {
    assert!(
        raw <= P,
        "trace contains an invalid M31 representative: {raw}"
    );
    BaseField::from_u32_unchecked(raw)
}

/// Copies a SIMD evaluation into CPU-owned storage without reducing M31 values.
///
/// STWO permits the two raw representatives `0` and `P` for the zero field
/// element. Commitments hash those representatives, so backend conversion must
/// retain the exact words rather than canonicalizing them.
pub(crate) fn simd_circle_evaluation_to_cpu<EvalOrder>(
    evaluation: CircleEvaluation<SimdBackend, BaseField, EvalOrder>,
) -> CircleEvaluation<CpuBackend, BaseField, EvalOrder> {
    let values = evaluation
        .values
        .as_slice()
        .iter()
        .map(|value| checked_m31_from_raw(value.0))
        .collect();

    CircleEvaluation::new(evaluation.domain, values)
}

pub(crate) fn simd_circle_evaluations_to_cpu<EvalOrder>(
    evaluations: Vec<CircleEvaluation<SimdBackend, BaseField, EvalOrder>>,
) -> Vec<CircleEvaluation<CpuBackend, BaseField, EvalOrder>> {
    evaluations
        .into_iter()
        .map(simd_circle_evaluation_to_cpu)
        .collect()
}

#[cfg(test)]
mod tests {
    use stwo::core::fields::m31::{BaseField, P};
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::prover::backend::simd::column::BaseColumn;
    use stwo::prover::poly::BitReversedOrder;

    use super::*;

    #[test]
    fn conversion_preserves_raw_zero_representatives_domain_and_order() {
        let domain = CanonicCoset::new(2).circle_domain();
        let raw_values = [0, P, P - 1, 1];
        let values: BaseColumn = raw_values
            .into_iter()
            .map(BaseField::from_u32_unchecked)
            .collect();
        let evaluation =
            CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(domain, values);

        let converted = simd_circle_evaluation_to_cpu(evaluation);

        assert_eq!(converted.domain, domain);
        assert_eq!(
            converted
                .values
                .iter()
                .map(|value| value.0)
                .collect::<Vec<_>>(),
            raw_values
        );
    }

    #[test]
    #[should_panic(expected = "invalid M31 representative")]
    fn conversion_rejects_out_of_range_representative() {
        let domain = CanonicCoset::new(1).circle_domain();
        let values: BaseColumn = [0, P + 1]
            .into_iter()
            .map(BaseField::from_u32_unchecked)
            .collect();
        let evaluation =
            CircleEvaluation::<SimdBackend, BaseField, BitReversedOrder>::new(domain, values);

        let _ = simd_circle_evaluation_to_cpu(evaluation);
    }
}
