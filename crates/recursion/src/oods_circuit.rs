//! OODS point geometry and composition-value arithmetic for recursion.
//!
//! The circuit maps the first secure transcript draw to STWO's circle point,
//! evaluates the fixed composition coset's vanishing polynomial at that point,
//! and combines the two split composition evaluations. Inverses are rejected
//! at witness construction when their denominator is zero, matching the
//! algebraic inverse constraints emitted by circuit lowering.

use core::fmt;

use num_traits::{One, Zero};
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::poly::circle::{
    CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE, MIN_CIRCLE_DOMAIN_LOG_SIZE,
};

use crate::recorder::Rec;

/// Circle point whose coordinates are arithmetic-circuit values.
#[derive(Clone, Debug, PartialEq)]
pub struct OodsPointCircuit {
    pub x: Rec,
    pub y: Rec,
}

/// Maps STWO's secure draw parameter to a point on the circle.
pub fn oods_point_from_seed(seed: Rec) -> Result<OodsPointCircuit, OodsCircuitError> {
    let square = seed.clone() * seed.clone();
    let denominator = Rec::one() + square.clone();
    if denominator.value().is_zero() {
        return Err(OodsCircuitError::ZeroPointDenominator);
    }
    let inverse = denominator.inverse();
    Ok(OodsPointCircuit {
        x: (Rec::one() - square) * inverse.clone(),
        y: (seed.clone() + seed) * inverse,
    })
}

/// Evaluates and inverts the fixed composition coset's vanishing polynomial.
pub fn coset_vanishing_inverse(
    point: &OodsPointCircuit,
    coset_log_size: u32,
) -> Result<Rec, OodsCircuitError> {
    if !(MIN_CIRCLE_DOMAIN_LOG_SIZE..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&coset_log_size) {
        return Err(OodsCircuitError::LogSizeOutOfRange {
            log_size: coset_log_size,
        });
    }
    let coset = CanonicCoset::new(coset_log_size).coset;
    // One constant rotation turns the composition coset into the canonical
    // half-step coset before the x-only doubling polynomial is evaluated.
    let rotation = (-coset.initial_index + coset.step_size.half()).to_point();
    let mut x = point.x.clone() * Rec::from(rotation.x) - point.y.clone() * Rec::from(rotation.y);
    for _ in 1..coset_log_size {
        x = double_x(x);
    }
    if x.value().is_zero() {
        return Err(OodsCircuitError::ZeroVanishingDenominator {
            log_size: coset_log_size,
        });
    }
    Ok(x.inverse())
}

/// Recombines STWO's left and right split composition coordinate evaluations.
pub fn combine_split_composition(
    left_coordinates: [Rec; SECURE_EXTENSION_DEGREE],
    right_coordinates: [Rec; SECURE_EXTENSION_DEGREE],
    oods_x: Rec,
    max_log_degree_bound: u32,
) -> Result<Rec, OodsCircuitError> {
    if max_log_degree_bound > MAX_CIRCLE_DOMAIN_LOG_SIZE {
        return Err(OodsCircuitError::CompositionLogDegreeOutOfRange {
            log_size: max_log_degree_bound,
        });
    }
    let doubles = max_log_degree_bound
        .checked_sub(1)
        .ok_or(OodsCircuitError::ZeroCompositionLogDegree)?;
    let split_factor = repeated_double_x(oods_x, doubles);
    Ok(combine_partial_evaluations(left_coordinates)
        + split_factor * combine_partial_evaluations(right_coordinates))
}

fn repeated_double_x(mut x: Rec, doubles: u32) -> Rec {
    for _ in 0..doubles {
        x = double_x(x);
    }
    x
}

fn double_x(x: Rec) -> Rec {
    let square = x.clone() * x;
    square.clone() + square - Rec::one()
}

fn combine_partial_evaluations(values: [Rec; SECURE_EXTENSION_DEGREE]) -> Rec {
    let [v0, v1, v2, v3] = values;
    v0 + v1 * basis(1) + v2 * basis(2) + v3 * basis(3)
}

fn basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        BaseField::from(u32::from(limb == index))
    }))
}

/// Invalid OODS point or unsupported fixed composition geometry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OodsCircuitError {
    ZeroPointDenominator,
    LogSizeOutOfRange { log_size: u32 },
    ZeroVanishingDenominator { log_size: u32 },
    ZeroCompositionLogDegree,
    CompositionLogDegreeOutOfRange { log_size: u32 },
}

impl fmt::Display for OodsCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for OodsCircuitError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::circle::CirclePoint;
    use stwo::core::constraints::coset_vanishing;
    use stwo::core::fields::FieldExpOps;
    use stwo::core::fields::m31::M31;

    use super::*;

    fn secure(seed: u32) -> SecureField {
        SecureField::from_m31_array([
            M31::from(seed),
            M31::from(seed + 1),
            M31::from(seed + 2),
            M31::from(seed + 3),
        ])
    }

    fn native_point(seed: SecureField) -> CirclePoint<SecureField> {
        let square = seed * seed;
        let inverse = (SecureField::one() + square).inverse();
        CirclePoint {
            x: (SecureField::one() - square) * inverse,
            y: (seed + seed) * inverse,
        }
    }

    #[rstest]
    fn oods_point_matches_stwo_rational_parameterization() {
        let seed = secure(7);
        let actual = oods_point_from_seed(Rec::from(seed)).expect("fixture denominator is nonzero");
        let expected = native_point(seed);
        assert_eq!(
            (actual.x.value(), actual.y.value()),
            (expected.x, expected.y)
        );
    }

    #[rstest]
    fn mapped_oods_point_satisfies_the_circle_equation() {
        let point =
            oods_point_from_seed(Rec::from(secure(11))).expect("fixture denominator is nonzero");
        assert_eq!(
            point.x.value() * point.x.value() + point.y.value() * point.y.value(),
            SecureField::one()
        );
    }

    #[rstest]
    #[case(4)]
    #[case(6)]
    #[case(30)]
    fn coset_inverse_matches_stwo(#[case] log_size: u32) {
        let seed = secure(log_size + 20);
        let native = native_point(seed);
        let circuit =
            oods_point_from_seed(Rec::from(seed)).expect("fixture point denominator is nonzero");
        assert_eq!(
            coset_vanishing_inverse(&circuit, log_size)
                .expect("fixture misses the component coset")
                .value(),
            coset_vanishing(CanonicCoset::new(log_size).coset, native).inverse()
        );
    }

    #[rstest]
    #[case(4)]
    #[case(17)]
    #[case(30)]
    fn split_composition_matches_stwo(#[case] max_log_degree_bound: u32) {
        let seed = secure(max_log_degree_bound + 40);
        let point = native_point(seed);
        let left = core::array::from_fn(|index| secure(100 + index as u32));
        let right = core::array::from_fn(|index| secure(200 + index as u32));
        let actual = combine_split_composition(
            left.map(Rec::from),
            right.map(Rec::from),
            Rec::from(point.x),
            max_log_degree_bound,
        )
        .expect("fixture composition degree is nonzero");
        let expected = SecureField::from_partial_evals(left)
            + point.repeated_double(max_log_degree_bound - 1).x
                * SecureField::from_partial_evals(right);
        assert_eq!(actual.value(), expected);
    }

    #[rstest]
    fn square_root_of_minus_one_is_rejected_as_an_oods_seed() {
        let sqrt_minus_one =
            SecureField::from_m31_array([M31::from(0), M31::from(1), M31::from(0), M31::from(0)]);
        assert_eq!(
            oods_point_from_seed(Rec::from(sqrt_minus_one)),
            Err(OodsCircuitError::ZeroPointDenominator)
        );
    }

    #[rstest]
    fn point_on_composition_coset_is_rejected_before_inverse_lowering() {
        let point: CirclePoint<SecureField> = CanonicCoset::new(4).coset.initial.into_ef();
        let circuit = OodsPointCircuit {
            x: Rec::from(point.x),
            y: Rec::from(point.y),
        };
        assert_eq!(
            coset_vanishing_inverse(&circuit, 4),
            Err(OodsCircuitError::ZeroVanishingDenominator { log_size: 4 })
        );
    }

    #[rstest]
    fn oversized_composition_degree_is_rejected_before_doubling() {
        assert_eq!(
            combine_split_composition(
                core::array::from_fn(|_| Rec::zero()),
                core::array::from_fn(|_| Rec::zero()),
                Rec::zero(),
                MAX_CIRCLE_DOMAIN_LOG_SIZE + 1,
            ),
            Err(OodsCircuitError::CompositionLogDegreeOutOfRange {
                log_size: MAX_CIRCLE_DOMAIN_LOG_SIZE + 1,
            })
        );
    }
}
