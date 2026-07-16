//! Transcript-bound formal relation parameters for recursion V2 AIR evaluation.
//!
//! The AIR registry and `Relations::draw` share one macro-generated order.
//! Each complete eight-word transcript draw is decoded into `z` and raw
//! `alpha`; every formal alpha power is then derived inside the arithmetic
//! circuit, so a proof cannot assign the powers independently.

use core::fmt;
use std::collections::HashMap;

use num_traits::One;
use prover::relations::RelationDescriptor;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};

use crate::recorder::Rec;

/// Two secure-field values, `z` followed by raw `alpha`.
pub const RELATION_CHALLENGE_WORD_COUNT: usize = 2 * SECURE_EXTENSION_DEGREE;

/// Complete transcript output assigned to one relation registry entry.
#[derive(Clone, Debug)]
pub struct RelationChallengeCircuit {
    words: [Rec; RELATION_CHALLENGE_WORD_COUNT],
}

impl RelationChallengeCircuit {
    pub const fn new(words: [Rec; RELATION_CHALLENGE_WORD_COUNT]) -> Self {
        Self { words }
    }

    pub fn words(&self) -> &[Rec; RELATION_CHALLENGE_WORD_COUNT] {
        &self.words
    }
}

/// Builds every `<relation>_z` and `<relation>_alphaN` formal parameter.
pub fn bind_relation_parameters(
    descriptors: &[RelationDescriptor],
    challenges: &[RelationChallengeCircuit],
) -> Result<HashMap<String, Rec>, AirRelationParameterError> {
    if descriptors.len() != challenges.len() {
        return Err(AirRelationParameterError::ChallengeCountMismatch {
            expected: descriptors.len(),
            actual: challenges.len(),
        });
    }

    let mut parameters = HashMap::new();
    for (descriptor, challenge) in descriptors.iter().zip(challenges) {
        let words = challenge.words();
        let z = compose_secure(&words[..SECURE_EXTENSION_DEGREE]);
        let alpha = compose_secure(&words[SECURE_EXTENSION_DEGREE..]);
        insert_parameter(&mut parameters, format!("{}_z", descriptor.name), z)?;

        let mut alpha_power = Rec::one();
        for index in 0..descriptor.size {
            insert_parameter(
                &mut parameters,
                format!("{}_alpha{index}", descriptor.name),
                alpha_power.clone(),
            )?;
            alpha_power *= alpha.clone();
        }
    }
    Ok(parameters)
}

fn insert_parameter(
    parameters: &mut HashMap<String, Rec>,
    name: String,
    value: Rec,
) -> Result<(), AirRelationParameterError> {
    if parameters.insert(name.clone(), value).is_some() {
        return Err(AirRelationParameterError::DuplicateParameter { name });
    }
    Ok(())
}

fn compose_secure(words: &[Rec]) -> Rec {
    debug_assert_eq!(words.len(), SECURE_EXTENSION_DEGREE);
    words
        .iter()
        .enumerate()
        .fold(Rec::from(SecureField::default()), |value, (index, word)| {
            value + word.clone() * basis(index)
        })
}

fn basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        BaseField::from(u32::from(limb == index))
    }))
}

/// Invalid mapping between the trusted relation registry and transcript draws.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AirRelationParameterError {
    ChallengeCountMismatch { expected: usize, actual: usize },
    DuplicateParameter { name: String },
}

impl fmt::Display for AirRelationParameterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for AirRelationParameterError {}

#[cfg(test)]
mod tests {
    use stwo::core::fields::m31::M31;

    use super::*;
    use crate::recorder::CircuitBuilder;

    fn challenge(builder: &mut CircuitBuilder) -> RelationChallengeCircuit {
        RelationChallengeCircuit::new(core::array::from_fn(|index| {
            builder
                .input(SecureField::from(M31::from(index as u32 + 2)))
                .1
        }))
    }

    #[test]
    fn vm_registry_matches_the_relation_draw_order() {
        assert_eq!(
            prover::relations::Relations::DESCRIPTORS
                .iter()
                .map(|descriptor| (descriptor.name, descriptor.size))
                .collect::<Vec<_>>(),
            vec![
                ("registers_state", 2),
                ("memory_access", 7),
                ("program_access", 5),
                ("merkle", 18),
                ("poseidon2", 16),
                ("poseidon2_io", 32),
                ("bitwise", 4),
                ("range_check_20", 1),
                ("range_check_8_11", 2),
                ("range_check_8_8_4", 3),
                ("range_check_8_8", 2),
                ("range_check_m31", 2),
            ]
        );
    }

    #[test]
    fn raw_alpha_is_the_only_witness_for_all_formal_powers() {
        let descriptor = RelationDescriptor {
            name: "test_relation",
            size: 3,
        };
        let mut builder = CircuitBuilder::default();
        let challenge = challenge(&mut builder);
        let parameters = bind_relation_parameters(&[descriptor], &[challenge])
            .expect("one descriptor owns one complete challenge");
        let z =
            SecureField::from_m31_array([M31::from(2), M31::from(3), M31::from(4), M31::from(5)]);
        let alpha =
            SecureField::from_m31_array([M31::from(6), M31::from(7), M31::from(8), M31::from(9)]);
        assert_eq!(
            [
                parameters["test_relation_z"].value(),
                parameters["test_relation_alpha0"].value(),
                parameters["test_relation_alpha1"].value(),
                parameters["test_relation_alpha2"].value(),
            ],
            [z, SecureField::one(), alpha, alpha * alpha]
        );
    }

    #[test]
    fn relation_parameters_remain_connected_to_the_input_arena() {
        let descriptor = RelationDescriptor {
            name: "test_relation",
            size: 2,
        };
        let mut builder = CircuitBuilder::default();
        let challenge = challenge(&mut builder);
        let parameters = bind_relation_parameters(&[descriptor], &[challenge])
            .expect("one descriptor owns one complete challenge");
        assert!(matches!(
            parameters["test_relation_alpha1"],
            Rec::Node { .. }
        ));
    }

    #[test]
    fn missing_relation_draw_is_rejected() {
        let descriptor = RelationDescriptor {
            name: "test_relation",
            size: 1,
        };
        assert_eq!(
            bind_relation_parameters(&[descriptor], &[]),
            Err(AirRelationParameterError::ChallengeCountMismatch {
                expected: 1,
                actual: 0,
            })
        );
    }

    #[test]
    fn duplicate_registry_name_is_rejected() {
        let descriptor = RelationDescriptor {
            name: "test_relation",
            size: 1,
        };
        let mut builder = CircuitBuilder::default();
        let first = challenge(&mut builder);
        let second = challenge(&mut builder);
        assert_eq!(
            bind_relation_parameters(&[descriptor, descriptor], &[first, second]),
            Err(AirRelationParameterError::DuplicateParameter {
                name: "test_relation_z".into(),
            })
        );
    }
}
