//! Fixed recursion AIR composition circuit for child-proof verification.
//!
//! One graph evaluates all three universal proof-kind programs over shared
//! child inputs. Statement-bound one-hot selectors activate exactly one
//! equality, keeping the operation schedule independent of the child kind.

use core::fmt;

use air::digest::M31Word;
use num_traits::{One, Zero};
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};

use crate::air_relation_parameters::{
    AirRelationParameterError, RELATION_CHALLENGE_WORD_COUNT, RelationChallengeCircuit,
    bind_relation_parameters,
};
use crate::oods_circuit::{OodsCircuitError, oods_point_from_seed};
use crate::protocol::CanonicalTag;
use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};
use crate::recursion_air_program::{
    RecursionAirProgram, RecursionAirProgramError, UNIVERSAL_COMPONENT_COUNT,
    UniversalComponentLogSizes,
};
use crate::statement::{SPAN_STATEMENT_CANONICAL_WORDS, canonical_layout};
use crate::statement_input_air::PARENT_STATEMENT_SCOPE;
use crate::universal_relations::{UNIVERSAL_RELATION_COUNT, universal_relation_descriptors};
use crate::wire::ProofKind;

const SECURE_VALUE_WORD_COUNT: usize = SECURE_EXTENSION_DEGREE;

/// Verifier relation that owns one recursion-composition input word.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum RecursionAirCompositionInputSource {
    ParentBinarySelector,
    ChildKindSelector { kind: ProofKind },
    StatementWord { word_index: u32 },
    SampledValueWord { item_index: u32, word_index: u32 },
    ClaimedSumWord { item_index: u32, word_index: u32 },
    RelationChallengeWord { challenge: u32, word_index: u32 },
    CompositionRandomnessWord { word_index: u32 },
    OodsPointWord { word_index: u32 },
}

/// Circuit node and the verifier source that supplies it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursionAirCompositionInputBinding {
    pub node_id: u32,
    pub source: RecursionAirCompositionInputSource,
}

/// Fixed child-composition circuit and its verifier-owned inputs.
#[derive(Debug)]
pub struct RecursionAirCompositionCircuit {
    circuit: ConstraintCircuit,
    input_bindings: Vec<RecursionAirCompositionInputBinding>,
}

impl RecursionAirCompositionCircuit {
    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[RecursionAirCompositionInputBinding] {
        &self.input_bindings
    }

    pub fn nonzero_output_count(&self) -> usize {
        self.circuit
            .outputs()
            .iter()
            .filter(|output| !self.circuit.arena().nodes[**output].value.is_zero())
            .count()
    }
}

/// Values for one recursion child AIR-composition check.
pub struct RecursionAirCompositionWitness<'a> {
    pub parent_binary_selector: bool,
    pub child_kind: ProofKind,
    pub statement_words: &'a [M31Word; SPAN_STATEMENT_CANONICAL_WORDS],
    pub sampled_values: &'a [SecureField],
    pub claimed_sums: &'a [SecureField],
    pub relation_challenges: &'a [[M31Word; RELATION_CHALLENGE_WORD_COUNT]],
    pub composition_randomness: [M31Word; SECURE_VALUE_WORD_COUNT],
    pub oods_point: [M31Word; SECURE_VALUE_WORD_COUNT],
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<RecursionAirCompositionInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: RecursionAirCompositionInputSource, value: M31Word) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value.as_u32())));
        self.bindings.push(RecursionAirCompositionInputBinding {
            node_id: u32::try_from(node_id).expect("recursion composition inputs fit u32"),
            source,
        });
        value
    }

    fn secure_input(
        &mut self,
        value: SecureField,
        source: impl Fn(u32) -> RecursionAirCompositionInputSource,
    ) -> Rec {
        let words = value.to_m31_array().map(M31Word::from);
        compose_secure(core::array::from_fn(|index| {
            self.input(
                source(u32::try_from(index).expect("secure-field word index fits u32")),
                words[index],
            )
        }))
    }

    fn secure_words(
        &mut self,
        words: [M31Word; SECURE_VALUE_WORD_COUNT],
        source: impl Fn(u32) -> RecursionAirCompositionInputSource,
    ) -> Rec {
        compose_secure(core::array::from_fn(|index| {
            self.input(
                source(u32::try_from(index).expect("secure-field word index fits u32")),
                words[index],
            )
        }))
    }

    fn constrain(&mut self, active: &Rec, value: Rec) {
        self.circuit.constrain_zero(active.clone() * value);
    }

    fn finish(self) -> RecursionAirCompositionCircuit {
        RecursionAirCompositionCircuit {
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

/// Builds the inactive fixed graph used to derive preprocessing and schedules.
pub fn build_recursion_air_composition_reference(
    component_log_sizes: UniversalComponentLogSizes,
    preprocessed_ids: &[stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId],
) -> Result<RecursionAirCompositionCircuit, RecursionAirCompositionCircuitError> {
    let programs = build_programs(component_log_sizes, preprocessed_ids)?;
    let sampled_values = vec![SecureField::zero(); programs[0].sample_coordinates().len()];
    let claimed_sums = vec![SecureField::zero(); UNIVERSAL_COMPONENT_COUNT];
    let relation_challenges =
        vec![[M31Word::ZERO; RELATION_CHALLENGE_WORD_COUNT]; UNIVERSAL_RELATION_COUNT];
    build_with_programs(
        &programs,
        RecursionAirCompositionWitness {
            parent_binary_selector: false,
            child_kind: ProofKind::EmptyLeaf,
            statement_words: &[M31Word::ZERO; SPAN_STATEMENT_CANONICAL_WORDS],
            sampled_values: &sampled_values,
            claimed_sums: &claimed_sums,
            relation_challenges: &relation_challenges,
            composition_randomness: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
            oods_point: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
        },
    )
}

/// Builds one active child-composition circuit from proof and transcript data.
pub fn build_recursion_air_composition_circuit(
    component_log_sizes: UniversalComponentLogSizes,
    preprocessed_ids: &[stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId],
    witness: RecursionAirCompositionWitness<'_>,
) -> Result<RecursionAirCompositionCircuit, RecursionAirCompositionCircuitError> {
    let programs = build_programs(component_log_sizes, preprocessed_ids)?;
    build_with_programs(&programs, witness)
}

fn build_programs(
    component_log_sizes: UniversalComponentLogSizes,
    preprocessed_ids: &[stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId],
) -> Result<[RecursionAirProgram; 3], RecursionAirCompositionCircuitError> {
    Ok([
        RecursionAirProgram::new_with_kind(
            component_log_sizes,
            preprocessed_ids,
            ProofKind::SegmentLeaf,
        )?,
        RecursionAirProgram::new_with_kind(
            component_log_sizes,
            preprocessed_ids,
            ProofKind::BinaryNode,
        )?,
        RecursionAirProgram::new_with_kind(
            component_log_sizes,
            preprocessed_ids,
            ProofKind::EmptyLeaf,
        )?,
    ])
}

fn build_with_programs(
    programs: &[RecursionAirProgram; 3],
    witness: RecursionAirCompositionWitness<'_>,
) -> Result<RecursionAirCompositionCircuit, RecursionAirCompositionCircuitError> {
    let sample_count = programs[0].sample_coordinates().len();
    if programs
        .iter()
        .any(|program| program.sample_coordinates().len() != sample_count)
    {
        return Err(RecursionAirCompositionCircuitError::ProgramGeometryMismatch);
    }
    if witness.sampled_values.len() != sample_count {
        return Err(
            RecursionAirCompositionCircuitError::SampledValueCountMismatch {
                expected: sample_count,
                actual: witness.sampled_values.len(),
            },
        );
    }
    if witness.claimed_sums.len() != UNIVERSAL_COMPONENT_COUNT {
        return Err(
            RecursionAirCompositionCircuitError::ClaimedSumCountMismatch {
                expected: UNIVERSAL_COMPONENT_COUNT,
                actual: witness.claimed_sums.len(),
            },
        );
    }
    if witness.relation_challenges.len() != UNIVERSAL_RELATION_COUNT {
        return Err(
            RecursionAirCompositionCircuitError::RelationChallengeCountMismatch {
                expected: UNIVERSAL_RELATION_COUNT,
                actual: witness.relation_challenges.len(),
            },
        );
    }

    let mut builder = TrackedBuilder::new();
    let active = builder.input(
        RecursionAirCompositionInputSource::ParentBinarySelector,
        M31Word::from(u16::from(witness.parent_binary_selector)),
    );
    let selectors = [
        ProofKind::SegmentLeaf,
        ProofKind::BinaryNode,
        ProofKind::EmptyLeaf,
    ]
    .map(|kind| {
        builder.input(
            RecursionAirCompositionInputSource::ChildKindSelector { kind },
            M31Word::from(u16::from(
                witness.parent_binary_selector && witness.child_kind == kind,
            )),
        )
    });
    let statement_words = core::array::from_fn(|index| {
        builder.input(
            RecursionAirCompositionInputSource::StatementWord {
                word_index: u32::try_from(index).expect("statement word index fits u32"),
            },
            witness.statement_words[index],
        )
    });
    bind_child_kind(&mut builder, &active, &selectors, &statement_words);

    let sampled_values = witness
        .sampled_values
        .iter()
        .copied()
        .enumerate()
        .map(|(item_index, value)| {
            builder.secure_input(value, |word_index| {
                RecursionAirCompositionInputSource::SampledValueWord {
                    item_index: u32::try_from(item_index).expect("sampled-value index fits u32"),
                    word_index,
                }
            })
        })
        .collect::<Vec<_>>();
    let claimed_sums = witness
        .claimed_sums
        .iter()
        .copied()
        .enumerate()
        .map(|(item_index, value)| {
            builder.secure_input(value, |word_index| {
                RecursionAirCompositionInputSource::ClaimedSumWord {
                    item_index: u32::try_from(item_index).expect("claimed-sum index fits u32"),
                    word_index,
                }
            })
        })
        .collect::<Vec<_>>();
    let relation_challenges = witness
        .relation_challenges
        .iter()
        .enumerate()
        .map(|(challenge, words)| {
            RelationChallengeCircuit::new(core::array::from_fn(|word_index| {
                builder.input(
                    RecursionAirCompositionInputSource::RelationChallengeWord {
                        challenge: u32::try_from(challenge).expect("challenge index fits u32"),
                        word_index: u32::try_from(word_index).expect("challenge word fits u32"),
                    },
                    words[word_index],
                )
            }))
        })
        .collect::<Vec<_>>();
    let relation_parameters =
        bind_relation_parameters(&universal_relation_descriptors(), &relation_challenges)?;
    constrain_global_logup(
        &mut builder,
        &active,
        &statement_words,
        &claimed_sums,
        &relation_parameters,
    );
    let composition_randomness = builder
        .secure_words(witness.composition_randomness, |word_index| {
            RecursionAirCompositionInputSource::CompositionRandomnessWord { word_index }
        });
    let oods_seed = builder.secure_words(witness.oods_point, |word_index| {
        RecursionAirCompositionInputSource::OodsPointWord { word_index }
    });
    let oods_point = oods_point_from_seed(oods_seed)?;

    for ((program, selector), kind) in programs.iter().zip(selectors).zip([
        ProofKind::SegmentLeaf,
        ProofKind::BinaryNode,
        ProofKind::EmptyLeaf,
    ]) {
        debug_assert_eq!(kind, witness_kind_for_program(kind));
        let evaluation = program.evaluate(
            &sampled_values,
            &claimed_sums,
            &relation_parameters,
            composition_randomness.clone(),
            &oods_point,
        )?;
        builder
            .circuit
            .constrain_zero(active.clone() * selector * evaluation.equality);
    }
    Ok(builder.finish())
}

fn constrain_global_logup(
    builder: &mut TrackedBuilder,
    active: &Rec,
    statement_words: &[Rec; SPAN_STATEMENT_CANONICAL_WORDS],
    claimed_sums: &[Rec],
    relation_parameters: &std::collections::HashMap<String, Rec>,
) {
    let z = relation_parameters["StatementWordRelation_z"].clone();
    let alphas = core::array::from_fn::<_, 3, _>(|index| {
        relation_parameters[&format!("StatementWordRelation_alpha{index}")].clone()
    });
    let scope = Rec::from(BaseField::from(PARENT_STATEMENT_SCOPE));
    let public_sum = statement_words
        .iter()
        .enumerate()
        .fold(Rec::zero(), |sum, (index, word)| {
            let denominator = scope.clone() * alphas[0].clone()
                + Rec::from(BaseField::from(
                    u32::try_from(index).expect("statement word index fits u32"),
                )) * alphas[1].clone()
                + word.clone() * alphas[2].clone()
                - z.clone();
            sum + denominator.inverse()
        });
    let claimed_sum = claimed_sums
        .iter()
        .cloned()
        .fold(Rec::zero(), |sum, value| sum + value);
    // A composition equality alone does not prove that all LogUp relations
    // close; the child is accepted only when its verifier-owned public terms
    // cancel every component interaction claim.
    builder.constrain(active, claimed_sum + public_sum);
}

fn bind_child_kind(
    builder: &mut TrackedBuilder,
    active: &Rec,
    selectors: &[Rec; 3],
    statement: &[Rec; SPAN_STATEMENT_CANONICAL_WORDS],
) {
    let [segment, binary, empty] = selectors;
    let one = Rec::one();
    builder.constrain(
        active,
        segment.clone() + binary.clone() + empty.clone() - one.clone(),
    );
    for selector in selectors {
        builder.constrain(active, selector.clone() * (one.clone() - selector.clone()));
    }
    let height = statement[canonical_layout::SLOT_HEIGHT].clone();
    builder.constrain(active, (segment.clone() + empty.clone()) * height.clone());
    let safe_height = height.clone() + one.clone() - binary.clone();
    let height_inverse = safe_height.inverse();
    builder.constrain(active, safe_height * height_inverse.clone() - one.clone());
    builder.constrain(active, height * height_inverse - binary.clone());
    let body_tag = statement[canonical_layout::BODY_TAG].clone();
    builder.constrain(
        active,
        segment.clone()
            * (body_tag.clone()
                - Rec::from(BaseField::from(CanonicalTag::ExecutedBody.word().as_u32()))),
    );
    builder.constrain(
        active,
        empty.clone()
            * (body_tag - Rec::from(BaseField::from(CanonicalTag::EmptyBody.word().as_u32()))),
    );
}

const fn witness_kind_for_program(kind: ProofKind) -> ProofKind {
    kind
}

fn compose_secure(values: [Rec; SECURE_VALUE_WORD_COUNT]) -> Rec {
    values
        .into_iter()
        .enumerate()
        .fold(Rec::zero(), |value, (index, word)| {
            value
                + word
                    * SecureField::from_m31_array(core::array::from_fn(|limb| {
                        BaseField::from(u32::from(limb == index))
                    }))
        })
}

/// Invalid child-composition profile, input assignment, or AIR evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionAirCompositionCircuitError {
    Program(RecursionAirProgramError),
    Relation(AirRelationParameterError),
    Oods(OodsCircuitError),
    ProgramGeometryMismatch,
    SampledValueCountMismatch { expected: usize, actual: usize },
    ClaimedSumCountMismatch { expected: usize, actual: usize },
    RelationChallengeCountMismatch { expected: usize, actual: usize },
}

impl fmt::Display for RecursionAirCompositionCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for RecursionAirCompositionCircuitError {}

impl From<RecursionAirProgramError> for RecursionAirCompositionCircuitError {
    fn from(error: RecursionAirProgramError) -> Self {
        Self::Program(error)
    }
}

impl From<AirRelationParameterError> for RecursionAirCompositionCircuitError {
    fn from(error: AirRelationParameterError) -> Self {
        Self::Relation(error)
    }
}

impl From<OodsCircuitError> for RecursionAirCompositionCircuitError {
    fn from(error: OodsCircuitError) -> Self {
        Self::Oods(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{CircuitTraces, lower_arena_operations};
    use crate::profile::{recursion_component_log_sizes, recursion_preprocessed_column_ids};

    #[test]
    fn combined_child_kind_graph_has_a_fixed_measured_shape() {
        let reference = build_recursion_air_composition_reference(
            recursion_component_log_sizes(),
            &recursion_preprocessed_column_ids(),
        )
        .expect("recursion composition reference builds");
        let mut traces = CircuitTraces::default();
        lower_arena_operations(
            &mut traces,
            1,
            &reference.circuit().arena(),
            reference.circuit().outputs(),
        );
        let log_size = |rows: usize| rows.max(1).next_power_of_two().ilog2().max(4);
        assert_eq!(
            [
                log_size(traces.qm31_mul.len()),
                log_size(traces.qm31_inv.len()),
                log_size(traces.linear_ops.len()),
            ],
            [15, 9, 15]
        );
    }
}
