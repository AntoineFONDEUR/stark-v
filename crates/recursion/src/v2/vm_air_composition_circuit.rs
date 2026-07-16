//! Fixed VM AIR composition circuit for recursion V2 segment verification.
//!
//! Every proof value and Fiat-Shamir word enters through a tracked base-field
//! input. The fixed VM program reconstructs secure values, evaluates all AIR
//! constraints and LogUp terms, and compares the result with the proof's split
//! composition sample. A segment selector gates the sole zero output so the
//! same circuit structure is present, with zero inputs, in non-segment modes.

use core::fmt;

use air::digest::M31Word;
use num_traits::Zero;
use prover::relations::Relations;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};

use super::air_relation_parameters::{
    AirRelationParameterError, RELATION_CHALLENGE_WORD_COUNT, RelationChallengeCircuit,
    bind_relation_parameters,
};
use super::oods_circuit::{OodsCircuitError, oods_point_from_seed};
use super::vm_air_program::{VM_AIR_COMPONENT_COUNT, VmAirProgram, VmAirProgramError};
use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

/// Base-field words in one secure-field verifier value.
pub const SECURE_VALUE_WORD_COUNT: usize = SECURE_EXTENSION_DEGREE;

/// Exact verifier relation that owns one composition-circuit input.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum VmAirCompositionInputSource {
    SampledValueWord { item_index: u32, word_index: u32 },
    ClaimedSumWord { item_index: u32, word_index: u32 },
    RelationChallengeWord { challenge: u32, word_index: u32 },
    CompositionRandomnessWord { word_index: u32 },
    OodsPointWord { word_index: u32 },
    SegmentSelector,
}

/// Circuit node and the exact verifier relation that supplies its value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmAirCompositionInputBinding {
    pub node_id: u32,
    pub source: VmAirCompositionInputSource,
}

/// Fixed dimensions tied to one compiled VM AIR profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmAirCompositionProfile {
    component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
    sampled_value_count: u32,
    claimed_sum_count: u32,
    relation_challenge_count: u32,
    air_instruction_count: u32,
}

impl VmAirCompositionProfile {
    pub const fn component_log_sizes(&self) -> [u32; VM_AIR_COMPONENT_COUNT] {
        self.component_log_sizes
    }

    pub const fn sampled_value_count(&self) -> u32 {
        self.sampled_value_count
    }

    pub const fn claimed_sum_count(&self) -> u32 {
        self.claimed_sum_count
    }

    pub const fn relation_challenge_count(&self) -> u32 {
        self.relation_challenge_count
    }

    pub const fn air_instruction_count(&self) -> u32 {
        self.air_instruction_count
    }
}

/// Fixed composition circuit and all verifier-owned input coordinates.
#[derive(Debug)]
pub struct VmAirCompositionCircuit {
    profile: VmAirCompositionProfile,
    circuit: ConstraintCircuit,
    input_bindings: Vec<VmAirCompositionInputBinding>,
}

impl VmAirCompositionCircuit {
    pub const fn profile(&self) -> VmAirCompositionProfile {
        self.profile
    }

    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub fn input_bindings(&self) -> &[VmAirCompositionInputBinding] {
        &self.input_bindings
    }

    pub fn constrained_equality(&self) -> SecureField {
        let output = *self
            .circuit
            .outputs()
            .first()
            .expect("VM AIR composition circuit has one output");
        self.circuit.arena().nodes[output].value
    }

    pub fn nonzero_output_count(&self) -> usize {
        usize::from(!self.constrained_equality().is_zero())
    }
}

/// Values for one universal VM AIR composition circuit instance.
pub struct VmAirCompositionWitness<'a> {
    pub segment_selector: bool,
    pub sampled_values: &'a [SecureField],
    pub claimed_sums: &'a [SecureField],
    pub relation_challenges: &'a [[M31Word; RELATION_CHALLENGE_WORD_COUNT]],
    pub composition_randomness: [M31Word; SECURE_VALUE_WORD_COUNT],
    pub oods_point: [M31Word; SECURE_VALUE_WORD_COUNT],
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<VmAirCompositionInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: VmAirCompositionInputSource, value: M31Word) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value.as_u32())));
        self.bindings.push(VmAirCompositionInputBinding {
            node_id: u32::try_from(node_id).expect("VM composition input count fits u32"),
            source,
        });
        value
    }

    fn secure_input(
        &mut self,
        value: SecureField,
        source: impl Fn(u32) -> VmAirCompositionInputSource,
    ) -> Rec {
        let words = value.to_m31_array().map(M31Word::from);
        let values = core::array::from_fn(|index| {
            let word_index = u32::try_from(index).expect("secure-field word index fits u32");
            self.input(source(word_index), words[index])
        });
        compose_secure(values)
    }

    fn secure_words(
        &mut self,
        words: [M31Word; SECURE_VALUE_WORD_COUNT],
        source: impl Fn(u32) -> VmAirCompositionInputSource,
    ) -> Rec {
        let values = core::array::from_fn(|index| {
            let word_index = u32::try_from(index).expect("secure-field word index fits u32");
            self.input(source(word_index), words[index])
        });
        compose_secure(values)
    }

    fn finish(self, profile: VmAirCompositionProfile) -> VmAirCompositionCircuit {
        VmAirCompositionCircuit {
            profile,
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

/// Builds the zero-input inactive circuit that fixes preprocessing structure.
pub fn build_vm_air_composition_reference(
    component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
) -> Result<VmAirCompositionCircuit, VmAirCompositionCircuitError> {
    let program = VmAirProgram::new(component_log_sizes)?;
    let sampled_values = vec![SecureField::zero(); program.sample_coordinates().len()];
    let claimed_sums = vec![SecureField::zero(); VM_AIR_COMPONENT_COUNT];
    let relation_challenges =
        vec![[M31Word::ZERO; RELATION_CHALLENGE_WORD_COUNT]; Relations::DESCRIPTORS.len()];
    build_with_program(
        component_log_sizes,
        &program,
        VmAirCompositionWitness {
            segment_selector: false,
            sampled_values: &sampled_values,
            claimed_sums: &claimed_sums,
            relation_challenges: &relation_challenges,
            composition_randomness: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
            oods_point: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
        },
    )
}

/// Builds one composition circuit from proof and transcript-bound values.
pub fn build_vm_air_composition_circuit(
    component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
    witness: VmAirCompositionWitness<'_>,
) -> Result<VmAirCompositionCircuit, VmAirCompositionCircuitError> {
    let program = VmAirProgram::new(component_log_sizes)?;
    build_with_program(component_log_sizes, &program, witness)
}

fn build_with_program(
    component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
    program: &VmAirProgram,
    witness: VmAirCompositionWitness<'_>,
) -> Result<VmAirCompositionCircuit, VmAirCompositionCircuitError> {
    let sampled_value_count = checked_count("sampled values", program.sample_coordinates().len())?;
    if witness.sampled_values.len() != program.sample_coordinates().len() {
        return Err(VmAirCompositionCircuitError::SampledValueCountMismatch {
            expected: program.sample_coordinates().len(),
            actual: witness.sampled_values.len(),
        });
    }
    if witness.claimed_sums.len() != VM_AIR_COMPONENT_COUNT {
        return Err(VmAirCompositionCircuitError::ClaimedSumCountMismatch {
            expected: VM_AIR_COMPONENT_COUNT,
            actual: witness.claimed_sums.len(),
        });
    }
    if witness.relation_challenges.len() != Relations::DESCRIPTORS.len() {
        return Err(
            VmAirCompositionCircuitError::RelationChallengeCountMismatch {
                expected: Relations::DESCRIPTORS.len(),
                actual: witness.relation_challenges.len(),
            },
        );
    }
    let profile = VmAirCompositionProfile {
        component_log_sizes,
        sampled_value_count,
        claimed_sum_count: checked_count("claimed sums", VM_AIR_COMPONENT_COUNT)?,
        relation_challenge_count: checked_count(
            "relation challenges",
            Relations::DESCRIPTORS.len(),
        )?,
        air_instruction_count: checked_count("AIR instructions", program.air_instruction_count())?,
    };

    let mut builder = TrackedBuilder::new();
    let segment = builder.input(
        VmAirCompositionInputSource::SegmentSelector,
        M31Word::from(u16::from(witness.segment_selector)),
    );
    let sampled_values = witness
        .sampled_values
        .iter()
        .copied()
        .enumerate()
        .map(|(item_index, value)| {
            let item_index =
                u32::try_from(item_index).expect("validated sampled-value count fits u32");
            builder.secure_input(value, |word_index| {
                VmAirCompositionInputSource::SampledValueWord {
                    item_index,
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
            let item_index =
                u32::try_from(item_index).expect("validated claimed-sum count fits u32");
            builder.secure_input(value, |word_index| {
                VmAirCompositionInputSource::ClaimedSumWord {
                    item_index,
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
            let challenge =
                u32::try_from(challenge).expect("validated relation challenge count fits u32");
            RelationChallengeCircuit::new(core::array::from_fn(|word_index| {
                builder.input(
                    VmAirCompositionInputSource::RelationChallengeWord {
                        challenge,
                        word_index: u32::try_from(word_index)
                            .expect("relation challenge word index fits u32"),
                    },
                    words[word_index],
                )
            }))
        })
        .collect::<Vec<_>>();
    let relation_parameters =
        bind_relation_parameters(&Relations::DESCRIPTORS, &relation_challenges)?;
    let composition_randomness = builder
        .secure_words(witness.composition_randomness, |word_index| {
            VmAirCompositionInputSource::CompositionRandomnessWord { word_index }
        });
    let oods_seed = builder.secure_words(witness.oods_point, |word_index| {
        VmAirCompositionInputSource::OodsPointWord { word_index }
    });
    let oods_point = oods_point_from_seed(oods_seed)?;
    let evaluation = program.evaluate(
        &sampled_values,
        &claimed_sums,
        &relation_parameters,
        composition_randomness,
        &oods_point,
    )?;
    builder
        .circuit
        .constrain_zero(segment * evaluation.equality);
    Ok(builder.finish(profile))
}

fn checked_count(field: &'static str, value: usize) -> Result<u32, VmAirCompositionCircuitError> {
    let value_u32 = u32::try_from(value)
        .map_err(|_| VmAirCompositionCircuitError::CountOutOfRange { field, value })?;
    M31Word::try_from(value_u32)
        .map(M31Word::as_u32)
        .map_err(|_| VmAirCompositionCircuitError::CountOutOfRange { field, value })
}

fn compose_secure(values: [Rec; SECURE_VALUE_WORD_COUNT]) -> Rec {
    values
        .into_iter()
        .enumerate()
        .fold(Rec::zero(), |value, (index, word)| {
            value + word * secure_basis(index)
        })
}

fn secure_basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        BaseField::from(u32::from(limb == index))
    }))
}

/// Invalid VM AIR profile, circuit input assignment, or OODS evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmAirCompositionCircuitError {
    SampledValueCountMismatch { expected: usize, actual: usize },
    ClaimedSumCountMismatch { expected: usize, actual: usize },
    RelationChallengeCountMismatch { expected: usize, actual: usize },
    CountOutOfRange { field: &'static str, value: usize },
    Program(VmAirProgramError),
    RelationParameters(AirRelationParameterError),
    Oods(OodsCircuitError),
}

impl From<VmAirProgramError> for VmAirCompositionCircuitError {
    fn from(value: VmAirProgramError) -> Self {
        Self::Program(value)
    }
}

impl From<AirRelationParameterError> for VmAirCompositionCircuitError {
    fn from(value: AirRelationParameterError) -> Self {
        Self::RelationParameters(value)
    }
}

impl From<OodsCircuitError> for VmAirCompositionCircuitError {
    fn from(value: OodsCircuitError) -> Self {
        Self::Oods(value)
    }
}

impl fmt::Display for VmAirCompositionCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirCompositionCircuitError {}

#[cfg(test)]
mod tests {
    use super::*;
    use prover::components::COMPONENT_NAMES;
    use stwo::core::fields::m31::M31;

    fn component_log_sizes() -> [u32; VM_AIR_COMPONENT_COUNT] {
        core::array::from_fn(|index| match COMPONENT_NAMES[index] {
            "bitwise" => 18,
            "range_check_20" | "range_check_8_8_4" => 20,
            "range_check_8_11" => 19,
            "range_check_8_8" => 16,
            "range_check_m31" => 15,
            _ => 6,
        })
    }

    struct ActiveFixture {
        samples: Vec<SecureField>,
        claimed_sums: Vec<SecureField>,
        challenges: Vec<[M31Word; RELATION_CHALLENGE_WORD_COUNT]>,
        composition_randomness: [M31Word; SECURE_VALUE_WORD_COUNT],
        oods_point: [M31Word; SECURE_VALUE_WORD_COUNT],
    }

    fn active_fixture() -> ActiveFixture {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let mut samples = vec![SecureField::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![SecureField::zero(); VM_AIR_COMPONENT_COUNT];
        let challenges = Relations::DESCRIPTORS
            .iter()
            .enumerate()
            .map(|(challenge, _)| {
                core::array::from_fn(|word| {
                    M31Word::from(
                        u16::try_from(2 + challenge * RELATION_CHALLENGE_WORD_COUNT + word)
                            .expect("fixture relation word fits u16"),
                    )
                })
            })
            .collect::<Vec<_>>();
        let relation_circuits = challenges
            .iter()
            .map(|words| {
                RelationChallengeCircuit::new(
                    words.map(|word| Rec::from(BaseField::from(word.as_u32()))),
                )
            })
            .collect::<Vec<_>>();
        let parameters = bind_relation_parameters(&Relations::DESCRIPTORS, &relation_circuits)
            .expect("fixture supplies every relation draw");
        let composition_randomness = [2_u16, 3, 5, 7].map(M31Word::from);
        let composition_randomness_value = SecureField::from_m31_array(
            composition_randomness.map(|word| M31::from(word.as_u32())),
        );
        let oods_words = [11_u16, 13, 17, 19].map(M31Word::from);
        let oods_seed =
            SecureField::from_m31_array(oods_words.map(|word| M31::from(word.as_u32())));
        let oods_point = oods_point_from_seed(Rec::from(oods_seed))
            .expect("fixture OODS seed maps outside the composition coset");
        let evaluation = program
            .evaluate(
                &samples.iter().copied().map(Rec::from).collect::<Vec<_>>(),
                &claimed_sums
                    .iter()
                    .copied()
                    .map(Rec::from)
                    .collect::<Vec<_>>(),
                &parameters,
                Rec::from(composition_randomness_value),
                &oods_point,
            )
            .expect("complete fixture evaluates");
        let composition_tree = program
            .sample_coordinates()
            .iter()
            .map(|coordinate| coordinate.tree)
            .max()
            .expect("VM program samples its composition tree");
        let first_left_coordinate = program
            .sample_coordinates()
            .iter()
            .position(|coordinate| {
                coordinate.tree == composition_tree
                    && coordinate.column == 0
                    && coordinate.point == 0
            })
            .expect("split composition has a first left coordinate");
        samples[first_left_coordinate] = evaluation.air_value.value();
        ActiveFixture {
            samples,
            claimed_sums,
            challenges,
            composition_randomness,
            oods_point: oods_words,
        }
    }

    #[test]
    fn inactive_reference_has_one_zero_output() {
        let circuit = build_vm_air_composition_reference(component_log_sizes())
            .expect("zero OODS inputs are outside the composition coset");
        assert_eq!(
            (
                circuit.circuit().outputs().len(),
                circuit.nonzero_output_count()
            ),
            (1, 0)
        );
    }

    #[test]
    fn fixed_profile_is_derived_from_the_compiled_program() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let circuit = build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture reference is constructible");
        assert_eq!(
            (
                circuit.profile().sampled_value_count(),
                circuit.profile().claimed_sum_count(),
                circuit.profile().relation_challenge_count(),
                circuit.profile().air_instruction_count(),
            ),
            (
                u32::try_from(program.sample_coordinates().len()).unwrap(),
                u32::try_from(VM_AIR_COMPONENT_COUNT).unwrap(),
                u32::try_from(Relations::DESCRIPTORS.len()).unwrap(),
                u32::try_from(program.air_instruction_count()).unwrap(),
            )
        );
    }

    #[test]
    fn every_secure_source_owns_exactly_four_input_words() {
        let circuit = build_vm_air_composition_reference(component_log_sizes())
            .expect("fixture reference is constructible");
        let counts = circuit
            .input_bindings()
            .iter()
            .fold([0_usize; 6], |mut counts, binding| {
                let index = match binding.source {
                    VmAirCompositionInputSource::SampledValueWord { .. } => 0,
                    VmAirCompositionInputSource::ClaimedSumWord { .. } => 1,
                    VmAirCompositionInputSource::RelationChallengeWord { .. } => 2,
                    VmAirCompositionInputSource::CompositionRandomnessWord { .. } => 3,
                    VmAirCompositionInputSource::OodsPointWord { .. } => 4,
                    VmAirCompositionInputSource::SegmentSelector => 5,
                };
                counts[index] += 1;
                counts
            });
        assert_eq!(
            counts,
            [
                circuit.profile().sampled_value_count() as usize * SECURE_VALUE_WORD_COUNT,
                VM_AIR_COMPONENT_COUNT * SECURE_VALUE_WORD_COUNT,
                Relations::DESCRIPTORS.len() * RELATION_CHALLENGE_WORD_COUNT,
                SECURE_VALUE_WORD_COUNT,
                SECURE_VALUE_WORD_COUNT,
                1,
            ]
        );
    }

    #[test]
    fn truncated_sample_assignment_is_rejected_before_input_tracking() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let samples = vec![SecureField::zero(); program.sample_coordinates().len() - 1];
        let claimed_sums = vec![SecureField::zero(); VM_AIR_COMPONENT_COUNT];
        let challenges =
            vec![[M31Word::ZERO; RELATION_CHALLENGE_WORD_COUNT]; Relations::DESCRIPTORS.len()];
        let result = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: true,
                sampled_values: &samples,
                claimed_sums: &claimed_sums,
                relation_challenges: &challenges,
                composition_randomness: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
                oods_point: [M31Word::ZERO; SECURE_VALUE_WORD_COUNT],
            },
        );
        assert!(matches!(
            result,
            Err(VmAirCompositionCircuitError::SampledValueCountMismatch {
                expected,
                actual,
            }) if expected == program.sample_coordinates().len() && actual == samples.len()
        ));
    }

    #[test]
    fn active_fixture_constrains_the_exact_composition_equality() {
        let fixture = active_fixture();
        let circuit = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: true,
                sampled_values: &fixture.samples,
                claimed_sums: &fixture.claimed_sums,
                relation_challenges: &fixture.challenges,
                composition_randomness: fixture.composition_randomness,
                oods_point: fixture.oods_point,
            },
        )
        .expect("valid active composition is constructible");
        assert_eq!(circuit.nonzero_output_count(), 0);
    }

    #[test]
    fn changed_composition_sample_keeps_the_output_nonzero() {
        let mut fixture = active_fixture();
        let last = fixture
            .samples
            .last_mut()
            .expect("VM composition fixture has sampled values");
        *last += SecureField::from(BaseField::from(1));
        let circuit = build_vm_air_composition_circuit(
            component_log_sizes(),
            VmAirCompositionWitness {
                segment_selector: true,
                sampled_values: &fixture.samples,
                claimed_sums: &fixture.claimed_sums,
                relation_challenges: &fixture.challenges,
                composition_randomness: fixture.composition_randomness,
                oods_point: fixture.oods_point,
            },
        )
        .expect("tampered assignment still has the fixed structure");
        assert_eq!(circuit.nonzero_output_count(), 1);
    }
}
