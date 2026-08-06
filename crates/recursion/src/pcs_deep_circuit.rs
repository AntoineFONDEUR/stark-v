//! Fixed STWO DEEP-quotient arithmetic for recursion.
//!
//! The profile derives every sample point from the generated AIR mask, adds
//! STWO's two-sample periodicity terms in native random-power order, and groups
//! equal points stably. The circuit reconstructs each bit-reversed lifting-
//! domain query point, evaluates the conjugate-line quotients, and equates the
//! result with the value that starts FRI. Every proof value remains a tracked
//! input so a separate ownership AIR can bind it to transcript and Merkle data.

use core::fmt;

use air::digest::M31Word;
use num_traits::{One, Zero};
use stwo::core::circle::{CirclePointIndex, M31_CIRCLE_LOG_ORDER};
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::fields::{ComplexConjugate, FieldExpOps};
use stwo::core::poly::circle::{CanonicCoset, MAX_CIRCLE_DOMAIN_LOG_SIZE};

use super::oods_circuit::{OodsCircuitError, OodsPointCircuit, oods_point_from_seed};
use super::protocol::{FixedProofShape, ProofShapeError, ValidatedPcsParameters};
use super::vm_air_program::{Poseidon2AirProgram, SampleCoordinate, VmAirProgram};
use super::vm_pcs_layout::VmPcsLayout;
use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

const M31_BITS: usize = M31_CIRCLE_LOG_ORDER as usize;
// Inactive lanes still instantiate every inverse. This fixed off-domain seed
// keeps those denominators defined while all verifier-owned inputs remain zero.
const SAFE_OODS_WORDS: [u32; SECURE_EXTENSION_DEGREE] = [17, 29, 43, 71];

/// One verifier-owned input of the fixed DEEP circuit.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum PcsDeepInputSource {
    ActiveSelector,
    SampledValueWord { sample: u32, word: u32 },
    QueriedValue { tree: u32, column: u32, query: u32 },
    OodsSeedWord { word: u32 },
    DeepRandomnessWord { word: u32 },
    QueryBit { query: u32, bit: u32 },
    QueryPosition { query: u32 },
    AnswerWord { query: u32, word: u32 },
}

/// Circuit node and the exact verifier relation that supplies it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PcsDeepInputBinding {
    pub node_id: u32,
    pub source: PcsDeepInputSource,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SampleTerm {
    column: usize,
    sample: usize,
    random_power: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SampleBatch {
    point_offset: CirclePointIndex,
    terms: Vec<SampleTerm>,
}

/// Trusted column, sample-point, and query geometry for one PCS verifier lane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsDeepProfile {
    column_log_sizes: Vec<Vec<u32>>,
    sample_point_offsets: Vec<Vec<Vec<CirclePointIndex>>>,
    batches: Vec<SampleBatch>,
    sample_count: usize,
    column_count: usize,
    term_count: usize,
    lifting_log_size: u32,
    query_count: usize,
}

impl PcsDeepProfile {
    /// Validates a generic tree-major PCS sample layout.
    pub fn new(
        column_log_sizes: Vec<Vec<u32>>,
        sample_point_offsets: Vec<Vec<Vec<CirclePointIndex>>>,
        lifting_log_size: u32,
        query_count: usize,
    ) -> Result<Self, PcsDeepCircuitError> {
        if !(1..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&lifting_log_size) {
            return Err(PcsDeepCircuitError::LiftingLogSizeOutOfRange { lifting_log_size });
        }
        if query_count == 0 {
            return Err(PcsDeepCircuitError::ZeroQueries);
        }
        if column_log_sizes.len() != sample_point_offsets.len() {
            return Err(PcsDeepCircuitError::TreeCountMismatch {
                columns: column_log_sizes.len(),
                samples: sample_point_offsets.len(),
            });
        }

        let mut sample_count = 0_usize;
        let mut column_count = 0_usize;
        for (tree, (log_sizes, samples)) in column_log_sizes
            .iter()
            .zip(&sample_point_offsets)
            .enumerate()
        {
            if log_sizes.len() != samples.len() {
                return Err(PcsDeepCircuitError::TreeColumnCountMismatch {
                    tree,
                    columns: log_sizes.len(),
                    samples: samples.len(),
                });
            }
            for (column, (&log_size, points)) in log_sizes.iter().zip(samples).enumerate() {
                if log_size > lifting_log_size {
                    return Err(PcsDeepCircuitError::ColumnExceedsLiftingDomain {
                        tree,
                        column,
                        log_size,
                        lifting_log_size,
                    });
                }
                sample_count = sample_count.checked_add(points.len()).ok_or(
                    PcsDeepCircuitError::CountOverflow {
                        field: "sample count",
                    },
                )?;
            }
            column_count = column_count.checked_add(log_sizes.len()).ok_or(
                PcsDeepCircuitError::CountOverflow {
                    field: "column count",
                },
            )?;
        }
        checked_u32("sample count", sample_count)?;
        checked_u32("column count", column_count)?;
        checked_u32("query count", query_count)?;

        let (batches, term_count) =
            build_sample_batches(&column_log_sizes, &sample_point_offsets, lifting_log_size)?;
        Ok(Self {
            column_log_sizes,
            sample_point_offsets,
            batches,
            sample_count,
            column_count,
            term_count,
            lifting_log_size,
            query_count,
        })
    }

    /// Derives the quotient layout from the generated VM AIR and checked PCS geometry.
    pub fn from_vm(
        program: &VmAirProgram,
        layout: &VmPcsLayout,
    ) -> Result<Self, PcsDeepCircuitError> {
        if program.column_log_sizes().0.as_slice() != layout.column_log_sizes() {
            return Err(PcsDeepCircuitError::AirColumnLayoutMismatch);
        }
        Self::from_air_metadata(
            program.column_log_sizes(),
            program.sample_coordinates(),
            program.sample_point_offsets(),
            layout.log_blowup_factor(),
            layout.lifting_log_size(),
            layout.n_queries(),
        )
    }

    /// Derives the quotient layout from the detached Poseidon2 AIR and proof shape.
    pub fn from_poseidon2<
        const N_TABLES: usize,
        const N_TREES: usize,
        const N_FRI_LAYERS: usize,
    >(
        program: &Poseidon2AirProgram,
        pcs: ValidatedPcsParameters,
        shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    ) -> Result<Self, PcsDeepCircuitError> {
        let validated = shape
            .validate(pcs)
            .map_err(PcsDeepCircuitError::Poseidon2Shape)?;
        Self::from_air_metadata(
            program.column_log_sizes(),
            program.sample_coordinates(),
            program.sample_point_offsets(),
            pcs.config().fri_config.log_blowup_factor,
            validated.lifting_log_size(),
            pcs.config().fri_config.n_queries,
        )
    }

    fn from_air_metadata(
        column_log_sizes: &stwo::core::pcs::TreeVec<Vec<u32>>,
        sample_coordinates: &[SampleCoordinate],
        sample_point_offsets: &[CirclePointIndex],
        log_blowup_factor: u32,
        lifting_log_size: u32,
        n_queries: usize,
    ) -> Result<Self, PcsDeepCircuitError> {
        if sample_coordinates.len() != sample_point_offsets.len() {
            return Err(PcsDeepCircuitError::AirSampleMetadataLengthMismatch {
                coordinates: sample_coordinates.len(),
                offsets: sample_point_offsets.len(),
            });
        }
        let mut nested = column_log_sizes
            .iter()
            .map(|columns| vec![Vec::new(); columns.len()])
            .collect::<Vec<_>>();
        let mut previous = None;
        for (index, (coordinate, &offset)) in sample_coordinates
            .iter()
            .zip(sample_point_offsets)
            .enumerate()
        {
            validate_sample_coordinate(index, *coordinate, previous, &nested)?;
            nested[coordinate.tree][coordinate.column].push(offset);
            previous = Some(*coordinate);
        }
        let committed_log_sizes = column_log_sizes
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|log_size| log_size + log_blowup_factor)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Self::new(committed_log_sizes, nested, lifting_log_size, n_queries)
    }

    pub const fn sample_count(&self) -> usize {
        self.sample_count
    }

    pub const fn column_count(&self) -> usize {
        self.column_count
    }

    pub const fn term_count(&self) -> usize {
        self.term_count
    }

    pub const fn lifting_log_size(&self) -> u32 {
        self.lifting_log_size
    }

    pub const fn query_count(&self) -> usize {
        self.query_count
    }

    pub fn column_log_sizes(&self) -> &[Vec<u32>] {
        &self.column_log_sizes
    }

    pub fn sample_point_offsets(&self) -> &[Vec<Vec<CirclePointIndex>>] {
        &self.sample_point_offsets
    }
}

fn validate_sample_coordinate(
    index: usize,
    coordinate: SampleCoordinate,
    previous: Option<SampleCoordinate>,
    nested: &[Vec<Vec<CirclePointIndex>>],
) -> Result<(), PcsDeepCircuitError> {
    let Some(columns) = nested.get(coordinate.tree) else {
        return Err(PcsDeepCircuitError::AirSampleCoordinateOutOfRange { index, coordinate });
    };
    let Some(points) = columns.get(coordinate.column) else {
        return Err(PcsDeepCircuitError::AirSampleCoordinateOutOfRange { index, coordinate });
    };
    if coordinate.point != points.len() {
        return Err(PcsDeepCircuitError::AirSamplePointOrderMismatch {
            index,
            expected: points.len(),
            actual: coordinate.point,
        });
    }
    if previous.is_some_and(|previous| {
        (coordinate.tree, coordinate.column, coordinate.point)
            <= (previous.tree, previous.column, previous.point)
    }) {
        return Err(PcsDeepCircuitError::AirSampleOrderMismatch { index });
    }
    Ok(())
}

fn build_sample_batches(
    column_log_sizes: &[Vec<u32>],
    sample_point_offsets: &[Vec<Vec<CirclePointIndex>>],
    lifting_log_size: u32,
) -> Result<(Vec<SampleBatch>, usize), PcsDeepCircuitError> {
    let lifting_step = CanonicCoset::new(lifting_log_size).step_size();
    let mut batches = Vec::<SampleBatch>::new();
    let mut sample = 0_usize;
    let mut column = 0_usize;
    let mut random_power = 0_usize;
    for (tree_log_sizes, tree_points) in column_log_sizes.iter().zip(sample_point_offsets) {
        for (&log_size, points) in tree_log_sizes.iter().zip(tree_points) {
            if points.len() == 2 {
                let period_multiplier =
                    1_usize
                        .checked_shl(log_size)
                        .ok_or(PcsDeepCircuitError::CountOverflow {
                            field: "period multiplier",
                        })?;
                let periodic_point = points[1] + lifting_step * period_multiplier;
                push_sample_term(
                    &mut batches,
                    periodic_point,
                    SampleTerm {
                        column,
                        sample: sample + 1,
                        random_power,
                    },
                );
                random_power =
                    random_power
                        .checked_add(1)
                        .ok_or(PcsDeepCircuitError::CountOverflow {
                            field: "random-power count",
                        })?;
            }
            for (point, sample_index) in points.iter().copied().zip(sample..) {
                push_sample_term(
                    &mut batches,
                    point,
                    SampleTerm {
                        column,
                        sample: sample_index,
                        random_power,
                    },
                );
                random_power =
                    random_power
                        .checked_add(1)
                        .ok_or(PcsDeepCircuitError::CountOverflow {
                            field: "random-power count",
                        })?;
            }
            sample =
                sample
                    .checked_add(points.len())
                    .ok_or(PcsDeepCircuitError::CountOverflow {
                        field: "sample count",
                    })?;
            column = column
                .checked_add(1)
                .ok_or(PcsDeepCircuitError::CountOverflow {
                    field: "column count",
                })?;
        }
    }
    checked_u32("DEEP term count", random_power)?;
    Ok((batches, random_power))
}

fn push_sample_term(
    batches: &mut Vec<SampleBatch>,
    point_offset: CirclePointIndex,
    term: SampleTerm,
) {
    if let Some(batch) = batches
        .iter_mut()
        .find(|batch| batch.point_offset == point_offset)
    {
        batch.terms.push(term);
    } else {
        batches.push(SampleBatch {
            point_offset,
            terms: vec![term],
        });
    }
}

/// Values for one fixed PCS DEEP circuit instance.
pub struct PcsDeepWitness<'a> {
    pub active: bool,
    pub sampled_values: &'a [SecureField],
    pub queried_values: &'a [BaseField],
    pub oods_seed: [M31Word; SECURE_EXTENSION_DEGREE],
    pub deep_randomness: [M31Word; SECURE_EXTENSION_DEGREE],
    pub raw_queries: &'a [M31Word],
    pub answers: &'a [SecureField],
}

/// Fixed DEEP circuit and its verifier-owned input coordinates.
#[derive(Debug)]
pub struct PcsDeepCircuit {
    profile: PcsDeepProfile,
    circuit: ConstraintCircuit,
    input_bindings: Vec<PcsDeepInputBinding>,
}

impl PcsDeepCircuit {
    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub const fn profile(&self) -> &PcsDeepProfile {
        &self.profile
    }

    pub fn input_bindings(&self) -> &[PcsDeepInputBinding] {
        &self.input_bindings
    }

    pub fn nonzero_output_count(&self) -> usize {
        let arena = self.circuit.arena();
        self.circuit
            .outputs()
            .iter()
            .filter(|&&output| !arena.nodes[output].value.is_zero())
            .count()
    }
}

#[derive(Clone)]
struct SecureCircuitValue {
    value: Rec,
    conjugate: Rec,
}

#[derive(Clone)]
struct CircuitCirclePoint {
    x: Rec,
    y: Rec,
    conjugate_x: Rec,
    conjugate_y: Rec,
}

struct CircuitLine {
    column: usize,
    a: Rec,
    b: Rec,
    c: Rec,
}

struct CircuitBatch {
    point: CircuitCirclePoint,
    lines: Vec<CircuitLine>,
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<PcsDeepInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: PcsDeepInputSource, value: M31Word) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value.as_u32())));
        self.bindings.push(PcsDeepInputBinding {
            node_id: u32::try_from(node_id).expect("validated DEEP input count fits u32"),
            source,
        });
        value
    }

    fn secure_words(
        &mut self,
        words: [M31Word; SECURE_EXTENSION_DEGREE],
        source: impl Fn(u32) -> PcsDeepInputSource,
    ) -> SecureCircuitValue {
        let limbs = core::array::from_fn(|index| {
            self.input(
                source(u32::try_from(index).expect("secure-field word index fits u32")),
                words[index],
            )
        });
        secure_from_limbs(limbs)
    }

    fn secure_value(
        &mut self,
        value: SecureField,
        source: impl Fn(u32) -> PcsDeepInputSource,
    ) -> SecureCircuitValue {
        self.secure_words(value.to_m31_array().map(M31Word::from), source)
    }

    fn finish(self, profile: PcsDeepProfile) -> PcsDeepCircuit {
        PcsDeepCircuit {
            profile,
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

/// Builds the inactive zero-input circuit that fixes the profile structure.
pub fn build_pcs_deep_reference(
    profile: &PcsDeepProfile,
) -> Result<PcsDeepCircuit, PcsDeepCircuitError> {
    let sampled_values = vec![SecureField::zero(); profile.sample_count];
    let queried_values = vec![BaseField::zero(); queried_value_count(profile)?];
    let raw_queries = vec![M31Word::ZERO; profile.query_count];
    let answers = vec![SecureField::zero(); profile.query_count];
    build_pcs_deep_circuit(
        profile,
        PcsDeepWitness {
            active: false,
            sampled_values: &sampled_values,
            queried_values: &queried_values,
            oods_seed: [M31Word::ZERO; SECURE_EXTENSION_DEGREE],
            deep_randomness: [M31Word::ZERO; SECURE_EXTENSION_DEGREE],
            raw_queries: &raw_queries,
            answers: &answers,
        },
    )
}

/// Records one STWO-compatible DEEP quotient for every raw PCS query.
pub fn build_pcs_deep_circuit(
    profile: &PcsDeepProfile,
    witness: PcsDeepWitness<'_>,
) -> Result<PcsDeepCircuit, PcsDeepCircuitError> {
    validate_witness(profile, &witness)?;
    let mut builder = TrackedBuilder::new();
    let active = builder.input(
        PcsDeepInputSource::ActiveSelector,
        M31Word::from(u16::from(witness.active)),
    );
    builder
        .circuit
        .constrain_zero(active.clone() * (Rec::one() - active.clone()));

    let sampled_values = witness
        .sampled_values
        .iter()
        .copied()
        .enumerate()
        .map(|(sample, value)| {
            let sample = u32::try_from(sample).expect("validated sample count fits u32");
            builder.secure_value(value, |word| PcsDeepInputSource::SampledValueWord {
                sample,
                word,
            })
        })
        .collect::<Vec<_>>();

    let mut queried_values = Vec::with_capacity(witness.queried_values.len());
    let mut flat = 0_usize;
    for (tree, columns) in profile.column_log_sizes.iter().enumerate() {
        for column in 0..columns.len() {
            for query in 0..profile.query_count {
                let value = M31Word::from(witness.queried_values[flat]);
                queried_values.push(builder.input(
                    PcsDeepInputSource::QueriedValue {
                        tree: u32::try_from(tree).expect("validated tree index fits u32"),
                        column: u32::try_from(column).expect("validated column index fits u32"),
                        query: u32::try_from(query).expect("validated query index fits u32"),
                    },
                    value,
                ));
                flat += 1;
            }
        }
    }

    let oods_seed = builder.secure_words(witness.oods_seed, |word| {
        PcsDeepInputSource::OodsSeedWord { word }
    });
    let deep_randomness = builder.secure_words(witness.deep_randomness, |word| {
        PcsDeepInputSource::DeepRandomnessWord { word }
    });
    let safe_seed = SecureField::from_m31_array(SAFE_OODS_WORDS.map(M31::from));
    let effective_seed = SecureCircuitValue {
        value: select(active.clone(), oods_seed.value, Rec::from(safe_seed)),
        conjugate: select(
            active.clone(),
            oods_seed.conjugate,
            Rec::from(outer_conjugate(safe_seed)),
        ),
    };
    let oods_point = circuit_point_from_seed(effective_seed)?;
    let effective_randomness = select(
        active.clone(),
        deep_randomness.value,
        Rec::from(SecureField::one()),
    );

    let mut query_points = Vec::with_capacity(profile.query_count);
    for (query, raw) in witness.raw_queries.iter().copied().enumerate() {
        let raw = raw.as_u32();
        let mut bits = Vec::with_capacity(M31_BITS);
        for bit in 0..M31_BITS {
            let value = M31Word::from(u16::try_from((raw >> bit) & 1).expect("bit fits u16"));
            let bit_value = builder.input(
                PcsDeepInputSource::QueryBit {
                    query: u32::try_from(query).expect("validated query index fits u32"),
                    bit: u32::try_from(bit).expect("M31 bit index fits u32"),
                },
                value,
            );
            builder
                .circuit
                .constrain_zero(bit_value.clone() * (Rec::one() - bit_value.clone()));
            bits.push(bit_value);
        }
        let mask = (1_u32 << profile.lifting_log_size) - 1;
        let position = raw & mask;
        let position_input = builder.input(
            PcsDeepInputSource::QueryPosition {
                query: u32::try_from(query).expect("validated query index fits u32"),
            },
            M31Word::try_from(position).expect("lifting-domain position is canonical"),
        );
        let reconstructed = bits
            .iter()
            .take(profile.lifting_log_size as usize)
            .enumerate()
            .fold(Rec::zero(), |sum, (bit, value)| {
                sum + value.clone() * BaseField::from(1_u32 << bit)
            });
        builder
            .circuit
            .constrain_zero(position_input - reconstructed);
        let effective_bits = bits
            .into_iter()
            .map(|bit| active.clone() * bit)
            .collect::<Vec<_>>();
        query_points.push(query_circle_point(
            &effective_bits,
            profile.lifting_log_size,
        ));
    }

    let answers = witness
        .answers
        .iter()
        .copied()
        .enumerate()
        .map(|(query, value)| {
            let query = u32::try_from(query).expect("validated query index fits u32");
            builder.secure_value(value, |word| PcsDeepInputSource::AnswerWord { query, word })
        })
        .collect::<Vec<_>>();

    let powers = random_powers(effective_randomness, profile.term_count);
    let batches = circuit_batches(profile, &oods_point, &sampled_values, &powers);
    for (query, point) in query_points.iter().enumerate() {
        let answer = evaluate_query(query, point, &batches, &queried_values, profile.query_count)?;
        builder
            .circuit
            .constrain_zero(active.clone() * (answer - answers[query].value.clone()));
    }
    Ok(builder.finish(profile.clone()))
}

fn validate_witness(
    profile: &PcsDeepProfile,
    witness: &PcsDeepWitness<'_>,
) -> Result<(), PcsDeepCircuitError> {
    require_count(
        "sampled values",
        profile.sample_count,
        witness.sampled_values.len(),
    )?;
    require_count(
        "queried values",
        queried_value_count(profile)?,
        witness.queried_values.len(),
    )?;
    require_count(
        "raw queries",
        profile.query_count,
        witness.raw_queries.len(),
    )?;
    require_count("DEEP answers", profile.query_count, witness.answers.len())
}

fn queried_value_count(profile: &PcsDeepProfile) -> Result<usize, PcsDeepCircuitError> {
    profile.column_count.checked_mul(profile.query_count).ok_or(
        PcsDeepCircuitError::CountOverflow {
            field: "queried value count",
        },
    )
}

fn require_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), PcsDeepCircuitError> {
    if expected == actual {
        Ok(())
    } else {
        Err(PcsDeepCircuitError::WitnessCountMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn circuit_point_from_seed(
    seed: SecureCircuitValue,
) -> Result<CircuitCirclePoint, PcsDeepCircuitError> {
    let point = oods_point_from_seed(seed.value)?;
    let conjugate = oods_point_from_seed(seed.conjugate)?;
    Ok(CircuitCirclePoint {
        x: point.x,
        y: point.y,
        conjugate_x: conjugate.x,
        conjugate_y: conjugate.y,
    })
}

fn query_circle_point(bits: &[Rec], lifting_log_size: u32) -> CircuitCirclePoint {
    let half_coset = CanonicCoset::new(lifting_log_size)
        .circle_domain()
        .half_coset;
    let initial = half_coset.initial;
    let mut point = OodsPointCircuit {
        x: Rec::from(initial.x),
        y: Rec::from(initial.y),
    };
    // Bit reversal makes raw bit zero select the conjugate half, while raw
    // bits one through L-1 select descending powers of the half-coset step.
    for (source_bit, bit) in bits
        .iter()
        .enumerate()
        .take(lifting_log_size as usize)
        .skip(1)
    {
        let scalar = 1_usize << (lifting_log_size as usize - 1 - source_bit);
        let contribution = (half_coset.step_size * scalar).to_point();
        let bit = bit.clone();
        let selected = OodsPointCircuit {
            x: Rec::one() + bit.clone() * (Rec::from(contribution.x) - Rec::one()),
            y: bit * contribution.y,
        };
        point = circle_add(point, selected);
    }
    let sign = Rec::one() - (bits[0].clone() + bits[0].clone());
    point.y *= sign;
    CircuitCirclePoint {
        conjugate_x: point.x.clone(),
        conjugate_y: point.y.clone(),
        x: point.x,
        y: point.y,
    }
}

fn circle_add(lhs: OodsPointCircuit, rhs: OodsPointCircuit) -> OodsPointCircuit {
    OodsPointCircuit {
        x: lhs.x.clone() * rhs.x.clone() - lhs.y.clone() * rhs.y.clone(),
        y: lhs.x * rhs.y + lhs.y * rhs.x,
    }
}

fn add_base_point(point: &CircuitCirclePoint, offset: CirclePointIndex) -> CircuitCirclePoint {
    let offset = offset.to_point();
    let add = |x: Rec, y: Rec| {
        circle_add(
            OodsPointCircuit { x, y },
            OodsPointCircuit {
                x: Rec::from(offset.x),
                y: Rec::from(offset.y),
            },
        )
    };
    let shifted = add(point.x.clone(), point.y.clone());
    let conjugate = add(point.conjugate_x.clone(), point.conjugate_y.clone());
    CircuitCirclePoint {
        x: shifted.x,
        y: shifted.y,
        conjugate_x: conjugate.x,
        conjugate_y: conjugate.y,
    }
}

fn random_powers(randomness: Rec, count: usize) -> Vec<Rec> {
    let mut current = Rec::one();
    (0..count)
        .map(|_| {
            let power = current.clone();
            current *= randomness.clone();
            power
        })
        .collect()
}

fn circuit_batches(
    profile: &PcsDeepProfile,
    oods_point: &CircuitCirclePoint,
    sampled_values: &[SecureCircuitValue],
    powers: &[Rec],
) -> Vec<CircuitBatch> {
    profile
        .batches
        .iter()
        .map(|batch| {
            let point = add_base_point(oods_point, batch.point_offset);
            let lines = batch
                .terms
                .iter()
                .map(|term| {
                    let sample = &sampled_values[term.sample];
                    let power = powers[term.random_power].clone();
                    let a = sample.conjugate.clone() - sample.value.clone();
                    let c = point.conjugate_y.clone() - point.y.clone();
                    let b = sample.value.clone() * c.clone() - a.clone() * point.y.clone();
                    CircuitLine {
                        column: term.column,
                        a: power.clone() * a,
                        b: power.clone() * b,
                        c: power * c,
                    }
                })
                .collect();
            CircuitBatch { point, lines }
        })
        .collect()
}

fn evaluate_query(
    query: usize,
    domain_point: &CircuitCirclePoint,
    batches: &[CircuitBatch],
    queried_values: &[Rec],
    query_count: usize,
) -> Result<Rec, PcsDeepCircuitError> {
    let half = Rec::from(BaseField::from(2).inverse());
    let inverse_two_outer_basis = Rec::from(SecureField::from_u32_unchecked(0, 0, 2, 0).inverse());
    let mut answer = Rec::zero();
    for (batch_index, batch) in batches.iter().enumerate() {
        let real_x = (batch.point.x.clone() + batch.point.conjugate_x.clone()) * half.clone();
        let imaginary_x = (batch.point.x.clone() - batch.point.conjugate_x.clone())
            * inverse_two_outer_basis.clone();
        let real_y = (batch.point.y.clone() + batch.point.conjugate_y.clone()) * half.clone();
        let imaginary_y = (batch.point.y.clone() - batch.point.conjugate_y.clone())
            * inverse_two_outer_basis.clone();
        let denominator = (real_x - domain_point.x.clone()) * imaginary_y
            - (real_y - domain_point.y.clone()) * imaginary_x;
        if denominator.value().is_zero() {
            return Err(PcsDeepCircuitError::ZeroQuotientDenominator {
                query,
                batch: batch_index,
            });
        }
        let mut numerator = Rec::zero();
        for line in &batch.lines {
            let index = line
                .column
                .checked_mul(query_count)
                .and_then(|base| base.checked_add(query))
                .expect("validated queried-value count fits usize");
            numerator += queried_values[index].clone() * line.c.clone()
                - (line.a.clone() * domain_point.y.clone() + line.b.clone());
        }
        answer += numerator * denominator.inverse();
    }
    Ok(answer)
}

fn select(selector: Rec, active: Rec, inactive: Rec) -> Rec {
    selector.clone() * active + (Rec::one() - selector) * inactive
}

fn secure_from_limbs(limbs: [Rec; SECURE_EXTENSION_DEGREE]) -> SecureCircuitValue {
    let [a, b, c, d] = limbs;
    let value = a.clone()
        + b.clone() * secure_basis(1)
        + c.clone() * secure_basis(2)
        + d.clone() * secure_basis(3);
    let conjugate = a + b * secure_basis(1) - c * secure_basis(2) - d * secure_basis(3);
    SecureCircuitValue { value, conjugate }
}

fn secure_basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        M31::from(u32::from(limb == index))
    }))
}

fn outer_conjugate(value: SecureField) -> SecureField {
    value.complex_conjugate()
}

fn checked_u32(field: &'static str, value: usize) -> Result<u32, PcsDeepCircuitError> {
    u32::try_from(value).map_err(|_| PcsDeepCircuitError::IndexOutOfRange { field, value })
}

/// Invalid fixed DEEP geometry or per-proof assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PcsDeepCircuitError {
    LiftingLogSizeOutOfRange {
        lifting_log_size: u32,
    },
    ZeroQueries,
    TreeCountMismatch {
        columns: usize,
        samples: usize,
    },
    TreeColumnCountMismatch {
        tree: usize,
        columns: usize,
        samples: usize,
    },
    ColumnExceedsLiftingDomain {
        tree: usize,
        column: usize,
        log_size: u32,
        lifting_log_size: u32,
    },
    AirColumnLayoutMismatch,
    AirSampleMetadataLengthMismatch {
        coordinates: usize,
        offsets: usize,
    },
    AirSampleCoordinateOutOfRange {
        index: usize,
        coordinate: SampleCoordinate,
    },
    AirSamplePointOrderMismatch {
        index: usize,
        expected: usize,
        actual: usize,
    },
    AirSampleOrderMismatch {
        index: usize,
    },
    Poseidon2Shape(ProofShapeError),
    CountOverflow {
        field: &'static str,
    },
    IndexOutOfRange {
        field: &'static str,
        value: usize,
    },
    WitnessCountMismatch {
        field: &'static str,
        expected: usize,
        actual: usize,
    },
    ZeroQuotientDenominator {
        query: usize,
        batch: usize,
    },
    Oods(OodsCircuitError),
}

impl From<OodsCircuitError> for PcsDeepCircuitError {
    fn from(value: OodsCircuitError) -> Self {
        Self::Oods(value)
    }
}

impl fmt::Display for PcsDeepCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for PcsDeepCircuitError {}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use stwo::core::circle::CirclePoint;
    use stwo::core::fields::qm31::SecureField;
    use stwo::core::pcs::TreeVec;
    use stwo::core::pcs::quotients::{PointSample, fri_answers};
    use stwo::core::poly::circle::CanonicCoset;
    use stwo::core::utils::bit_reverse_index;

    use super::*;

    fn secure(seed: u32) -> SecureField {
        SecureField::from_m31_array([
            M31::from(seed),
            M31::from(seed + 1),
            M31::from(seed + 2),
            M31::from(seed + 3),
        ])
    }

    fn native_oods(seed: SecureField) -> CirclePoint<SecureField> {
        let square = seed.square();
        let inverse = (SecureField::one() + square).inverse();
        CirclePoint {
            x: (SecureField::one() - square) * inverse,
            y: (seed + seed) * inverse,
        }
    }

    fn profile() -> PcsDeepProfile {
        let mask_step = CanonicCoset::new(4).step_size();
        PcsDeepProfile::new(
            vec![vec![4, 3], vec![4]],
            vec![
                vec![vec![CirclePointIndex::zero(), mask_step], Vec::new()],
                vec![vec![-mask_step]],
            ],
            5,
            2,
        )
        .expect("fixture DEEP profile is valid")
    }

    fn native_answers(
        profile: &PcsDeepProfile,
        sampled_values: &[SecureField],
        queried_values: &[BaseField],
        oods_seed: SecureField,
        randomness: SecureField,
        raw_queries: &[M31Word],
    ) -> Vec<SecureField> {
        let oods = native_oods(oods_seed);
        let mut sample = 0_usize;
        let samples = profile
            .sample_point_offsets
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|points| {
                        points
                            .iter()
                            .map(|offset| {
                                let value = sampled_values[sample];
                                sample += 1;
                                PointSample {
                                    point: oods + offset.to_point().into_ef(),
                                    value,
                                }
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut queried = 0_usize;
        let queried_values = profile
            .column_log_sizes
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|_| {
                        let values =
                            queried_values[queried..queried + profile.query_count].to_vec();
                        queried += profile.query_count;
                        values
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        fri_answers(
            TreeVec::new(profile.column_log_sizes.clone()),
            TreeVec::new(samples),
            randomness,
            &raw_queries
                .iter()
                .map(|query| query.as_u32() as usize & ((1 << profile.lifting_log_size) - 1))
                .collect::<Vec<_>>(),
            TreeVec::new(queried_values),
            profile.lifting_log_size,
        )
        .expect("fixture quotient denominators are nonzero")
    }

    fn differential_circuit(answer_delta: SecureField) -> PcsDeepCircuit {
        let profile = profile();
        let sampled_values = [secure(101), secure(107), secure(109)];
        let queried_values = [11, 13, 17, 19, 23, 29].map(BaseField::from);
        let oods_seed = secure(37);
        let randomness = secure(53);
        let raw_queries = [M31Word::from(5_u16), M31Word::from(18_u16)];
        let mut answers = native_answers(
            &profile,
            &sampled_values,
            &queried_values,
            oods_seed,
            randomness,
            &raw_queries,
        );
        answers[0] += answer_delta;
        build_pcs_deep_circuit(
            &profile,
            PcsDeepWitness {
                active: true,
                sampled_values: &sampled_values,
                queried_values: &queried_values,
                oods_seed: oods_seed.to_m31_array().map(M31Word::from),
                deep_randomness: randomness.to_m31_array().map(M31Word::from),
                raw_queries: &raw_queries,
                answers: &answers,
            },
        )
        .expect("fixture DEEP circuit is constructible")
    }

    #[rstest]
    #[case(4, 0)]
    #[case(4, 7)]
    #[case(5, 18)]
    #[case(12, 2_731)]
    fn query_point_matches_stwo_bit_reversed_domain(#[case] log_size: u32, #[case] position: u32) {
        let bits = (0..M31_BITS)
            .map(|bit| Rec::from(BaseField::from((position >> bit) & 1)))
            .collect::<Vec<_>>();
        let actual = query_circle_point(&bits, log_size);
        let domain = CanonicCoset::new(log_size).circle_domain();
        let expected = domain.at(bit_reverse_index(position as usize, log_size));
        assert_eq!(
            (actual.x.value(), actual.y.value()),
            (expected.x.into(), expected.y.into())
        );
    }

    #[rstest]
    fn circuit_matches_stwo_deep_answers_with_periodicity() {
        assert_eq!(
            differential_circuit(SecureField::zero()).nonzero_output_count(),
            0
        );
    }

    #[rstest]
    fn changed_first_fri_answer_breaks_the_deep_equality() {
        assert_eq!(
            differential_circuit(SecureField::one()).nonzero_output_count(),
            1
        );
    }

    #[rstest]
    fn inactive_reference_keeps_the_full_circuit_satisfied() {
        let profile = profile();
        assert_eq!(
            build_pcs_deep_reference(&profile)
                .expect("fixed inactive reference is constructible")
                .nonzero_output_count(),
            0
        );
    }
}
