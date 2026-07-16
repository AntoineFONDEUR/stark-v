//! Fixed STWO FRI folding and last-layer arithmetic for recursion V2.
//!
//! The circuit checks each authenticated fold subset in proof order, replaces
//! the queried offset with the value carried from the preceding stage, and
//! applies STWO's exact circle-to-line and line-fold butterflies. It then
//! evaluates the bit-reversed last-layer coefficients at every routed query
//! point. Every proof value is a tracked input so ownership AIRs can connect
//! the arithmetic to transcript, query-routing, and Merkle relations.

use core::fmt;

use air::digest::M31Word;
use num_traits::{One, Zero};
use stwo::core::circle::{CirclePointIndex, M31_CIRCLE_LOG_ORDER};
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::{BaseField, M31};
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::poly::circle::MAX_CIRCLE_DOMAIN_LOG_SIZE;

use super::protocol::{FixedProofShape, ProofShapeError, ValidatedPcsParameters};
use crate::recorder::{CircuitBuilder, ConstraintCircuit, Rec};

const M31_BITS: usize = M31_CIRCLE_LOG_ORDER as usize;

/// One verifier-owned input of the fixed FRI arithmetic circuit.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum FriVerifierInputSource {
    ActiveSelector,
    DeepAnswerWord {
        query: u32,
        word: u32,
    },
    AuthenticatedValueWord {
        layer: u32,
        query: u32,
        offset: u32,
        word: u32,
    },
    FriAlphaWord {
        layer: u32,
        word: u32,
    },
    QueryBit {
        query: u32,
        bit: u32,
    },
    FriPosition {
        layer: u32,
        query: u32,
    },
    FriOffset {
        layer: u32,
        query: u32,
    },
    LastLayerPosition {
        query: u32,
    },
    LastLayerCoefficientWord {
        coefficient: u32,
        word: u32,
    },
}

/// Circuit node and the exact verifier relation that supplies it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriVerifierInputBinding {
    pub node_id: u32,
    pub source: FriVerifierInputSource,
}

/// Trusted FRI domain, layer, coefficient, and query geometry for one lane.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriVerifierProfile {
    lifting_log_size: u32,
    log_blowup_factor: u32,
    log_last_layer_degree_bound: u32,
    fold_steps: Vec<u32>,
    fold_widths: Vec<usize>,
    query_count: usize,
    last_layer_coefficient_count: usize,
    last_layer_domain_log_size: u32,
}

impl FriVerifierProfile {
    /// Validates the exact FRI geometry needed by the arithmetic circuit.
    pub fn new(
        lifting_log_size: u32,
        log_blowup_factor: u32,
        log_last_layer_degree_bound: u32,
        fold_widths: Vec<u32>,
        query_count: usize,
    ) -> Result<Self, FriVerifierCircuitError> {
        if !(1..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&lifting_log_size) {
            return Err(FriVerifierCircuitError::LiftingLogSizeOutOfRange { lifting_log_size });
        }
        if query_count == 0 {
            return Err(FriVerifierCircuitError::ZeroQueries);
        }
        if fold_widths.is_empty() {
            return Err(FriVerifierCircuitError::ZeroLayers);
        }
        let last_layer_domain_log_size = log_blowup_factor
            .checked_add(log_last_layer_degree_bound)
            .ok_or(FriVerifierCircuitError::CountOverflow {
                field: "last-layer domain log size",
            })?;
        let required_folds = lifting_log_size
            .checked_sub(last_layer_domain_log_size)
            .ok_or(FriVerifierCircuitError::InvalidDegreeRange {
                lifting_log_size,
                log_blowup_factor,
                log_last_layer_degree_bound,
            })?;
        if required_folds == 0 {
            return Err(FriVerifierCircuitError::InvalidDegreeRange {
                lifting_log_size,
                log_blowup_factor,
                log_last_layer_degree_bound,
            });
        }

        let mut folded = 0_u32;
        let mut fold_steps = Vec::with_capacity(fold_widths.len());
        let mut checked_widths = Vec::with_capacity(fold_widths.len());
        for (layer, width) in fold_widths.into_iter().enumerate() {
            if width < 2 || !width.is_power_of_two() {
                return Err(FriVerifierCircuitError::InvalidFoldWidth { layer, width });
            }
            let fold_step = width.ilog2();
            folded =
                folded
                    .checked_add(fold_step)
                    .ok_or(FriVerifierCircuitError::CountOverflow {
                        field: "FRI fold count",
                    })?;
            fold_steps.push(fold_step);
            checked_widths.push(usize::try_from(width).map_err(|_| {
                FriVerifierCircuitError::IndexOutOfRange {
                    field: "FRI fold width",
                    value: width as usize,
                }
            })?);
        }
        if folded != required_folds {
            return Err(FriVerifierCircuitError::FoldCountMismatch {
                expected: required_folds,
                actual: folded,
            });
        }
        let last_layer_coefficient_count = 1_usize.checked_shl(log_last_layer_degree_bound).ok_or(
            FriVerifierCircuitError::CountOverflow {
                field: "last-layer coefficient count",
            },
        )?;
        checked_u32("query count", query_count)?;
        checked_u32("last-layer coefficient count", last_layer_coefficient_count)?;
        for &width in &checked_widths {
            checked_u32("FRI fold width", width)?;
        }

        Ok(Self {
            lifting_log_size,
            log_blowup_factor,
            log_last_layer_degree_bound,
            fold_steps,
            fold_widths: checked_widths,
            query_count,
            last_layer_coefficient_count,
            last_layer_domain_log_size,
        })
    }

    /// Derives the circuit profile from a semantically checked proof shape.
    pub fn from_shape<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
        pcs: ValidatedPcsParameters,
        shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    ) -> Result<Self, FriVerifierCircuitError> {
        let validated = shape
            .validate(pcs)
            .map_err(FriVerifierCircuitError::Shape)?;
        let config = pcs.config().fri_config;
        Self::new(
            validated.lifting_log_size(),
            config.log_blowup_factor,
            config.log_last_layer_degree_bound,
            shape
                .fri_layer_fold_widths
                .iter()
                .copied()
                .map(M31Word::as_u32)
                .collect(),
            config.n_queries,
        )
    }

    pub const fn lifting_log_size(&self) -> u32 {
        self.lifting_log_size
    }

    pub const fn log_blowup_factor(&self) -> u32 {
        self.log_blowup_factor
    }

    pub const fn log_last_layer_degree_bound(&self) -> u32 {
        self.log_last_layer_degree_bound
    }

    pub fn fold_steps(&self) -> &[u32] {
        &self.fold_steps
    }

    pub fn fold_widths(&self) -> &[usize] {
        &self.fold_widths
    }

    pub const fn query_count(&self) -> usize {
        self.query_count
    }

    pub const fn last_layer_coefficient_count(&self) -> usize {
        self.last_layer_coefficient_count
    }

    pub const fn last_layer_domain_log_size(&self) -> u32 {
        self.last_layer_domain_log_size
    }

    pub fn layer_count(&self) -> usize {
        self.fold_steps.len()
    }
}

/// Per-proof assignment for one fixed FRI verifier circuit.
#[derive(Clone, Copy)]
pub struct FriVerifierWitness<'a> {
    pub active: bool,
    pub deep_answers: &'a [SecureField],
    /// Layer-major, then query-major, then subset-offset-major values.
    pub authenticated_values: &'a [Vec<SecureField>],
    pub fri_alphas: &'a [SecureField],
    pub raw_queries: &'a [M31Word],
    pub fri_positions: &'a [Vec<M31Word>],
    pub fri_offsets: &'a [Vec<M31Word>],
    pub last_layer_positions: &'a [M31Word],
    pub last_layer_coefficients: &'a [SecureField],
}

/// One fixed zero-output FRI verifier arithmetic graph.
#[derive(Debug)]
pub struct FriVerifierCircuit {
    profile: FriVerifierProfile,
    circuit: ConstraintCircuit,
    input_bindings: Vec<FriVerifierInputBinding>,
}

impl FriVerifierCircuit {
    pub const fn circuit(&self) -> &ConstraintCircuit {
        &self.circuit
    }

    pub const fn profile(&self) -> &FriVerifierProfile {
        &self.profile
    }

    pub fn input_bindings(&self) -> &[FriVerifierInputBinding] {
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
struct CircuitPoint {
    x: Rec,
    y: Rec,
}

struct TrackedBuilder {
    circuit: CircuitBuilder,
    bindings: Vec<FriVerifierInputBinding>,
}

impl TrackedBuilder {
    fn new() -> Self {
        Self {
            circuit: CircuitBuilder::default(),
            bindings: Vec::new(),
        }
    }

    fn input(&mut self, source: FriVerifierInputSource, value: M31Word) -> Rec {
        let (node_id, value) = self
            .circuit
            .input(SecureField::from(BaseField::from(value.as_u32())));
        self.bindings.push(FriVerifierInputBinding {
            node_id: u32::try_from(node_id).expect("validated FRI input count fits u32"),
            source,
        });
        value
    }

    fn secure_value(
        &mut self,
        value: SecureField,
        source: impl Fn(u32) -> FriVerifierInputSource,
    ) -> Rec {
        let limbs = value.to_m31_array().map(M31Word::from);
        let words = core::array::from_fn(|index| {
            self.input(
                source(u32::try_from(index).expect("secure-field word index fits u32")),
                limbs[index],
            )
        });
        secure_from_words(words)
    }

    fn finish(self, profile: FriVerifierProfile) -> FriVerifierCircuit {
        FriVerifierCircuit {
            profile,
            circuit: self.circuit.finish(),
            input_bindings: self.bindings,
        }
    }
}

/// Builds the inactive zero-input circuit that fixes the FRI graph structure.
pub fn build_fri_verifier_reference(
    profile: &FriVerifierProfile,
) -> Result<FriVerifierCircuit, FriVerifierCircuitError> {
    let deep_answers = vec![SecureField::zero(); profile.query_count];
    let authenticated_values = profile
        .fold_widths
        .iter()
        .map(|width| vec![SecureField::zero(); profile.query_count * width])
        .collect::<Vec<_>>();
    let fri_alphas = vec![SecureField::zero(); profile.layer_count()];
    let raw_queries = vec![M31Word::ZERO; profile.query_count];
    let fri_positions = profile
        .fold_widths
        .iter()
        .map(|_| vec![M31Word::ZERO; profile.query_count])
        .collect::<Vec<_>>();
    let fri_offsets = fri_positions.clone();
    let last_layer_positions = vec![M31Word::ZERO; profile.query_count];
    let last_layer_coefficients = vec![SecureField::zero(); profile.last_layer_coefficient_count];
    build_fri_verifier_circuit(
        profile,
        FriVerifierWitness {
            active: false,
            deep_answers: &deep_answers,
            authenticated_values: &authenticated_values,
            fri_alphas: &fri_alphas,
            raw_queries: &raw_queries,
            fri_positions: &fri_positions,
            fri_offsets: &fri_offsets,
            last_layer_positions: &last_layer_positions,
            last_layer_coefficients: &last_layer_coefficients,
        },
    )
}

/// Records STWO-compatible FRI folds and last-layer checks for every query.
pub fn build_fri_verifier_circuit(
    profile: &FriVerifierProfile,
    witness: FriVerifierWitness<'_>,
) -> Result<FriVerifierCircuit, FriVerifierCircuitError> {
    validate_witness(profile, &witness)?;
    let mut builder = TrackedBuilder::new();
    let active = builder.input(
        FriVerifierInputSource::ActiveSelector,
        M31Word::from(u16::from(witness.active)),
    );
    builder
        .circuit
        .constrain_zero(active.clone() * (Rec::one() - active.clone()));

    let deep_answers = witness
        .deep_answers
        .iter()
        .copied()
        .enumerate()
        .map(|(query, value)| {
            let query = checked_u32("query", query).expect("validated query index fits u32");
            builder.secure_value(value, |word| FriVerifierInputSource::DeepAnswerWord {
                query,
                word,
            })
        })
        .collect::<Vec<_>>();

    let mut authenticated_values = Vec::with_capacity(profile.layer_count());
    for (layer, (values, &width)) in witness
        .authenticated_values
        .iter()
        .zip(&profile.fold_widths)
        .enumerate()
    {
        let layer = checked_u32("FRI layer", layer).expect("validated layer index fits u32");
        let tracked = values
            .iter()
            .copied()
            .enumerate()
            .map(|(index, value)| {
                let query = index / width;
                let offset = index % width;
                let query = checked_u32("query", query).expect("validated query index fits u32");
                let offset = checked_u32("FRI offset", offset).expect("validated offset fits u32");
                builder.secure_value(value, |word| {
                    FriVerifierInputSource::AuthenticatedValueWord {
                        layer,
                        query,
                        offset,
                        word,
                    }
                })
            })
            .collect::<Vec<_>>();
        authenticated_values.push(tracked);
    }

    let fri_alphas = witness
        .fri_alphas
        .iter()
        .copied()
        .enumerate()
        .map(|(layer, alpha)| {
            let layer = checked_u32("FRI layer", layer).expect("validated layer index fits u32");
            builder.secure_value(alpha, |word| FriVerifierInputSource::FriAlphaWord {
                layer,
                word,
            })
        })
        .collect::<Vec<_>>();

    let mut query_bits = Vec::with_capacity(profile.query_count);
    for (query, raw_query) in witness.raw_queries.iter().copied().enumerate() {
        let raw = raw_query.as_u32();
        let query = checked_u32("query", query).expect("validated query index fits u32");
        let mut bits = Vec::with_capacity(M31_BITS);
        for bit in 0..M31_BITS {
            let value = M31Word::from(u16::try_from((raw >> bit) & 1).expect("bit fits u16"));
            let tracked = builder.input(
                FriVerifierInputSource::QueryBit {
                    query,
                    bit: u32::try_from(bit).expect("M31 bit index fits u32"),
                },
                value,
            );
            builder
                .circuit
                .constrain_zero(tracked.clone() * (Rec::one() - tracked.clone()));
            bits.push(tracked);
        }
        query_bits.push(bits);
    }

    let mut fri_positions = Vec::with_capacity(profile.layer_count());
    let mut fri_offsets = Vec::with_capacity(profile.layer_count());
    for layer in 0..profile.layer_count() {
        let layer_u32 = checked_u32("FRI layer", layer).expect("validated layer index fits u32");
        fri_positions.push(
            witness.fri_positions[layer]
                .iter()
                .copied()
                .enumerate()
                .map(|(query, value)| {
                    builder.input(
                        FriVerifierInputSource::FriPosition {
                            layer: layer_u32,
                            query: checked_u32("query", query)
                                .expect("validated query index fits u32"),
                        },
                        value,
                    )
                })
                .collect::<Vec<_>>(),
        );
        fri_offsets.push(
            witness.fri_offsets[layer]
                .iter()
                .copied()
                .enumerate()
                .map(|(query, value)| {
                    builder.input(
                        FriVerifierInputSource::FriOffset {
                            layer: layer_u32,
                            query: checked_u32("query", query)
                                .expect("validated query index fits u32"),
                        },
                        value,
                    )
                })
                .collect::<Vec<_>>(),
        );
    }
    let last_layer_positions = witness
        .last_layer_positions
        .iter()
        .copied()
        .enumerate()
        .map(|(query, value)| {
            builder.input(
                FriVerifierInputSource::LastLayerPosition {
                    query: checked_u32("query", query).expect("validated query index fits u32"),
                },
                value,
            )
        })
        .collect::<Vec<_>>();
    let last_layer_coefficients = witness
        .last_layer_coefficients
        .iter()
        .copied()
        .enumerate()
        .map(|(coefficient, value)| {
            let coefficient = checked_u32("last-layer coefficient", coefficient)
                .expect("validated coefficient index fits u32");
            builder.secure_value(value, |word| {
                FriVerifierInputSource::LastLayerCoefficientWord { coefficient, word }
            })
        })
        .collect::<Vec<_>>();

    for query in 0..profile.query_count {
        let bits = &query_bits[query];
        let mut folded_bits = 0_u32;
        let mut previous = deep_answers[query].clone();
        let mut current_log_size = profile.lifting_log_size;
        for layer in 0..profile.layer_count() {
            let fold_step = profile.fold_steps[layer];
            let width = profile.fold_widths[layer];
            let current_bits = &bits[folded_bits as usize
                ..usize::try_from(folded_bits + current_log_size)
                    .expect("validated bit range fits usize")];
            let position = reconstruct_bits(current_bits);
            let offset = reconstruct_bits(&current_bits[..fold_step as usize]);
            builder
                .circuit
                .constrain_zero(fri_positions[layer][query].clone() - position);
            builder
                .circuit
                .constrain_zero(fri_offsets[layer][query].clone() - offset);

            let values = &authenticated_values[layer][query * width..(query + 1) * width];
            let selected = select_offset(values, &current_bits[..fold_step as usize]);
            builder
                .circuit
                .constrain_zero(active.clone() * (selected - previous));

            let mut subset_bits = current_bits.to_vec();
            for bit in subset_bits.iter_mut().take(fold_step as usize) {
                *bit = Rec::zero();
            }
            let initial = if layer == 0 {
                circle_domain_point(&subset_bits, current_log_size)
            } else {
                line_domain_point(&subset_bits, current_log_size)
            };
            previous = if layer == 0 {
                fold_circle_subset(values, initial, fold_step, fri_alphas[layer].clone())
            } else {
                fold_line_subset(values, initial, fold_step, fri_alphas[layer].clone())
            };
            folded_bits += fold_step;
            current_log_size -= fold_step;
        }

        let last_bits = &bits[folded_bits as usize
            ..usize::try_from(folded_bits + profile.last_layer_domain_log_size)
                .expect("validated last-layer bit range fits usize")];
        builder
            .circuit
            .constrain_zero(last_layer_positions[query].clone() - reconstruct_bits(last_bits));
        let point = line_domain_point(last_bits, profile.last_layer_domain_log_size);
        let expected = evaluate_last_layer(&last_layer_coefficients, point.x);
        builder
            .circuit
            .constrain_zero(active.clone() * (previous - expected));
    }

    Ok(builder.finish(profile.clone()))
}

fn validate_witness(
    profile: &FriVerifierProfile,
    witness: &FriVerifierWitness<'_>,
) -> Result<(), FriVerifierCircuitError> {
    require_count(
        "DEEP answers",
        profile.query_count,
        witness.deep_answers.len(),
    )?;
    require_count(
        "authenticated FRI layers",
        profile.layer_count(),
        witness.authenticated_values.len(),
    )?;
    for (layer, (&width, values)) in profile
        .fold_widths
        .iter()
        .zip(witness.authenticated_values)
        .enumerate()
    {
        let expected = profile.query_count.checked_mul(width).ok_or(
            FriVerifierCircuitError::CountOverflow {
                field: "authenticated FRI values",
            },
        )?;
        if values.len() != expected {
            return Err(FriVerifierCircuitError::LayerValueCountMismatch {
                layer,
                expected,
                actual: values.len(),
            });
        }
    }
    require_count(
        "FRI alphas",
        profile.layer_count(),
        witness.fri_alphas.len(),
    )?;
    require_count(
        "raw queries",
        profile.query_count,
        witness.raw_queries.len(),
    )?;
    require_count(
        "FRI position layers",
        profile.layer_count(),
        witness.fri_positions.len(),
    )?;
    require_count(
        "FRI offset layers",
        profile.layer_count(),
        witness.fri_offsets.len(),
    )?;
    for (layer, positions) in witness.fri_positions.iter().enumerate() {
        if positions.len() != profile.query_count {
            return Err(FriVerifierCircuitError::LayerRouteCountMismatch {
                field: "FRI positions",
                layer,
                expected: profile.query_count,
                actual: positions.len(),
            });
        }
    }
    for (layer, offsets) in witness.fri_offsets.iter().enumerate() {
        if offsets.len() != profile.query_count {
            return Err(FriVerifierCircuitError::LayerRouteCountMismatch {
                field: "FRI offsets",
                layer,
                expected: profile.query_count,
                actual: offsets.len(),
            });
        }
    }
    require_count(
        "last-layer positions",
        profile.query_count,
        witness.last_layer_positions.len(),
    )?;
    require_count(
        "last-layer coefficients",
        profile.last_layer_coefficient_count,
        witness.last_layer_coefficients.len(),
    )
}

fn require_count(
    field: &'static str,
    expected: usize,
    actual: usize,
) -> Result<(), FriVerifierCircuitError> {
    if expected == actual {
        Ok(())
    } else {
        Err(FriVerifierCircuitError::WitnessCountMismatch {
            field,
            expected,
            actual,
        })
    }
}

fn reconstruct_bits(bits: &[Rec]) -> Rec {
    bits.iter()
        .enumerate()
        .fold(Rec::zero(), |sum, (bit, value)| {
            sum + value.clone() * BaseField::from(1_u32 << bit)
        })
}

fn select_offset(values: &[Rec], bits: &[Rec]) -> Rec {
    values
        .iter()
        .enumerate()
        .fold(Rec::zero(), |selected, (offset, value)| {
            let selector = bits
                .iter()
                .enumerate()
                .fold(Rec::one(), |selector, (bit, input)| {
                    if (offset >> bit) & 1 == 1 {
                        selector * input.clone()
                    } else {
                        selector * (Rec::one() - input.clone())
                    }
                });
            selected + selector * value.clone()
        })
}

fn circle_domain_point(bits: &[Rec], log_size: u32) -> CircuitPoint {
    let half_coset = stwo::core::poly::circle::CanonicCoset::new(log_size)
        .circle_domain()
        .half_coset;
    let mut point = CircuitPoint {
        x: Rec::from(half_coset.initial.x),
        y: Rec::from(half_coset.initial.y),
    };
    // In bit-reversed order, source bit zero selects the conjugate half and
    // each remaining source bit selects a descending half-coset step power.
    for (source_bit, bit) in bits.iter().enumerate().take(log_size as usize).skip(1) {
        let scalar = 1_usize << (log_size as usize - 1 - source_bit);
        let contribution = (half_coset.step_size * scalar).to_point();
        let selected = CircuitPoint {
            x: Rec::one() + bit.clone() * (Rec::from(contribution.x) - Rec::one()),
            y: bit.clone() * contribution.y,
        };
        point = circle_add(point, selected);
    }
    point.y *= Rec::one() - (bits[0].clone() + bits[0].clone());
    point
}

fn line_domain_point(bits: &[Rec], log_size: u32) -> CircuitPoint {
    // `half_odds(log_size)` is the first half of the canonical circle domain
    // one level larger. A leading zero keeps bit reversal in that half.
    let mut circle_bits = Vec::with_capacity(bits.len() + 1);
    circle_bits.push(Rec::zero());
    circle_bits.extend_from_slice(bits);
    circle_domain_point(&circle_bits, log_size + 1)
}

fn circle_add(lhs: CircuitPoint, rhs: CircuitPoint) -> CircuitPoint {
    CircuitPoint {
        x: lhs.x.clone() * rhs.x.clone() - lhs.y.clone() * rhs.y.clone(),
        y: lhs.x * rhs.y + lhs.y * rhs.x,
    }
}

fn circle_double(point: CircuitPoint) -> CircuitPoint {
    CircuitPoint {
        x: point.x.clone() * point.x.clone() * BaseField::from(2) - Rec::one(),
        y: point.x * point.y * BaseField::from(2),
    }
}

fn add_constant_point(point: CircuitPoint, offset: CirclePointIndex) -> CircuitPoint {
    let offset = offset.to_point();
    circle_add(
        point,
        CircuitPoint {
            x: Rec::from(offset.x),
            y: Rec::from(offset.y),
        },
    )
}

fn fold_pair(lhs: Rec, rhs: Rec, inverse_twiddle: Rec, alpha: Rec) -> Rec {
    let even = lhs.clone() + rhs.clone();
    let odd = (lhs - rhs) * inverse_twiddle;
    even + alpha * odd
}

fn fold_circle_subset(values: &[Rec], initial: CircuitPoint, fold_step: u32, alpha: Rec) -> Rec {
    let first_log = fold_step - 1;
    let mut line_values = Vec::with_capacity(values.len() / 2);
    for (pair, chunk) in values.chunks_exact(2).enumerate() {
        let reversed = stwo::core::utils::bit_reverse_index(pair, first_log);
        let offset = CirclePointIndex::subgroup_gen(first_log) * reversed;
        let point = add_constant_point(initial.clone(), offset);
        line_values.push(fold_pair(
            chunk[0].clone(),
            chunk[1].clone(),
            point.y.inverse(),
            alpha.clone(),
        ));
    }
    if fold_step == 1 {
        line_values[0].clone()
    } else {
        fold_coset(line_values, initial, fold_step - 1, alpha.clone() * alpha)
    }
}

fn fold_line_subset(values: &[Rec], initial: CircuitPoint, fold_step: u32, alpha: Rec) -> Rec {
    fold_coset(values.to_vec(), initial, fold_step, alpha)
}

fn fold_coset(
    mut values: Vec<Rec>,
    mut initial: CircuitPoint,
    log_size: u32,
    mut alpha: Rec,
) -> Rec {
    let mut current_log = log_size;
    while current_log > 0 {
        let current_len = 1_usize << current_log;
        for pair in 0..current_len / 2 {
            let source = pair * 2;
            let reversed = stwo::core::utils::bit_reverse_index(source, current_log);
            let offset = CirclePointIndex::subgroup_gen(current_log) * reversed;
            let point = add_constant_point(initial.clone(), offset);
            values[pair] = fold_pair(
                values[source].clone(),
                values[source + 1].clone(),
                point.x.inverse(),
                alpha.clone(),
            );
        }
        alpha = alpha.clone() * alpha;
        initial = circle_double(initial);
        current_log -= 1;
    }
    values[0].clone()
}

fn evaluate_last_layer(coefficients: &[Rec], mut x: Rec) -> Rec {
    let mut factors = Vec::with_capacity(coefficients.len().ilog2() as usize);
    for _ in 0..coefficients.len().ilog2() {
        factors.push(x.clone());
        x = x.clone() * x * BaseField::from(2) - Rec::one();
    }
    let mut values = coefficients.to_vec();
    for factor in factors.into_iter().rev() {
        values = values
            .chunks_exact(2)
            .map(|pair| pair[0].clone() + factor.clone() * pair[1].clone())
            .collect();
    }
    values[0].clone()
}

fn secure_from_words(words: [Rec; SECURE_EXTENSION_DEGREE]) -> Rec {
    let [a, b, c, d] = words;
    a + b * secure_basis(1) + c * secure_basis(2) + d * secure_basis(3)
}

fn secure_basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        M31::from(u32::from(limb == index))
    }))
}

fn checked_u32(field: &'static str, value: usize) -> Result<u32, FriVerifierCircuitError> {
    u32::try_from(value).map_err(|_| FriVerifierCircuitError::IndexOutOfRange { field, value })
}

/// Invalid fixed FRI geometry or per-proof assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FriVerifierCircuitError {
    LiftingLogSizeOutOfRange {
        lifting_log_size: u32,
    },
    ZeroQueries,
    ZeroLayers,
    InvalidDegreeRange {
        lifting_log_size: u32,
        log_blowup_factor: u32,
        log_last_layer_degree_bound: u32,
    },
    InvalidFoldWidth {
        layer: usize,
        width: u32,
    },
    FoldCountMismatch {
        expected: u32,
        actual: u32,
    },
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
    LayerValueCountMismatch {
        layer: usize,
        expected: usize,
        actual: usize,
    },
    LayerRouteCountMismatch {
        field: &'static str,
        layer: usize,
        expected: usize,
        actual: usize,
    },
    Shape(ProofShapeError),
}

impl fmt::Display for FriVerifierCircuitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FriVerifierCircuitError {}

#[cfg(test)]
mod tests {
    use num_traits::One;
    use rstest::rstest;
    use stwo::core::circle::Coset;
    use stwo::core::fri::{fold_circle_into_line, fold_coset};
    use stwo::core::poly::circle::{CanonicCoset, CircleDomain};
    use stwo::core::poly::line::{LineDomain, LinePoly};
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

    #[rstest]
    #[case(4, 0)]
    #[case(5, 18)]
    #[case(12, 2_731)]
    fn circle_domain_point_matches_stwo(#[case] log_size: u32, #[case] position: u32) {
        let bits = (0..log_size)
            .map(|bit| Rec::from(BaseField::from((position >> bit) & 1)))
            .collect::<Vec<_>>();
        let actual = circle_domain_point(&bits, log_size);
        let expected = CanonicCoset::new(log_size)
            .circle_domain()
            .at(bit_reverse_index(position as usize, log_size));
        assert_eq!(
            (actual.x.value(), actual.y.value()),
            (expected.x.into(), expected.y.into())
        );
    }

    #[rstest]
    #[case(3, 0)]
    #[case(4, 11)]
    #[case(9, 307)]
    fn line_domain_point_matches_stwo(#[case] log_size: u32, #[case] position: u32) {
        let bits = (0..log_size)
            .map(|bit| Rec::from(BaseField::from((position >> bit) & 1)))
            .collect::<Vec<_>>();
        let actual = line_domain_point(&bits, log_size);
        let domain = LineDomain::new(Coset::half_odds(log_size));
        let expected_index = bit_reverse_index(position as usize, log_size);
        assert_eq!(
            actual.x.value(),
            SecureField::from(domain.at(expected_index))
        );
    }

    struct Fixture {
        profile: FriVerifierProfile,
        deep_answers: Vec<SecureField>,
        values: Vec<Vec<SecureField>>,
        alphas: Vec<SecureField>,
        raw_queries: Vec<M31Word>,
        positions: Vec<Vec<M31Word>>,
        offsets: Vec<Vec<M31Word>>,
        last_positions: Vec<M31Word>,
        coefficients: Vec<SecureField>,
    }

    impl Fixture {
        fn circuit(&self) -> FriVerifierCircuit {
            build_fri_verifier_circuit(
                &self.profile,
                FriVerifierWitness {
                    active: true,
                    deep_answers: &self.deep_answers,
                    authenticated_values: &self.values,
                    fri_alphas: &self.alphas,
                    raw_queries: &self.raw_queries,
                    fri_positions: &self.positions,
                    fri_offsets: &self.offsets,
                    last_layer_positions: &self.last_positions,
                    last_layer_coefficients: &self.coefficients,
                },
            )
            .expect("fixture FRI circuit is constructible")
        }
    }

    fn fixture() -> Fixture {
        let profile = FriVerifierProfile::new(8, 1, 2, vec![4, 4, 2], 1)
            .expect("fixture FRI profile is valid");
        let raw = 93_u32;
        let deep_answer = secure(101);
        let alphas = vec![secure(131), secure(151), secure(173)];
        let mut values = Vec::new();
        let mut positions = Vec::new();
        let mut offsets = Vec::new();
        let mut previous = deep_answer;
        let mut folded_bits = 0_u32;
        let mut current_log = profile.lifting_log_size;
        for (layer, (&fold_step, &width)) in profile
            .fold_steps
            .iter()
            .zip(&profile.fold_widths)
            .enumerate()
        {
            let current_position = raw >> folded_bits;
            let offset = current_position & ((1 << fold_step) - 1);
            let subset_start = current_position & !((1 << fold_step) - 1);
            let mut subset = (0..width)
                .map(|index| secure(211 + layer as u32 * 31 + index as u32 * 5))
                .collect::<Vec<_>>();
            subset[offset as usize] = previous;
            let initial_index = bit_reverse_index(subset_start as usize, current_log);
            previous = if layer == 0 {
                let source = CanonicCoset::new(current_log).circle_domain();
                let initial = source.index_at(initial_index);
                let circle_domain = CircleDomain::new(Coset::new(initial, fold_step - 1));
                let line = fold_circle_into_line(&subset, circle_domain, alphas[layer]);
                if fold_step == 1 {
                    line[0]
                } else {
                    fold_coset(
                        line,
                        LineDomain::new(Coset::new(initial, fold_step - 1)),
                        alphas[layer] * alphas[layer],
                    )
                }
            } else {
                let source = LineDomain::new(Coset::half_odds(current_log));
                let initial = source.coset().index_at(initial_index);
                fold_coset(
                    subset.clone(),
                    LineDomain::new(Coset::new(initial, fold_step)),
                    alphas[layer],
                )
            };
            values.push(subset);
            positions.push(vec![
                M31Word::try_from(current_position).expect("position is canonical"),
            ]);
            offsets.push(vec![
                M31Word::try_from(offset).expect("offset is canonical"),
            ]);
            folded_bits += fold_step;
            current_log -= fold_step;
        }
        let last_position = raw >> folded_bits;
        let mut coefficients = vec![SecureField::zero(); profile.last_layer_coefficient_count];
        coefficients[0] = previous;
        Fixture {
            profile,
            deep_answers: vec![deep_answer],
            values,
            alphas,
            raw_queries: vec![M31Word::try_from(raw).expect("raw query is canonical")],
            positions,
            offsets,
            last_positions: vec![
                M31Word::try_from(last_position).expect("last position is canonical"),
            ],
            coefficients,
        }
    }

    #[rstest]
    fn circuit_matches_stwo_folds_and_last_layer() {
        assert_eq!(fixture().circuit().nonzero_output_count(), 0);
    }

    #[rstest]
    #[case(3_u32, 5_u32)]
    #[case(4_u32, 11_u32)]
    fn last_layer_evaluation_matches_stwo(#[case] log_size: u32, #[case] position: u32) {
        let coefficients = (0..1 << log_size)
            .map(|index| secure(401 + index as u32 * 7))
            .collect::<Vec<_>>();
        let x = LineDomain::new(Coset::half_odds(log_size + 2))
            .at(bit_reverse_index(position as usize, log_size + 2));
        let actual = evaluate_last_layer(
            &coefficients
                .iter()
                .copied()
                .map(Rec::from)
                .collect::<Vec<_>>(),
            Rec::from(x),
        );
        assert_eq!(
            actual.value(),
            LinePoly::new(coefficients).eval_at_point(x.into())
        );
    }

    #[rstest]
    fn changed_authenticated_value_breaks_the_fold_chain() {
        let mut fixture = fixture();
        fixture.values[1][0] += SecureField::one();
        assert!(fixture.circuit().nonzero_output_count() > 0);
    }

    #[rstest]
    fn changed_routed_offset_breaks_the_circuit() {
        let mut fixture = fixture();
        fixture.offsets[2][0] = M31Word::ZERO;
        assert!(fixture.circuit().nonzero_output_count() > 0);
    }

    #[rstest]
    fn changed_last_layer_coefficient_breaks_the_circuit() {
        let mut fixture = fixture();
        fixture.coefficients[0] += SecureField::one();
        assert_eq!(fixture.circuit().nonzero_output_count(), 1);
    }

    #[rstest]
    fn inactive_reference_keeps_the_full_graph_satisfied() {
        let profile = fixture().profile;
        assert_eq!(
            build_fri_verifier_reference(&profile)
                .expect("inactive FRI reference is constructible")
                .nonzero_output_count(),
            0
        );
    }
}
