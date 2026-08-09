//! Trusted operation schedule for the shared recursion verifier kernel.
//!
//! The proof supplies values only. This module derives every mandatory
//! verifier phase, repetition count, tree path, FRI fold, and relation close
//! from a validated manifest shape. Native execution and the universal AIR
//! consume this same ordered plan, whose digest is bound by the AIR program
//! identity. A missing or reordered operation therefore changes a fixed
//! control row instead of silently shortening verification.

use core::fmt;

use air::digest::{Digest8, M31Word};
use prover::poseidon2_channel::poseidon2_hash_m31_words;

use super::protocol::{
    CanonicalWords, FixedProofShape, PcsParameterError, PcsParameters, ProofShapeError,
    ValidatedProtocolManifest, fri_query_path_depth,
};

const VM_PLAN_HASH_DOMAIN: u16 = 0x564d;
const RECURSION_PLAN_HASH_DOMAIN: u16 = 0x5243;
const POSEIDON2_PLAN_HASH_DOMAIN: u16 = 0x5032;
const PLAN_ENCODING_TAG: u16 = 0x5001;
const QUERY_WORDS_PER_DRAW: usize = 8;
const COMMITMENT_TREE_COUNT: usize = 4;
const MAX_PROGRAM_PHASE_COUNT: u32 = 1_000_000;

/// Which fixed AIR schema one verifier invocation executes.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(u16)]
pub enum VerifierSchema {
    Vm = 1,
    Recursion = 2,
    Poseidon2 = 3,
}

impl VerifierSchema {
    const fn hash_domain(self) -> u16 {
        match self {
            Self::Vm => VM_PLAN_HASH_DOMAIN,
            Self::Recursion => RECURSION_PLAN_HASH_DOMAIN,
            Self::Poseidon2 => POSEIDON2_PLAN_HASH_DOMAIN,
        }
    }
}

/// Semantic transcript round for each fixed trace commitment tree.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
#[repr(u16)]
pub enum CommitmentRound {
    Preprocessed = 1,
    Main = 2,
    Interaction = 3,
    Composition = 4,
}

/// Counts owned by the generated AIR program rather than proof bytes.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct VerifierProgramSpec {
    schema: VerifierSchema,
    relation_challenge_count: u32,
    public_logup_term_count: u32,
    air_instruction_count: u32,
    relation_closure_count: u32,
}

impl VerifierProgramSpec {
    pub fn new(
        schema: VerifierSchema,
        relation_challenge_count: u32,
        public_logup_term_count: u32,
        air_instruction_count: u32,
        relation_closure_count: u32,
    ) -> Result<Self, VerifierPlanError> {
        for (field, value) in [
            ("relation challenges", relation_challenge_count),
            ("AIR instructions", air_instruction_count),
            ("relation closures", relation_closure_count),
        ] {
            if value == 0 {
                return Err(VerifierPlanError::ZeroProgramCount { field });
            }
            if value > MAX_PROGRAM_PHASE_COUNT {
                return Err(VerifierPlanError::ProgramCountOutOfRange { field, value });
            }
        }
        if schema == VerifierSchema::Vm && public_logup_term_count == 0 {
            return Err(VerifierPlanError::ZeroProgramCount {
                field: "public LogUp terms",
            });
        }
        if public_logup_term_count > MAX_PROGRAM_PHASE_COUNT {
            return Err(VerifierPlanError::ProgramCountOutOfRange {
                field: "public LogUp terms",
                value: public_logup_term_count,
            });
        }
        Ok(Self {
            schema,
            relation_challenge_count,
            public_logup_term_count,
            air_instruction_count,
            relation_closure_count,
        })
    }

    pub const fn schema(self) -> VerifierSchema {
        self.schema
    }
}

/// One mandatory control event in transcript and verification order.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum VerifierStep {
    BindProtocol,
    BindStatement,
    BindPcsParameters,
    AbsorbTraceCommitment {
        round: CommitmentRound,
        tree: u32,
        height: u32,
    },
    AbsorbPublicClaim,
    DrawInteractionSeed,
    AbsorbJointInteractionSeeds,
    AbsorbJointInteractionNonce {
        bits: u32,
    },
    VerifyAndAbsorbInteractionPow {
        bits: u32,
    },
    DrawRelationChallenge {
        challenge: u32,
    },
    AbsorbClaimedSums {
        count: u32,
    },
    DrawCompositionRandomness,
    DrawOodsPoint,
    AccumulatePublicLogupTerm {
        term: u32,
    },
    AssertVmSharedRelation,
    AssertSegmentSharedRelationZero,
    AbsorbSharedRelationSum,
    AssertGlobalLogupZero,
    EvaluateAirInstruction {
        instruction: u32,
    },
    AssertComposition {
        sampled_value_count: u32,
    },
    AbsorbSampledValues {
        count: u32,
    },
    DrawDeepRandomness,
    AbsorbFriCommitment {
        layer: u32,
    },
    DrawFriAlpha {
        layer: u32,
    },
    AbsorbLastLayerCoefficients {
        count: u32,
    },
    VerifyAndAbsorbPcsPow {
        bits: u32,
    },
    DrawQueryBlock {
        block: u32,
        first_query: u32,
        query_count: u32,
    },
    VerifyTraceMerklePath {
        tree: u32,
        query: u32,
        depth: u32,
    },
    EvaluateDeepQuotient {
        query: u32,
        queried_values_per_query: u32,
    },
    VerifyFriMerklePath {
        layer: u32,
        query: u32,
        depth: u32,
        width: u32,
    },
    FoldFri {
        layer: u32,
        query: u32,
        width: u32,
    },
    VerifyLastLayer {
        query: u32,
    },
    CloseRelation {
        relation: u32,
    },
    Complete,
}

/// Fixed-width control encoding of one verifier step.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct EncodedVerifierStep {
    tag: u32,
    args: [u32; 4],
    arity: u8,
}

impl EncodedVerifierStep {
    pub const fn tag(self) -> u32 {
        self.tag
    }

    pub const fn args(self) -> [u32; 4] {
        self.args
    }

    pub const fn arity(self) -> u8 {
        self.arity
    }
}

impl VerifierStep {
    /// Encodes the step with zero-filled unused arguments for fixed control rows.
    pub const fn encode(self) -> EncodedVerifierStep {
        macro_rules! step {
            ($tag:expr) => {
                EncodedVerifierStep {
                    tag: $tag,
                    args: [0, 0, 0, 0],
                    arity: 0,
                }
            };
            ($tag:expr, $arg_0:expr) => {
                EncodedVerifierStep {
                    tag: $tag,
                    args: [$arg_0, 0, 0, 0],
                    arity: 1,
                }
            };
            ($tag:expr, $arg_0:expr, $arg_1:expr) => {
                EncodedVerifierStep {
                    tag: $tag,
                    args: [$arg_0, $arg_1, 0, 0],
                    arity: 2,
                }
            };
            ($tag:expr, $arg_0:expr, $arg_1:expr, $arg_2:expr) => {
                EncodedVerifierStep {
                    tag: $tag,
                    args: [$arg_0, $arg_1, $arg_2, 0],
                    arity: 3,
                }
            };
            ($tag:expr, $arg_0:expr, $arg_1:expr, $arg_2:expr, $arg_3:expr) => {
                EncodedVerifierStep {
                    tag: $tag,
                    args: [$arg_0, $arg_1, $arg_2, $arg_3],
                    arity: 4,
                }
            };
        }
        match self {
            Self::BindProtocol => step!(1),
            Self::BindStatement => step!(2),
            Self::BindPcsParameters => step!(3),
            Self::AbsorbTraceCommitment {
                round,
                tree,
                height,
            } => step!(4, round as u32, tree, height),
            Self::AbsorbPublicClaim => step!(5),
            Self::VerifyAndAbsorbInteractionPow { bits } => step!(6, bits),
            Self::DrawRelationChallenge { challenge } => step!(7, challenge),
            Self::AbsorbClaimedSums { count } => step!(8, count),
            Self::DrawCompositionRandomness => step!(9),
            Self::DrawOodsPoint => step!(10),
            Self::AccumulatePublicLogupTerm { term } => step!(11, term),
            Self::AssertGlobalLogupZero => step!(12),
            Self::EvaluateAirInstruction { instruction } => step!(13, instruction),
            Self::AssertComposition {
                sampled_value_count,
            } => step!(14, sampled_value_count),
            Self::AbsorbSampledValues { count } => step!(15, count),
            Self::DrawDeepRandomness => step!(16),
            Self::AbsorbFriCommitment { layer } => step!(17, layer),
            Self::DrawFriAlpha { layer } => step!(18, layer),
            Self::AbsorbLastLayerCoefficients { count } => step!(19, count),
            Self::VerifyAndAbsorbPcsPow { bits } => step!(20, bits),
            Self::DrawQueryBlock {
                block,
                first_query,
                query_count,
            } => step!(21, block, first_query, query_count),
            Self::VerifyTraceMerklePath { tree, query, depth } => {
                step!(22, tree, query, depth)
            }
            Self::EvaluateDeepQuotient {
                query,
                queried_values_per_query,
            } => step!(23, query, queried_values_per_query),
            Self::VerifyFriMerklePath {
                layer,
                query,
                depth,
                width,
            } => step!(24, layer, query, depth, width),
            Self::FoldFri {
                layer,
                query,
                width,
            } => step!(25, layer, query, width),
            Self::VerifyLastLayer { query } => step!(26, query),
            Self::CloseRelation { relation } => step!(27, relation),
            Self::Complete => step!(28),
            Self::DrawInteractionSeed => step!(29),
            Self::AbsorbJointInteractionSeeds => step!(30),
            Self::AbsorbJointInteractionNonce { bits } => step!(31, bits),
            Self::AssertVmSharedRelation => step!(32),
            Self::AssertSegmentSharedRelationZero => step!(33),
            Self::AbsorbSharedRelationSum => step!(34),
        }
    }
}

/// Exact trusted schedule consumed by both verifier backends.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifierControlPlan {
    schema: VerifierSchema,
    pcs: PcsParameters,
    canonical_prefix: Vec<M31Word>,
    steps: Vec<VerifierStep>,
}

impl VerifierControlPlan {
    pub fn new<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
        spec: VerifierProgramSpec,
        pcs: PcsParameters,
        shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    ) -> Result<Self, VerifierPlanError> {
        if N_TREES != COMMITMENT_TREE_COUNT {
            return Err(VerifierPlanError::CommitmentTreeCount {
                expected: COMMITMENT_TREE_COUNT,
                actual: N_TREES,
            });
        }
        let validated_pcs = pcs.validate().map_err(VerifierPlanError::Pcs)?;
        shape
            .validate(validated_pcs)
            .map_err(VerifierPlanError::Shape)?;

        let config = validated_pcs.config();
        let n_queries = config.fri_config.n_queries;
        let queried_values = word_as_usize("queried values", shape.queried_value_count)?;
        let queried_values_per_query = queried_values / n_queries;
        let mut steps = Vec::new();
        steps.extend([
            VerifierStep::BindProtocol,
            VerifierStep::BindStatement,
            VerifierStep::BindPcsParameters,
            commitment_step(shape, CommitmentRound::Preprocessed, 0),
            commitment_step(shape, CommitmentRound::Main, 1),
            VerifierStep::AbsorbPublicClaim,
        ]);
        match spec.schema {
            VerifierSchema::Vm => steps.extend([
                VerifierStep::DrawInteractionSeed,
                VerifierStep::AbsorbJointInteractionSeeds,
                VerifierStep::VerifyAndAbsorbInteractionPow {
                    bits: validated_pcs.interaction_pow_bits(),
                },
            ]),
            VerifierSchema::Poseidon2 => steps.extend([
                VerifierStep::DrawInteractionSeed,
                VerifierStep::AbsorbJointInteractionSeeds,
                VerifierStep::AbsorbJointInteractionNonce {
                    bits: validated_pcs.interaction_pow_bits(),
                },
            ]),
            VerifierSchema::Recursion => {
                steps.push(VerifierStep::VerifyAndAbsorbInteractionPow {
                    bits: validated_pcs.interaction_pow_bits(),
                });
            }
        }
        if spec.schema != VerifierSchema::Poseidon2 {
            for challenge in 0..spec.relation_challenge_count {
                steps.push(VerifierStep::DrawRelationChallenge { challenge });
            }
        }
        for term in 0..spec.public_logup_term_count {
            steps.push(VerifierStep::AccumulatePublicLogupTerm { term });
        }
        match spec.schema {
            VerifierSchema::Vm => steps.extend([
                VerifierStep::AssertVmSharedRelation,
                VerifierStep::AssertSegmentSharedRelationZero,
            ]),
            VerifierSchema::Recursion => steps.push(VerifierStep::AssertGlobalLogupZero),
            VerifierSchema::Poseidon2 => {}
        }
        steps.push(VerifierStep::AbsorbClaimedSums {
            count: shape.claimed_sum_count.as_u32(),
        });
        if spec.schema == VerifierSchema::Vm {
            steps.push(VerifierStep::AbsorbSharedRelationSum);
        }
        steps.extend([
            commitment_step(shape, CommitmentRound::Interaction, 2),
            VerifierStep::DrawCompositionRandomness,
            commitment_step(shape, CommitmentRound::Composition, 3),
            VerifierStep::DrawOodsPoint,
        ]);
        for instruction in 0..spec.air_instruction_count {
            steps.push(VerifierStep::EvaluateAirInstruction { instruction });
        }
        steps.extend([
            VerifierStep::AssertComposition {
                sampled_value_count: shape.sampled_value_count.as_u32(),
            },
            VerifierStep::AbsorbSampledValues {
                count: shape.sampled_value_count.as_u32(),
            },
            VerifierStep::DrawDeepRandomness,
        ]);
        for layer in 0..N_FRI_LAYERS {
            let layer = u32::try_from(layer).map_err(|_| VerifierPlanError::IndexOutOfRange {
                field: "FRI layer",
                value: layer,
            })?;
            steps.extend([
                VerifierStep::AbsorbFriCommitment { layer },
                VerifierStep::DrawFriAlpha { layer },
            ]);
        }
        steps.extend([
            VerifierStep::AbsorbLastLayerCoefficients {
                count: shape.last_layer_coefficient_count.as_u32(),
            },
            VerifierStep::VerifyAndAbsorbPcsPow {
                bits: config.pow_bits,
            },
        ]);
        append_query_draws(&mut steps, n_queries)?;
        append_trace_openings(&mut steps, shape, n_queries)?;
        let queried_values_per_query = u32::try_from(queried_values_per_query).map_err(|_| {
            VerifierPlanError::IndexOutOfRange {
                field: "queried values per query",
                value: queried_values_per_query,
            }
        })?;
        for query in 0..n_queries {
            steps.push(VerifierStep::EvaluateDeepQuotient {
                query: index_u32("raw query", query)?,
                queried_values_per_query,
            });
        }
        append_fri_checks(&mut steps, shape, n_queries)?;
        for query in 0..n_queries {
            steps.push(VerifierStep::VerifyLastLayer {
                query: index_u32("raw query", query)?,
            });
        }
        for relation in 0..spec.relation_closure_count {
            steps.push(VerifierStep::CloseRelation { relation });
        }
        steps.push(VerifierStep::Complete);

        let canonical_prefix = profile_prefix(spec.schema, pcs, shape);
        Ok(Self {
            schema: spec.schema,
            pcs,
            canonical_prefix,
            steps,
        })
    }

    pub const fn schema(&self) -> VerifierSchema {
        self.schema
    }

    /// Returns the checked PCS parameters that generated this control plan.
    pub const fn pcs_parameters(&self) -> PcsParameters {
        self.pcs
    }

    pub fn steps(&self) -> &[VerifierStep] {
        &self.steps
    }

    fn matches_profile<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
        &self,
        schema: VerifierSchema,
        pcs: PcsParameters,
        shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    ) -> bool {
        self.canonical_prefix == profile_prefix(schema, pcs, shape)
    }

    /// Hashes the exact schedule and all validated profile inputs into its AIR ID.
    pub fn digest(&self) -> Digest8 {
        let mut words = self.canonical_prefix.clone();
        words.push(canonical_usize("verifier step count", self.steps.len()));
        for step in &self.steps {
            append_step_words(*step, &mut words);
        }
        poseidon2_hash_m31_words(&words, M31Word::from(self.schema.hash_domain()))
    }

    /// Rejects any witness control stream that omits, adds, or reorders a phase.
    pub fn verify_control_trace(&self, actual: &[VerifierStep]) -> Result<(), ControlTraceError> {
        for (sequence, expected) in self.steps.iter().copied().enumerate() {
            let Some(actual) = actual.get(sequence).copied() else {
                return Err(ControlTraceError::MissingStep { sequence, expected });
            };
            if actual != expected {
                return Err(ControlTraceError::UnexpectedStep {
                    sequence,
                    expected,
                    actual,
                });
            }
        }
        if let Some(actual) = actual.get(self.steps.len()).copied() {
            return Err(ControlTraceError::ExtraStep {
                sequence: self.steps.len(),
                actual,
            });
        }
        Ok(())
    }
}

/// VM and recursion plans whose digests match one validated manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundVerifierPlans<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
> {
    manifest: ValidatedProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >,
    vm: VerifierControlPlan,
    poseidon2: VerifierControlPlan,
    recursion: VerifierControlPlan,
}

impl<
    const VM_TABLES: usize,
    const VM_TREES: usize,
    const VM_FRI_LAYERS: usize,
    const RECURSION_TABLES: usize,
    const RECURSION_TREES: usize,
    const RECURSION_FRI_LAYERS: usize,
>
    BoundVerifierPlans<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    >
{
    pub fn new(
        manifest: ValidatedProtocolManifest<
            VM_TABLES,
            VM_TREES,
            VM_FRI_LAYERS,
            RECURSION_TABLES,
            RECURSION_TREES,
            RECURSION_FRI_LAYERS,
        >,
        vm: VerifierControlPlan,
        poseidon2: VerifierControlPlan,
        recursion: VerifierControlPlan,
    ) -> Result<Self, PlanBindingError> {
        if vm.schema() != VerifierSchema::Vm {
            return Err(PlanBindingError::SchemaMismatch {
                slot: VerifierSchema::Vm,
                actual: vm.schema(),
            });
        }
        if recursion.schema() != VerifierSchema::Recursion {
            return Err(PlanBindingError::SchemaMismatch {
                slot: VerifierSchema::Recursion,
                actual: recursion.schema(),
            });
        }
        if poseidon2.schema() != VerifierSchema::Poseidon2 {
            return Err(PlanBindingError::SchemaMismatch {
                slot: VerifierSchema::Poseidon2,
                actual: poseidon2.schema(),
            });
        }
        if !vm.matches_profile(
            VerifierSchema::Vm,
            manifest.manifest().vm_pcs,
            &manifest.manifest().vm_proof_shape,
        ) {
            return Err(PlanBindingError::ProfileMismatch {
                schema: VerifierSchema::Vm,
            });
        }
        if !recursion.matches_profile(
            VerifierSchema::Recursion,
            manifest.manifest().recursion_pcs,
            &manifest.manifest().recursion_proof_shape,
        ) {
            return Err(PlanBindingError::ProfileMismatch {
                schema: VerifierSchema::Recursion,
            });
        }

        let expected_vm = manifest.manifest().vm_air_program.into_digest();
        let actual_vm = vm.digest();
        if actual_vm != expected_vm {
            return Err(PlanBindingError::AirProgramDigestMismatch {
                schema: VerifierSchema::Vm,
                expected: expected_vm,
                actual: actual_vm,
            });
        }
        let expected_recursion = manifest.manifest().recursion_air_program.into_digest();
        let actual_recursion = recursion.digest();
        if actual_recursion != expected_recursion {
            return Err(PlanBindingError::AirProgramDigestMismatch {
                schema: VerifierSchema::Recursion,
                expected: expected_recursion,
                actual: actual_recursion,
            });
        }
        let expected_poseidon2 = manifest.manifest().poseidon2_air_program.into_digest();
        let actual_poseidon2 = poseidon2.digest();
        if actual_poseidon2 != expected_poseidon2 {
            return Err(PlanBindingError::AirProgramDigestMismatch {
                schema: VerifierSchema::Poseidon2,
                expected: expected_poseidon2,
                actual: actual_poseidon2,
            });
        }
        Ok(Self {
            manifest,
            vm,
            poseidon2,
            recursion,
        })
    }

    pub const fn manifest(
        &self,
    ) -> &ValidatedProtocolManifest<
        VM_TABLES,
        VM_TREES,
        VM_FRI_LAYERS,
        RECURSION_TABLES,
        RECURSION_TREES,
        RECURSION_FRI_LAYERS,
    > {
        &self.manifest
    }

    pub const fn vm(&self) -> &VerifierControlPlan {
        &self.vm
    }

    pub const fn recursion(&self) -> &VerifierControlPlan {
        &self.recursion
    }

    pub const fn poseidon2(&self) -> &VerifierControlPlan {
        &self.poseidon2
    }
}

fn profile_prefix<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    schema: VerifierSchema,
    pcs: PcsParameters,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
) -> Vec<M31Word> {
    let mut words = vec![
        M31Word::from(PLAN_ENCODING_TAG),
        M31Word::from(schema as u16),
    ];
    pcs.append_canonical_words(&mut words);
    shape.append_canonical_words(&mut words);
    words
}

fn commitment_step<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    round: CommitmentRound,
    tree: usize,
) -> VerifierStep {
    VerifierStep::AbsorbTraceCommitment {
        round,
        tree: tree as u32,
        height: shape.tree_heights[tree].as_u32(),
    }
}

fn append_query_draws(
    steps: &mut Vec<VerifierStep>,
    n_queries: usize,
) -> Result<(), VerifierPlanError> {
    let mut first_query = 0;
    let mut block = 0;
    while first_query < n_queries {
        let query_count = (n_queries - first_query).min(QUERY_WORDS_PER_DRAW);
        steps.push(VerifierStep::DrawQueryBlock {
            block: index_u32("query draw block", block)?,
            first_query: index_u32("raw query", first_query)?,
            query_count: index_u32("query draw width", query_count)?,
        });
        first_query += query_count;
        block += 1;
    }
    Ok(())
}

fn append_trace_openings<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    steps: &mut Vec<VerifierStep>,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    n_queries: usize,
) -> Result<(), VerifierPlanError> {
    for tree in 0..N_TREES {
        if shape.tree_heights[tree] == M31Word::ZERO {
            continue;
        }
        for query in 0..n_queries {
            steps.push(VerifierStep::VerifyTraceMerklePath {
                tree: index_u32("commitment tree", tree)?,
                query: index_u32("raw query", query)?,
                depth: shape.tree_heights[tree].as_u32(),
            });
        }
    }
    Ok(())
}

fn append_fri_checks<const N_TABLES: usize, const N_TREES: usize, const N_FRI_LAYERS: usize>(
    steps: &mut Vec<VerifierStep>,
    shape: &FixedProofShape<N_TABLES, N_TREES, N_FRI_LAYERS>,
    n_queries: usize,
) -> Result<(), VerifierPlanError> {
    for layer in 0..N_FRI_LAYERS {
        let layer_index = index_u32("FRI layer", layer)?;
        let width = shape.fri_layer_fold_widths[layer].as_u32();
        let depth = fri_query_path_depth(shape.fri_layer_tree_heights[layer].as_u32(), width)
            .expect("validated FRI shape has an authentication path depth");
        for query in 0..n_queries {
            let query = index_u32("raw query", query)?;
            steps.extend([
                VerifierStep::VerifyFriMerklePath {
                    layer: layer_index,
                    query,
                    depth,
                    width,
                },
                VerifierStep::FoldFri {
                    layer: layer_index,
                    query,
                    width,
                },
            ]);
        }
    }
    Ok(())
}

fn word_as_usize(field: &'static str, value: M31Word) -> Result<usize, VerifierPlanError> {
    usize::try_from(value.as_u32()).map_err(|_| VerifierPlanError::WordOutOfRange {
        field,
        value: value.as_u32(),
    })
}

fn index_u32(field: &'static str, value: usize) -> Result<u32, VerifierPlanError> {
    u32::try_from(value).map_err(|_| VerifierPlanError::IndexOutOfRange { field, value })
}

fn canonical_usize(field: &'static str, value: usize) -> M31Word {
    u32::try_from(value)
        .ok()
        .and_then(|value| M31Word::try_from(value).ok())
        .unwrap_or_else(|| panic!("{field} must fit in one canonical M31 word"))
}

fn push_step_word(words: &mut Vec<M31Word>, value: u32) {
    words.push(M31Word::try_from(value).expect("validated verifier step values fit in M31"));
}

fn append_step_words(step: VerifierStep, words: &mut Vec<M31Word>) {
    let encoded = step.encode();
    push_step_word(words, encoded.tag());
    for value in &encoded.args()[..encoded.arity() as usize] {
        push_step_word(words, *value);
    }
}

/// Invalid trusted inputs while constructing a fixed verifier plan.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifierPlanError {
    ZeroProgramCount { field: &'static str },
    ProgramCountOutOfRange { field: &'static str, value: u32 },
    CommitmentTreeCount { expected: usize, actual: usize },
    Pcs(PcsParameterError),
    Shape(ProofShapeError),
    WordOutOfRange { field: &'static str, value: u32 },
    IndexOutOfRange { field: &'static str, value: usize },
}

impl fmt::Display for VerifierPlanError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroProgramCount { field } => {
                write!(formatter, "verifier program has zero {field}")
            }
            Self::ProgramCountOutOfRange { field, value } => write!(
                formatter,
                "verifier program {field} count {value} exceeds {MAX_PROGRAM_PHASE_COUNT}"
            ),
            Self::CommitmentTreeCount { expected, actual } => write!(
                formatter,
                "verifier plan requires {expected} commitment trees, shape has {actual}"
            ),
            Self::Pcs(source) => write!(formatter, "invalid verifier PCS profile: {source}"),
            Self::Shape(source) => write!(formatter, "invalid verifier proof shape: {source}"),
            Self::WordOutOfRange { field, value } => {
                write!(formatter, "{field} value {value} does not fit usize")
            }
            Self::IndexOutOfRange { field, value } => {
                write!(formatter, "{field} index {value} does not fit u32")
            }
        }
    }
}

impl std::error::Error for VerifierPlanError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Pcs(source) => Some(source),
            Self::Shape(source) => Some(source),
            _ => None,
        }
    }
}

/// Exact reason a proposed control trace differs from the trusted schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ControlTraceError {
    MissingStep {
        sequence: usize,
        expected: VerifierStep,
    },
    UnexpectedStep {
        sequence: usize,
        expected: VerifierStep,
        actual: VerifierStep,
    },
    ExtraStep {
        sequence: usize,
        actual: VerifierStep,
    },
}

impl fmt::Display for ControlTraceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingStep { sequence, expected } => {
                write!(formatter, "missing verifier step {sequence}: {expected:?}")
            }
            Self::UnexpectedStep {
                sequence,
                expected,
                actual,
            } => write!(
                formatter,
                "verifier step {sequence} is {actual:?}, expected {expected:?}"
            ),
            Self::ExtraStep { sequence, actual } => {
                write!(formatter, "extra verifier step {sequence}: {actual:?}")
            }
        }
    }
}

impl std::error::Error for ControlTraceError {}

/// A generated plan that does not match the manifest's trusted AIR identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanBindingError {
    SchemaMismatch {
        slot: VerifierSchema,
        actual: VerifierSchema,
    },
    ProfileMismatch {
        schema: VerifierSchema,
    },
    AirProgramDigestMismatch {
        schema: VerifierSchema,
        expected: Digest8,
        actual: Digest8,
    },
}

impl fmt::Display for PlanBindingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SchemaMismatch { slot, actual } => write!(
                formatter,
                "{slot:?} verifier slot contains an {actual:?} plan"
            ),
            Self::ProfileMismatch { schema } => write!(
                formatter,
                "{schema:?} verifier plan uses PCS or shape fields different from the manifest"
            ),
            Self::AirProgramDigestMismatch { schema, .. } => {
                write!(
                    formatter,
                    "{schema:?} verifier plan digest does not match the manifest"
                )
            }
        }
    }
}

impl std::error::Error for PlanBindingError {}

#[cfg(test)]
mod tests {
    use air::digest::{
        HashSuiteDigest, Poseidon2AirProgramDigest, RecursionAirProgramDigest,
        RecursionPreprocessingDigest, VmAirProgramDigest, VmPreprocessingDigest,
    };
    use rstest::rstest;

    use super::*;
    use crate::protocol::{OptionalM31Word, ProtocolManifest, ProtocolVersion};

    type TestBoundPlans = BoundVerifierPlans<2, 4, 4, 2, 4, 4>;

    fn word(value: u16) -> M31Word {
        M31Word::from(value)
    }

    fn digest(seed: u16) -> Digest8 {
        Digest8::new([
            word(seed),
            word(seed + 1),
            word(seed + 2),
            word(seed + 3),
            word(seed + 4),
            word(seed + 5),
            word(seed + 6),
            word(seed + 7),
        ])
    }

    fn pcs() -> PcsParameters {
        PcsParameters {
            interaction_pow_bits: word(8),
            pow_bits: word(10),
            fri_log_blowup_factor: word(1),
            fri_n_queries: word(9),
            fri_log_last_layer_degree_bound: M31Word::ZERO,
            fri_fold_step: word(2),
            lifting_log_size: OptionalM31Word::Some(word(8)),
        }
    }

    fn shape() -> FixedProofShape<2, 4, 4> {
        FixedProofShape {
            claimed_sum_count: word(7),
            sampled_value_count: word(8),
            queried_value_count: word(36),
            trace_path_count: word(36),
            raw_query_count: word(9),
            last_layer_coefficient_count: word(1),
            table_log_sizes: [word(5), word(6)],
            tree_heights: [word(8), word(8), word(8), word(8)],
            fri_layer_fold_widths: [word(4), word(4), word(4), word(2)],
            fri_layer_tree_heights: [word(6), word(4), word(2), word(2)],
        }
    }

    fn plan(schema: VerifierSchema) -> VerifierControlPlan {
        plan_with_pcs(schema, pcs())
    }

    fn plan_with_pcs(schema: VerifierSchema, parameters: PcsParameters) -> VerifierControlPlan {
        let spec = VerifierProgramSpec::new(schema, 3, 5, 7, 4)
            .expect("the fixture program has every mandatory phase");
        VerifierControlPlan::new(spec, parameters, &shape())
            .expect("the fixture shape matches its PCS profile")
    }

    fn manifest(
        vm: &VerifierControlPlan,
        poseidon2: &VerifierControlPlan,
        recursion: &VerifierControlPlan,
    ) -> ProtocolManifest<2, 4, 4, 2, 4, 4> {
        ProtocolManifest {
            version: ProtocolVersion(word(2)),
            hash_suite: HashSuiteDigest::from(digest(10)),
            vm_preprocessing: VmPreprocessingDigest::from(digest(20)),
            recursion_preprocessing: RecursionPreprocessingDigest::from(digest(30)),
            vm_air_program: VmAirProgramDigest::from(vm.digest()),
            poseidon2_air_program: Poseidon2AirProgramDigest::from(poseidon2.digest()),
            recursion_air_program: RecursionAirProgramDigest::from(recursion.digest()),
            vm_pcs: pcs(),
            recursion_pcs: pcs(),
            vm_proof_shape: shape(),
            recursion_proof_shape: shape(),
        }
    }

    #[rstest]
    fn exact_control_trace_is_accepted() {
        let plan = plan(VerifierSchema::Vm);
        assert_eq!(plan.verify_control_trace(plan.steps()), Ok(()));
    }

    #[rstest]
    fn recursion_program_accepts_zero_public_logup_terms() {
        assert!(VerifierProgramSpec::new(VerifierSchema::Recursion, 3, 0, 7, 4).is_ok());
    }

    #[rstest]
    fn vm_program_rejects_zero_public_logup_terms() {
        assert_eq!(
            VerifierProgramSpec::new(VerifierSchema::Vm, 3, 0, 7, 4),
            Err(VerifierPlanError::ZeroProgramCount {
                field: "public LogUp terms"
            })
        );
    }

    #[rstest]
    fn missing_control_step_is_rejected() {
        let plan = plan(VerifierSchema::Vm);
        let truncated = &plan.steps()[..plan.steps().len() - 1];
        assert_eq!(
            plan.verify_control_trace(truncated),
            Err(ControlTraceError::MissingStep {
                sequence: truncated.len(),
                expected: VerifierStep::Complete,
            })
        );
    }

    #[rstest]
    fn reordered_control_steps_are_rejected() {
        let plan = plan(VerifierSchema::Vm);
        let mut reordered = plan.steps().to_vec();
        reordered.swap(0, 1);
        assert_eq!(
            plan.verify_control_trace(&reordered),
            Err(ControlTraceError::UnexpectedStep {
                sequence: 0,
                expected: VerifierStep::BindProtocol,
                actual: VerifierStep::BindStatement,
            })
        );
    }

    #[rstest]
    fn extra_control_step_is_rejected() {
        let plan = plan(VerifierSchema::Vm);
        let mut extended = plan.steps().to_vec();
        extended.push(VerifierStep::Complete);
        assert_eq!(
            plan.verify_control_trace(&extended),
            Err(ControlTraceError::ExtraStep {
                sequence: plan.steps().len(),
                actual: VerifierStep::Complete,
            })
        );
    }

    #[rstest]
    fn vm_and_recursion_plans_have_distinct_digests() {
        assert_ne!(
            plan(VerifierSchema::Vm).digest(),
            plan(VerifierSchema::Recursion).digest()
        );
    }

    #[rstest]
    fn query_draws_retain_the_partial_final_block() {
        let plan = plan(VerifierSchema::Vm);
        assert_eq!(
            plan.steps()
                .iter()
                .filter(|step| matches!(step, VerifierStep::DrawQueryBlock { .. }))
                .copied()
                .collect::<Vec<_>>(),
            vec![
                VerifierStep::DrawQueryBlock {
                    block: 0,
                    first_query: 0,
                    query_count: 8,
                },
                VerifierStep::DrawQueryBlock {
                    block: 1,
                    first_query: 8,
                    query_count: 1,
                },
            ]
        );
    }

    #[rstest]
    fn every_tree_and_raw_query_gets_an_independent_trace_path() {
        let plan = plan(VerifierSchema::Vm);
        assert_eq!(
            plan.steps()
                .iter()
                .filter(|step| matches!(step, VerifierStep::VerifyTraceMerklePath { .. }))
                .count(),
            36
        );
    }

    #[rstest]
    fn plan_digests_bind_to_the_validated_manifest() {
        let vm = plan(VerifierSchema::Vm);
        let poseidon2 = plan(VerifierSchema::Poseidon2);
        let recursion = plan(VerifierSchema::Recursion);
        let manifest = manifest(&vm, &poseidon2, &recursion);
        let protocol_id = manifest.protocol_id();
        assert_eq!(
            TestBoundPlans::new(
                manifest
                    .validate()
                    .expect("the fixture manifest has valid PCS shapes"),
                vm,
                poseidon2,
                recursion,
            )
            .map(|bound| bound.manifest().protocol_id()),
            Ok(protocol_id)
        );
    }

    #[rstest]
    fn substituted_air_program_digest_is_rejected() {
        let vm = plan(VerifierSchema::Vm);
        let poseidon2 = plan(VerifierSchema::Poseidon2);
        let recursion = plan(VerifierSchema::Recursion);
        let actual = vm.digest();
        let expected = digest(200);
        let mut manifest = manifest(&vm, &poseidon2, &recursion);
        manifest.vm_air_program = VmAirProgramDigest::from(expected);
        assert_eq!(
            TestBoundPlans::new(
                manifest
                    .validate()
                    .expect("the substituted digest does not change PCS geometry"),
                vm,
                poseidon2,
                recursion,
            ),
            Err(PlanBindingError::AirProgramDigestMismatch {
                schema: VerifierSchema::Vm,
                expected,
                actual,
            })
        );
    }

    #[rstest]
    fn swapped_schema_plans_are_rejected() {
        let vm = plan(VerifierSchema::Vm);
        let poseidon2 = plan(VerifierSchema::Poseidon2);
        let recursion = plan(VerifierSchema::Recursion);
        let manifest = manifest(&vm, &poseidon2, &recursion);
        assert_eq!(
            TestBoundPlans::new(
                manifest
                    .validate()
                    .expect("the fixture manifest has valid PCS shapes"),
                recursion,
                poseidon2,
                vm,
            ),
            Err(PlanBindingError::SchemaMismatch {
                slot: VerifierSchema::Vm,
                actual: VerifierSchema::Recursion,
            })
        );
    }

    #[rstest]
    fn air_plan_profile_must_match_the_manifest_profile() {
        let mut alternative_pcs = pcs();
        alternative_pcs.pow_bits = word(11);
        let vm = plan_with_pcs(VerifierSchema::Vm, alternative_pcs);
        let poseidon2 = plan(VerifierSchema::Poseidon2);
        let recursion = plan(VerifierSchema::Recursion);
        let manifest = manifest(&vm, &poseidon2, &recursion);
        assert_eq!(
            TestBoundPlans::new(
                manifest
                    .validate()
                    .expect("both individual PCS profiles are valid"),
                vm,
                poseidon2,
                recursion,
            ),
            Err(PlanBindingError::ProfileMismatch {
                schema: VerifierSchema::Vm,
            })
        );
    }
}
