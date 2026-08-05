//! Recursion AIR self-program: the universal roster evaluated as one circuit.
//!
//! This is the recursion analogue of [`super::vm_air_program::VmAirProgram`]:
//! the fixed metadata that maps STWO's flat sampled-value order back to every
//! universal component mask, plus the streaming evaluation that recomputes the
//! universal AIR's composition value from sampled values, claimed sums, and
//! transcript-bound relation parameters. A recursion lane's composition check
//! lowers this evaluation into the shared arithmetic tables, so the metadata
//! here also sizes those tables.
//!
//! The circuit path compiles each macro-generated component once through
//! `ExprEvaluator` using the same `FrameworkEval::evaluate` implementation
//! that drives proving. It then replays the resulting formal expression
//! program over circuit wires via [`super::air_expression_circuit`], avoiding
//! any separately transcribed constraint system.

use core::fmt;
use std::collections::HashMap;

use air::relation_eval::DynamicRelationFrameworkEval;
use num_traits::{One, Zero};
use stwo::core::Fraction;
use stwo::core::circle::{CirclePoint, CirclePointIndex};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::pcs::{TreeSubspan, TreeVec};
use stwo::core::poly::circle::{MAX_CIRCLE_DOMAIN_LOG_SIZE, MIN_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::prover::ComponentProver;
use stwo::prover::backend::Column;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::expr::degree::NamedExprs;
use stwo_constraint_framework::expr::{BaseExpr, ColumnExpr, ExprEvaluator};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, PREPROCESSED_TRACE_IDX, TraceLocationAllocator,
    assert_constraints_on_trace,
};

/// Measures constraints with verifier preprocessing treated as degree-one columns.
///
/// Named preprocessing expressions are otherwise unresolved by `ExprEvaluator`,
/// which would understate products that combine fixed columns with witness data.
pub(crate) fn constraint_degree_bounds_with_preprocessed(
    expressions: &ExprEvaluator,
    preprocessed: &[PreProcessedColumnId],
) -> Vec<usize> {
    let mut base_expressions = expressions.intermediates.clone();
    for (index, id) in preprocessed.iter().enumerate() {
        base_expressions.insert(
            id.id.clone(),
            BaseExpr::Col(ColumnExpr::from((PREPROCESSED_TRACE_IDX, index, 0))),
        );
    }
    let named_expressions =
        NamedExprs::new(base_expressions, expressions.ext_intermediates.clone());
    expressions
        .constraints
        .iter()
        .map(|constraint| constraint.degree_bound(&named_expressions))
        .collect()
}

use super::air_expression_circuit::{
    AirExpressionError, AirExpressionInputs, accumulate_air_constraints, evaluate_air_expressions,
};
use super::oods_circuit::{
    OodsCircuitError, OodsPointCircuit, combine_split_composition, coset_vanishing_inverse,
};
use super::universal_relations::UniversalRelations;
use super::vm_air_program::SampleCoordinate;
use super::wire::ProofKind;
use crate::recorder::Rec;

/// Number of universal components and interaction claimed sums.
pub const UNIVERSAL_COMPONENT_COUNT: usize = 36;
/// Number of split-composition coordinate samples appended by STWO.
pub const COMPOSITION_SAMPLE_COUNT: usize = 2 * SECURE_EXTENSION_DEGREE;

/// Canonical component order: commitment, interaction, and composition order.
pub const UNIVERSAL_COMPONENT_NAMES: [&str; UNIVERSAL_COMPONENT_COUNT] = [
    "control",
    "transcript_air",
    "transcript_binding",
    "transcript_state",
    "transcript_word",
    "transcript_payload",
    "pow_check",
    "pow_frame",
    "relation_challenge",
    "verifier_randomness",
    "statement_input",
    "statement_semantics_input",
    "vm_public_claim_input",
    "vm_public_claim_hash",
    "vm_public_io_hash",
    "vm_public_claim_semantics_input",
    "vm_public_logup_input",
    "vm_public_logup_control",
    "vm_air_composition_input",
    "vm_air_composition_control",
    "query_bits",
    "query_mapping",
    "merkle_root",
    "trace_merkle",
    "pcs_deep_input",
    "fri_merkle_leaf",
    "fri_merkle_node",
    "fri_merkle_anchor",
    "fri_verifier_control",
    "fri_verifier_input",
    "qm31_mul",
    "qm31_inv",
    "linear_ops",
    "merkle_path",
    "poseidon2",
    "range_check_8_8",
];

/// Per-component table log sizes in [`UNIVERSAL_COMPONENT_NAMES`] order.
pub type UniversalComponentLogSizes = [u32; UNIVERSAL_COMPONENT_COUNT];

/// Every preprocessed column the universal roster reads, in first-use order.
///
/// The allocator auto-registers columns as components ask for them, so
/// running the roster once over a dynamic allocator yields the canonical
/// preprocessed layout the program and the universal preprocessing commit
/// against. The list is deterministic: component order is fixed and every
/// component reads its own columns in declaration order.
pub fn universal_preprocessed_column_ids(
    log_sizes: &UniversalComponentLogSizes,
) -> Vec<PreProcessedColumnId> {
    let relations = UniversalRelations::dummy();
    let mut allocator = TraceLocationAllocator::default();
    let mut collector = RosterCollector::default();
    collector.push_all(
        &mut allocator,
        &relations,
        ProofKind::SegmentLeaf,
        log_sizes,
        &[SecureField::zero(); UNIVERSAL_COMPONENT_COUNT],
    );
    allocator.preprocessed_columns().clone()
}

/// Evaluates every universal component row against one assembled trace.
///
/// This is the direct witness-acceptance gate used before recursive proving:
/// each macro-generated evaluator receives its allocator-selected columns and
/// its own claimed sum, including the shared preprocessing registry.
pub fn assert_universal_constraints(
    traces: &TreeVec<Vec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>>,
    preprocessing_ids: &[PreProcessedColumnId],
    relations: &UniversalRelations,
    proof_kind: ProofKind,
    log_sizes: &UniversalComponentLogSizes,
    claimed_sums: &[SecureField; UNIVERSAL_COMPONENT_COUNT],
) -> usize {
    let cpu_traces = TreeVec::new(
        traces
            .iter()
            .map(|tree| {
                tree.iter()
                    .map(|column| column.values.to_cpu())
                    .collect::<Vec<_>>()
            })
            .collect(),
    );
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(preprocessing_ids);
    let mut collector = RosterCollector::default();
    collector.push_all(
        &mut allocator,
        relations,
        proof_kind,
        log_sizes,
        claimed_sums,
    );
    for (name, checker) in UNIVERSAL_COMPONENT_NAMES
        .iter()
        .zip(&collector.constraint_checkers)
    {
        if std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            checker.assert_constraints(&cpu_traces);
        }))
        .is_err()
        {
            panic!("universal component {name} rejected the assembled trace");
        }
    }
    collector.constraint_checkers.len()
}

/// One canonical universal roster instantiated for native proving or verification.
pub(crate) struct UniversalComponents {
    components: Vec<Box<dyn UniversalComponent>>,
}

impl UniversalComponents {
    pub(crate) fn provers(&self) -> Vec<&dyn ComponentProver<SimdBackend>> {
        self.components
            .iter()
            .map(|component| component.as_prover())
            .collect()
    }

    pub(crate) fn verifiers(&self) -> Vec<&dyn stwo::core::air::Component> {
        self.components
            .iter()
            .map(|component| component.as_verifier())
            .collect()
    }
}

/// Instantiates the same generated roster used by self-evaluation and direct checks.
pub(crate) fn universal_components(
    preprocessing_ids: &[PreProcessedColumnId],
    relations: &UniversalRelations,
    proof_kind: ProofKind,
    log_sizes: &UniversalComponentLogSizes,
    claimed_sums: &[SecureField; UNIVERSAL_COMPONENT_COUNT],
) -> UniversalComponents {
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(preprocessing_ids);
    let mut collector = RosterCollector::default();
    collector.push_all(
        &mut allocator,
        relations,
        proof_kind,
        log_sizes,
        claimed_sums,
    );
    UniversalComponents {
        components: collector.component_refs,
    }
}

/// Records the exact mask-consumption order of one component's `evaluate`.
///
/// `ExprEvaluator` indexes formal columns with a counter shared across all
/// interaction trees, so the circuit binding needs the interleaved call order
/// to map each formal column back to its tree position. Running the same
/// `evaluate` against this recorder yields the authoritative order; it also
/// replaces `InfoEvaluator` for constraint counts and preprocessed usage.
#[derive(Default)]
struct MaskConsumptionRecorder {
    consumption: Vec<(usize, Vec<isize>)>,
    preprocessed_columns: Vec<PreProcessedColumnId>,
    n_constraints: usize,
    open_fracs: usize,
}

impl MaskConsumptionRecorder {
    fn mask_offsets(&self) -> TreeVec<Vec<Vec<isize>>> {
        let mut offsets = TreeVec::new(vec![]);
        for (interaction, column) in &self.consumption {
            if offsets.len() <= *interaction {
                offsets.0.resize_with(interaction + 1, Vec::new);
            }
            offsets[*interaction].push(column.clone());
        }
        offsets
    }
}

impl EvalAtRow for MaskConsumptionRecorder {
    type F = BaseField;
    type EF = SecureField;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        self.consumption.push((interaction, offsets.to_vec()));
        [BaseField::zero(); N]
    }

    fn get_preprocessed_column(&mut self, column: PreProcessedColumnId) -> Self::F {
        self.preprocessed_columns.push(column);
        BaseField::zero()
    }

    fn add_constraint<G>(&mut self, _constraint: G)
    where
        Self::EF: core::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        self.n_constraints += 1;
    }

    fn combine_ef(_values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        SecureField::zero()
    }

    fn write_logup_frac(&mut self, _fraction: Fraction<Self::EF, Self::EF>) {
        self.open_fracs += 1;
    }

    fn finalize_logup_batched(&mut self, batching: &Vec<usize>) {
        assert_eq!(batching.len(), self.open_fracs);
        let last_batch = *batching.iter().max().expect("LogUp requires a fraction");
        for _ in 0..last_batch {
            self.next_extension_interaction_mask(
                stwo_constraint_framework::INTERACTION_TRACE_IDX,
                [0],
            );
            self.n_constraints += 1;
        }
        self.next_extension_interaction_mask(
            stwo_constraint_framework::INTERACTION_TRACE_IDX,
            [-1, 0],
        );
        self.n_constraints += 1;
        self.open_fracs = 0;
    }

    fn finalize_logup(&mut self) {
        let batches = (0..self.open_fracs).collect();
        self.finalize_logup_batched(&batches)
    }

    fn finalize_logup_in_pairs(&mut self) {
        let batches = (0..self.open_fracs).map(|index| index / 2).collect();
        self.finalize_logup_batched(&batches)
    }
}

/// How one component's composition contribution is evaluated over wires.
///
/// Every standard protocol component compiles to a formal expression program
/// once. The Poseidon2 permutation nests its round expressions without shared
/// intermediates, which makes that forest exponential, so it is evaluated
/// through its macro-generated dynamic-relation evaluator instead — the same
/// seam the VM composition circuit uses.
enum ComponentEvaluation {
    Expressions {
        expressions: Box<ExprEvaluator>,
        column_variables: HashMap<(usize, usize), usize>,
    },
    Poseidon2(Box<air::poseidon2::component::air::Eval>),
}

struct RecursionComponentProgram {
    name: &'static str,
    log_size: u32,
    constraint_count: usize,
    sampled_mask: TreeVec<Vec<Vec<usize>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
    preprocessed_column_ids: Vec<PreProcessedColumnId>,
    evaluation: ComponentEvaluation,
}

struct UnresolvedComponentProgram {
    name: &'static str,
    log_size: u32,
    constraint_count: usize,
    sampled_mask: TreeVec<Vec<Vec<UnresolvedSample>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
    preprocessed_column_ids: Vec<PreProcessedColumnId>,
    evaluation: ComponentEvaluation,
}

#[derive(Clone, Copy, Debug)]
struct UnresolvedSample {
    tree: usize,
    column: usize,
    point: usize,
}

/// Verifier-owned universal component program and exact STWO sample layout.
pub struct RecursionAirProgram {
    component_log_sizes: UniversalComponentLogSizes,
    components: Vec<RecursionComponentProgram>,
    column_log_sizes: TreeVec<Vec<u32>>,
    sample_coordinates: Vec<SampleCoordinate>,
    sample_point_offsets: Vec<CirclePointIndex>,
    composition_samples: [usize; COMPOSITION_SAMPLE_COUNT],
    max_log_degree_bound: u32,
    air_instruction_count: usize,
}

impl RecursionAirProgram {
    /// Compiles one fixed universal log-size profile into a compact mask map.
    ///
    /// The proof kind only enters the compiled expressions as a public
    /// constant, so the mask layout, constraint counts, and degree bounds are
    /// identical for every mode; the mode only changes constant values inside
    /// the expression forests. [`Self::new_with_kind`] fixes which child's
    /// forests a recursion lane replays.
    pub fn new(
        component_log_sizes: UniversalComponentLogSizes,
        preprocessed_ids: &[PreProcessedColumnId],
    ) -> Result<Self, RecursionAirProgramError> {
        Self::build(
            component_log_sizes,
            preprocessed_ids,
            ProofKind::SegmentLeaf,
            None,
        )
    }

    /// Compiles the profile whose expression forests carry one child mode's
    /// public proof-kind constants.
    pub fn new_with_kind(
        component_log_sizes: UniversalComponentLogSizes,
        preprocessed_ids: &[PreProcessedColumnId],
        proof_kind: ProofKind,
    ) -> Result<Self, RecursionAirProgramError> {
        Self::build(component_log_sizes, preprocessed_ids, proof_kind, None)
    }

    /// Compiles a profile for an explicitly lifted PCS degree bound.
    pub fn new_with_max_log_degree_bound(
        component_log_sizes: UniversalComponentLogSizes,
        preprocessed_ids: &[PreProcessedColumnId],
        max_log_degree_bound: u32,
    ) -> Result<Self, RecursionAirProgramError> {
        Self::build(
            component_log_sizes,
            preprocessed_ids,
            ProofKind::SegmentLeaf,
            Some(max_log_degree_bound),
        )
    }

    fn build(
        component_log_sizes: UniversalComponentLogSizes,
        preprocessed_ids: &[PreProcessedColumnId],
        proof_kind: ProofKind,
        requested_max_log_degree_bound: Option<u32>,
    ) -> Result<Self, RecursionAirProgramError> {
        for (component, log_size) in component_log_sizes.iter().copied().enumerate() {
            if !(MIN_CIRCLE_DOMAIN_LOG_SIZE..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&log_size) {
                return Err(RecursionAirProgramError::ComponentLogSizeOutOfRange {
                    component,
                    log_size,
                });
            }
        }

        let relations = UniversalRelations::dummy();
        let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(preprocessed_ids);
        let mut collector = RosterCollector::default();
        collector.push_all(
            &mut allocator,
            &relations,
            proof_kind,
            &component_log_sizes,
            &[SecureField::zero(); UNIVERSAL_COMPONENT_COUNT],
        );
        let RosterCollector {
            components,
            component_refs,
            constraint_checkers: _,
        } = collector;
        if components.len() != UNIVERSAL_COMPONENT_COUNT {
            return Err(RecursionAirProgramError::ComponentCountMismatch {
                expected: UNIVERSAL_COMPONENT_COUNT,
                actual: components.len(),
            });
        }

        let core_components = stwo::core::air::Components {
            components: component_refs
                .iter()
                .map(|component| component.as_verifier())
                .collect(),
            n_preprocessed_columns: preprocessed_ids.len(),
        };
        let composition_log_degree_bound = core_components.composition_log_degree_bound();
        let minimum_max_log_degree_bound = composition_log_degree_bound
            .checked_sub(stwo::core::verifier::COMPOSITION_LOG_SPLIT)
            .ok_or(RecursionAirProgramError::CompositionSplitUnderflow {
                composition_log_degree_bound,
            })?;
        let max_log_degree_bound =
            requested_max_log_degree_bound.unwrap_or(minimum_max_log_degree_bound);
        if !(minimum_max_log_degree_bound..=MAX_CIRCLE_DOMAIN_LOG_SIZE)
            .contains(&max_log_degree_bound)
        {
            return Err(RecursionAirProgramError::MaxLogDegreeBoundOutOfRange {
                minimum: minimum_max_log_degree_bound,
                actual: max_log_degree_bound,
            });
        }
        let mut column_log_sizes = core_components.column_log_sizes();
        column_log_sizes.push(vec![max_log_degree_bound; COMPOSITION_SAMPLE_COUNT]);
        let layout_point = CirclePoint {
            x: SecureField::zero(),
            y: SecureField::one(),
        };
        let mut sample_points =
            core_components.mask_points(layout_point, max_log_degree_bound, false);
        sample_points.push(vec![vec![layout_point]; COMPOSITION_SAMPLE_COUNT]);
        let (sample_coordinates, sampled_indices) = index_sample_layout(&sample_points);
        let composition_tree = sample_points.len() - 1;
        let composition_samples =
            core::array::from_fn(|column| sampled_indices[composition_tree][column][0]);
        let sample_point_offsets = resolve_sample_point_offsets(
            &components,
            &sampled_indices,
            sample_coordinates.len(),
            composition_samples,
            max_log_degree_bound,
        )?;
        let components = components
            .into_iter()
            .map(|component| resolve_component(component, &sampled_indices))
            .collect::<Result<Vec<_>, _>>()?;
        let air_instruction_count = components
            .iter()
            .try_fold(0_usize, |count, component| {
                count.checked_add(component.constraint_count)
            })
            .ok_or(RecursionAirProgramError::AirInstructionCountOverflow)?;

        Ok(Self {
            component_log_sizes,
            components,
            column_log_sizes,
            sample_coordinates,
            sample_point_offsets,
            composition_samples,
            max_log_degree_bound,
            air_instruction_count,
        })
    }

    pub fn sample_coordinates(&self) -> &[SampleCoordinate] {
        &self.sample_coordinates
    }

    /// Returns the base-circle shift from OODS for every sampled value.
    pub fn sample_point_offsets(&self) -> &[CirclePointIndex] {
        &self.sample_point_offsets
    }

    /// Returns every committed column degree in tree-major order.
    pub const fn column_log_sizes(&self) -> &TreeVec<Vec<u32>> {
        &self.column_log_sizes
    }

    pub const fn max_log_degree_bound(&self) -> u32 {
        self.max_log_degree_bound
    }

    pub const fn air_instruction_count(&self) -> usize {
        self.air_instruction_count
    }

    pub const fn component_log_sizes(&self) -> &UniversalComponentLogSizes {
        &self.component_log_sizes
    }

    pub fn component_names(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.components.iter().map(|component| component.name)
    }

    /// Evaluates every universal component and the split-composition equality.
    pub fn evaluate(
        &self,
        sampled_values: &[Rec],
        claimed_sums: &[Rec],
        relation_parameters: &HashMap<String, Rec>,
        random_coefficient: Rec,
        oods_point: &OodsPointCircuit,
    ) -> Result<RecursionAirEvaluation, RecursionAirProgramError> {
        if sampled_values.len() != self.sample_coordinates.len() {
            return Err(RecursionAirProgramError::SampledValueCountMismatch {
                expected: self.sample_coordinates.len(),
                actual: sampled_values.len(),
            });
        }
        if claimed_sums.len() != self.components.len() {
            return Err(RecursionAirProgramError::ClaimedSumCountMismatch {
                expected: self.components.len(),
                actual: claimed_sums.len(),
            });
        }
        let denominator_inverse = coset_vanishing_inverse(oods_point, self.max_log_degree_bound)?;
        let mut accumulator = Rec::zero();
        for (index, component) in self.components.iter().enumerate() {
            match &component.evaluation {
                ComponentEvaluation::Expressions { .. } => {
                    let inputs = component.expression_inputs(
                        sampled_values,
                        &claimed_sums[index],
                        relation_parameters,
                    );
                    let ComponentEvaluation::Expressions { expressions, .. } =
                        &component.evaluation
                    else {
                        unreachable!("matched expressions above")
                    };
                    let constraints = evaluate_air_expressions(expressions, &inputs)?;
                    accumulator = accumulate_air_constraints(
                        accumulator,
                        random_coefficient.clone(),
                        denominator_inverse.clone(),
                        constraints,
                    );
                }
                ComponentEvaluation::Poseidon2(eval) => {
                    let mask = component.sampled_mask.clone().map_cols(|column| {
                        column
                            .into_iter()
                            .map(|sample| sampled_values[sample].clone())
                            .collect::<Vec<_>>()
                    });
                    let evaluator = CircuitPointEvaluator::new(
                        component.name,
                        mask,
                        component.mask_offsets.clone(),
                        accumulator,
                        random_coefficient.clone(),
                        denominator_inverse.clone(),
                        claimed_sums[index].clone(),
                        component.log_size,
                        relation_parameters,
                    );
                    let evaluator = eval.evaluate_dynamic_relations(evaluator);
                    accumulator = evaluator.finish(component.constraint_count)?;
                }
            }
        }

        let left =
            core::array::from_fn(|index| sampled_values[self.composition_samples[index]].clone());
        let right = core::array::from_fn(|index| {
            sampled_values[self.composition_samples[SECURE_EXTENSION_DEGREE + index]].clone()
        });
        let claimed_value = combine_split_composition(
            left,
            right,
            oods_point.x.clone(),
            self.max_log_degree_bound,
        )?;
        let equality = accumulator.clone() - claimed_value.clone();
        Ok(RecursionAirEvaluation {
            air_value: accumulator,
            claimed_value,
            equality,
        })
    }
}

/// Computed and proof-claimed sides of the OODS composition assertion.
#[derive(Clone, Debug)]
pub struct RecursionAirEvaluation {
    pub air_value: Rec,
    pub claimed_value: Rec,
    pub equality: Rec,
}

impl RecursionComponentProgram {
    /// Assigns circuit wires to every formal variable of the component's
    /// compiled expression program.
    fn expression_inputs(
        &self,
        sampled_values: &[Rec],
        claimed_sum: &Rec,
        relation_parameters: &HashMap<String, Rec>,
    ) -> AirExpressionInputs {
        let ComponentEvaluation::Expressions {
            column_variables, ..
        } = &self.evaluation
        else {
            unreachable!("expression inputs are only built for compiled components")
        };
        let mut columns = HashMap::new();
        for (&(interaction, variable), &tree_column) in column_variables {
            for (point, offset) in self.mask_offsets[interaction][tree_column]
                .iter()
                .copied()
                .enumerate()
            {
                let sample = self.sampled_mask[interaction][tree_column][point];
                columns.insert(
                    (interaction, variable, offset),
                    sampled_values[sample].clone(),
                );
            }
        }

        let mut base_parameters = HashMap::new();
        for (position, column_id) in self.preprocessed_column_ids.iter().enumerate() {
            let sample = self.sampled_mask[PREPROCESSED_TRACE_IDX][position][0];
            base_parameters.insert(column_id.id.clone(), sampled_values[sample].clone());
        }
        base_parameters.insert(
            "column_size".to_owned(),
            Rec::from(BaseField::from_u32_unchecked(1_u32 << self.log_size)),
        );

        let mut extension_parameters = relation_parameters.clone();
        extension_parameters.insert("claimed_sum".to_owned(), claimed_sum.clone());

        AirExpressionInputs {
            columns,
            base_parameters,
            extension_parameters,
        }
    }
}

#[derive(Default)]
struct RosterCollector {
    components: Vec<UnresolvedComponentProgram>,
    component_refs: Vec<Box<dyn UniversalComponent>>,
    constraint_checkers: Vec<Box<dyn UniversalConstraintChecker>>,
}

trait UniversalComponent {
    fn as_prover(&self) -> &dyn ComponentProver<SimdBackend>;
    fn as_verifier(&self) -> &dyn stwo::core::air::Component;
}

impl<T> UniversalComponent for T
where
    T: ComponentProver<SimdBackend> + 'static,
{
    fn as_prover(&self) -> &dyn ComponentProver<SimdBackend> {
        self
    }

    fn as_verifier(&self) -> &dyn stwo::core::air::Component {
        self
    }
}

trait UniversalConstraintChecker {
    fn assert_constraints(&self, trace: &TreeVec<Vec<Vec<BaseField>>>);
}

struct FrameworkConstraintChecker<E> {
    eval: E,
    trace_locations: Vec<TreeSubspan>,
    preprocessed_column_indices: Vec<usize>,
    claimed_sum: SecureField,
}

impl<E: FrameworkEval + Sync> UniversalConstraintChecker for FrameworkConstraintChecker<E> {
    fn assert_constraints(&self, trace: &TreeVec<Vec<Vec<BaseField>>>) {
        let mut component_trace = trace.sub_tree(&self.trace_locations);
        component_trace[PREPROCESSED_TRACE_IDX] = self
            .preprocessed_column_indices
            .iter()
            .map(|index| &trace[PREPROCESSED_TRACE_IDX][*index])
            .collect();
        assert_constraints_on_trace(
            &component_trace,
            self.eval.log_size(),
            |evaluator| {
                self.eval.evaluate(evaluator);
            },
            self.claimed_sum,
        );
    }
}

impl RosterCollector {
    fn compile<E: FrameworkEval + Clone + Sync + 'static>(
        &mut self,
        name: &'static str,
        evaluation: ComponentEvaluation,
        component: FrameworkComponent<E>,
        recorder: MaskConsumptionRecorder,
        checker_eval: E,
    ) {
        let mask_offsets = recorder.mask_offsets();
        let mut sampled_mask = TreeVec::new(vec![Vec::new(); mask_offsets.len().max(1)]);
        for (interaction, columns) in mask_offsets.iter().enumerate() {
            let Some(location) = component
                .trace_locations()
                .iter()
                .find(|location| location.tree_index == interaction)
            else {
                panic!("component {name} has no trace location for interaction {interaction}");
            };
            assert_eq!(
                location.col_end - location.col_start,
                columns.len(),
                "component {name} column count mismatch on interaction {interaction}"
            );
            sampled_mask[interaction] = columns
                .iter()
                .enumerate()
                .map(|(local_column, offsets)| {
                    offsets
                        .iter()
                        .enumerate()
                        .map(|(point, _)| UnresolvedSample {
                            tree: interaction,
                            column: location.col_start + local_column,
                            point,
                        })
                        .collect()
                })
                .collect();
        }
        let preprocessed_columns = component.preprocessed_column_indices().to_vec();
        sampled_mask[PREPROCESSED_TRACE_IDX] = preprocessed_columns
            .iter()
            .copied()
            .map(|column| {
                vec![UnresolvedSample {
                    tree: PREPROCESSED_TRACE_IDX,
                    column,
                    point: 0,
                }]
            })
            .collect();
        let mut mask_offsets = mask_offsets;
        if mask_offsets.is_empty() {
            mask_offsets.push(Vec::new());
        }
        mask_offsets[PREPROCESSED_TRACE_IDX] = vec![vec![0]; preprocessed_columns.len()];

        self.components.push(UnresolvedComponentProgram {
            name,
            log_size: (*component).log_size(),
            constraint_count: recorder.n_constraints,
            sampled_mask,
            mask_offsets,
            preprocessed_column_ids: recorder.preprocessed_columns,
            evaluation,
        });
        self.constraint_checkers
            .push(Box::new(FrameworkConstraintChecker {
                eval: checker_eval,
                trace_locations: component.trace_locations().to_vec(),
                preprocessed_column_indices: component.preprocessed_column_indices().to_vec(),
                claimed_sum: component.claimed_sum(),
            }));
        self.component_refs.push(Box::new(component));
    }

    fn push<E: FrameworkEval + Clone + Sync + 'static>(
        &mut self,
        allocator: &mut TraceLocationAllocator,
        name: &'static str,
        claimed_sum: SecureField,
        eval: E,
    ) {
        let checker_eval = eval.clone();
        let component = FrameworkComponent::new(allocator, eval, claimed_sum);
        let recorder = (*component).evaluate(MaskConsumptionRecorder::default());
        let expressions = (*component).evaluate(ExprEvaluator::new());
        let max_degree = constraint_degree_bounds_with_preprocessed(
            &expressions,
            &recorder.preprocessed_columns,
        )
        .into_iter()
        .max()
        .unwrap_or(0);
        let constraint_log_degree_offset = component
            .max_constraint_log_degree_bound()
            .checked_sub(component.log_size())
            .expect("component constraint domain contains its trace domain");
        let max_supported_degree = 1_usize
            .checked_shl(constraint_log_degree_offset + 1)
            .unwrap_or(usize::MAX)
            .saturating_sub(1);
        assert!(
            max_degree <= max_supported_degree,
            "component {name} has constraint degree {max_degree}, exceeding degree {max_supported_degree} supported by its framework bound"
        );
        let mut column_variables = HashMap::new();
        let mut per_interaction: HashMap<usize, usize> = HashMap::new();
        for (variable, (interaction, _offsets)) in recorder.consumption.iter().enumerate() {
            let column = per_interaction.entry(*interaction).or_insert(0);
            column_variables.insert((*interaction, variable), *column);
            *column += 1;
        }
        self.compile(
            name,
            ComponentEvaluation::Expressions {
                expressions: Box::new(expressions),
                column_variables,
            },
            component,
            recorder,
            checker_eval,
        );
    }

    /// The poseidon2 permutation skips the formal-forest compilation (see
    /// [`ComponentEvaluation`]); its dynamic-relation evaluator consumes the
    /// same masks in the same order at circuit-evaluation time.
    fn push_poseidon2(
        &mut self,
        allocator: &mut TraceLocationAllocator,
        name: &'static str,
        claimed_sum: SecureField,
        eval: air::poseidon2::component::air::Eval,
    ) {
        let checker_eval = eval.clone();
        let stored_eval = Box::new(eval.clone());
        let component = FrameworkComponent::new(allocator, eval, claimed_sum);
        let recorder = (*component).evaluate(MaskConsumptionRecorder::default());
        self.compile(
            name,
            ComponentEvaluation::Poseidon2(stored_eval),
            component,
            recorder,
            checker_eval,
        );
    }

    /// Builds every universal component in canonical order against one
    /// allocator. The proof kind only enters expressions as a public
    /// constant, so the compiled structure is identical for every mode.
    fn push_all(
        &mut self,
        allocator: &mut TraceLocationAllocator,
        relations: &UniversalRelations,
        proof_kind: ProofKind,
        log_sizes: &UniversalComponentLogSizes,
        claimed_sums: &[SecureField; UNIVERSAL_COMPONENT_COUNT],
    ) {
        let kind = proof_kind;
        let mut next = 0_usize;
        let mut log_size = || {
            let log_size = log_sizes[next];
            next += 1;
            log_size
        };
        let mut sum_index = 0_usize;
        let mut claimed_sum = || {
            let sum = claimed_sums[sum_index];
            sum_index += 1;
            sum
        };
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[0], claimed_sum(), {
            let log_size = log_size();
            super::control_air::eval_for_proof_kind(log_size, kind, relations.control.clone())
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[1], claimed_sum(), {
            let log_size = log_size();
            super::transcript_air::Eval {
                log_size,
                relations: super::transcript_air::TranscriptHashCallRelations::new(
                    &relations.vm,
                    &relations.transcript,
                ),
            }
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[2], claimed_sum(), {
            let log_size = log_size();
            super::transcript_binding_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.control,
                &relations.transcript,
                &relations.transcript_binding,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[3], claimed_sum(), {
            let log_size = log_size();
            super::transcript_state_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.transcript_binding,
                &relations.transcript_state,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[4], claimed_sum(), {
            let log_size = log_size();
            super::transcript_word_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.transcript_binding,
                &relations.transcript_word,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[5], claimed_sum(), {
            let log_size = log_size();
            super::transcript_payload_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.transcript_word,
                &relations.verifier_input,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[6], claimed_sum(), {
            let log_size = log_size();
            super::pow::Eval {
                log_size,
                relations: relations.pow.clone(),
            }
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[7], claimed_sum(), {
            let log_size = log_size();
            super::pow::frame_eval(log_size, &relations.pow, &relations.transcript_binding)
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[8], claimed_sum(), {
            let log_size = log_size();
            super::relation_challenge_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.transcript_state,
                &relations.relation_challenge,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[9], claimed_sum(), {
            let log_size = log_size();
            super::verifier_randomness_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.transcript_state,
                &relations.verifier_randomness,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[10], claimed_sum(), {
            let log_size = log_size();
            super::statement_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.verifier_input,
                &relations.statement_input,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[11], claimed_sum(), {
            let log_size = log_size();
            super::statement_semantics_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.statement_input,
                &relations.recursion,
                &relations.vm,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[12], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_claim_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm_public_claim_input,
                &relations.vm,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[13], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_claim_hash_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm,
                &relations.vm_public_claim_input,
                &relations.vm_public_claim_hash,
                &relations.verifier_input,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[14], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_io_hash_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm,
                &relations.vm_public_claim_input,
                &relations.vm_public_io_hash,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[15], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_claim_semantics_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm_public_claim_input,
                &relations.statement_input,
                &relations.recursion,
                &relations.vm_public_io_hash,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[16], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_logup_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm_public_claim_input,
                &relations.relation_challenge,
                &relations.verifier_input,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[17], claimed_sum(), {
            let log_size = log_size();
            super::vm_public_logup_control_air::eval_for_proof_kind(
                log_size,
                kind,
                relations.control.clone(),
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[18], claimed_sum(), {
            let log_size = log_size();
            super::vm_air_composition_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.relation_challenge,
                &relations.verifier_input,
                &relations.verifier_randomness,
                &relations.statement_input,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[19], claimed_sum(), {
            let log_size = log_size();
            super::vm_air_composition_control_air::eval_for_proof_kind(
                log_size,
                kind,
                relations.control.clone(),
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[20], claimed_sum(), {
            let log_size = log_size();
            super::query_position_air::bits_eval_for_proof_kind(
                log_size,
                kind,
                &relations.verifier_randomness,
                &relations.query_position,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[21], claimed_sum(), {
            let log_size = log_size();
            super::query_position_air::mapping_eval_for_proof_kind(
                log_size,
                kind,
                &relations.query_position,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[22], claimed_sum(), {
            let log_size = log_size();
            super::merkle_root_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.verifier_input,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[23], claimed_sum(), {
            let log_size = log_size();
            super::trace_merkle_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm,
                &relations.control,
                &relations.query_position,
                &relations.trace_merkle,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[24], claimed_sum(), {
            let log_size = log_size();
            super::pcs_deep_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.verifier_input,
                &relations.trace_merkle,
                &relations.verifier_randomness,
                &relations.query_position,
                &relations.pcs_deep,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[25], claimed_sum(), {
            let log_size = log_size();
            super::fri_merkle_air::leaf_eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm,
                &relations.fri_merkle,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[26], claimed_sum(), {
            let log_size = log_size();
            super::fri_merkle_air::node_eval_for_proof_kind(
                log_size,
                kind,
                &relations.vm,
                &relations.fri_merkle,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[27], claimed_sum(), {
            let log_size = log_size();
            super::fri_merkle_air::anchor_eval_for_proof_kind(
                log_size,
                kind,
                &relations.control,
                &relations.query_position,
                &relations.fri_merkle,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[28], claimed_sum(), {
            let log_size = log_size();
            super::fri_verifier_control_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.control,
                &relations.query_position,
                &relations.fri_verifier_route,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[29], claimed_sum(), {
            let log_size = log_size();
            super::fri_verifier_input_air::eval_for_proof_kind(
                log_size,
                kind,
                &relations.verifier_input,
                &relations.verifier_randomness,
                &relations.query_position,
                &relations.pcs_deep,
                &relations.fri_merkle,
                &relations.fri_verifier_route,
                &relations.recursion,
            )
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[30], claimed_sum(), {
            let log_size = log_size();
            crate::qm31_mul::eval_for_proof_kind(log_size, kind, &relations.recursion)
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[31], claimed_sum(), {
            let log_size = log_size();
            crate::qm31_inv::eval_for_proof_kind(log_size, kind, &relations.recursion)
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[32], claimed_sum(), {
            let log_size = log_size();
            crate::linear_ops::eval_for_proof_kind(log_size, kind, &relations.recursion)
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[33], claimed_sum(), {
            let log_size = log_size();
            crate::merkle_path::Eval {
                log_size,
                relations: crate::relations::SharedPrimitiveRelations::for_merkle(
                    &relations.vm,
                    &relations.recursion,
                ),
            }
        });
        self.push_poseidon2(allocator, UNIVERSAL_COMPONENT_NAMES[34], claimed_sum(), {
            let log_size = log_size();
            air::poseidon2::component::air::Eval {
                log_size,
                relations: relations.vm.clone(),
            }
        });
        self.push(allocator, UNIVERSAL_COMPONENT_NAMES[35], claimed_sum(), {
            let log_size = log_size();
            prover::components::lookups::range_check_8_8::air::Eval {
                log_size,
                relations: relations.vm.clone(),
            }
        });
    }
}

fn index_sample_layout<T>(
    sample_points: &TreeVec<Vec<Vec<T>>>,
) -> (Vec<SampleCoordinate>, TreeVec<Vec<Vec<usize>>>) {
    let mut coordinates = Vec::new();
    let mut indices = Vec::with_capacity(sample_points.len());
    for (tree, columns) in sample_points.iter().enumerate() {
        let mut tree_indices = Vec::with_capacity(columns.len());
        for (column, points) in columns.iter().enumerate() {
            let mut column_indices = Vec::with_capacity(points.len());
            for _point in 0..points.len() {
                column_indices.push(coordinates.len());
                coordinates.push(SampleCoordinate {
                    tree,
                    column,
                    point: _point,
                });
            }
            tree_indices.push(column_indices);
        }
        indices.push(tree_indices);
    }
    (coordinates, TreeVec::new(indices))
}

fn resolve_sample_point_offsets(
    components: &[UnresolvedComponentProgram],
    sampled_indices: &TreeVec<Vec<Vec<usize>>>,
    sample_count: usize,
    composition_samples: [usize; COMPOSITION_SAMPLE_COUNT],
    max_log_degree_bound: u32,
) -> Result<Vec<CirclePointIndex>, RecursionAirProgramError> {
    let trace_step = stwo::core::poly::circle::CanonicCoset::new(max_log_degree_bound).step_size();
    let mut offsets: Vec<Option<CirclePointIndex>> = vec![None; sample_count];
    for (component_index, component) in components.iter().enumerate() {
        for (interaction, columns) in component.sampled_mask.iter().enumerate() {
            let component_offsets = component.mask_offsets.get(interaction).ok_or(
                RecursionAirProgramError::ComponentMaskInteractionMissing {
                    component: component_index,
                    interaction,
                },
            )?;
            if component_offsets.len() != columns.len() {
                return Err(RecursionAirProgramError::ComponentMaskColumnCountMismatch {
                    component: component_index,
                    interaction,
                    expected: columns.len(),
                    actual: component_offsets.len(),
                });
            }
            for (column, (samples, sample_offsets)) in
                columns.iter().zip(component_offsets).enumerate()
            {
                if samples.len() != sample_offsets.len() {
                    return Err(RecursionAirProgramError::ComponentMaskPointCountMismatch {
                        component: component_index,
                        interaction,
                        column,
                        expected: samples.len(),
                        actual: sample_offsets.len(),
                    });
                }
                for (sample, &offset) in samples.iter().zip(sample_offsets) {
                    let sample_index =
                        sampled_index(sampled_indices, sample.tree, sample.column, sample.point)?;
                    let point_offset = signed_index_multiple(trace_step, offset);
                    match offsets[sample_index] {
                        Some(existing) if existing != point_offset => {
                            return Err(RecursionAirProgramError::SamplePointOffsetConflict {
                                sample: sample_index,
                                expected: existing.0,
                                actual: point_offset.0,
                            });
                        }
                        Some(_) => {}
                        None => offsets[sample_index] = Some(point_offset),
                    }
                }
            }
        }
    }
    for sample in composition_samples {
        offsets[sample] = Some(CirclePointIndex::zero());
    }
    offsets
        .into_iter()
        .enumerate()
        .map(|(sample, offset)| {
            offset.ok_or(RecursionAirProgramError::SamplePointOffsetMissing { sample })
        })
        .collect()
}

fn signed_index_multiple(step: CirclePointIndex, multiplier: isize) -> CirclePointIndex {
    let magnitude = step * multiplier.unsigned_abs();
    if multiplier.is_negative() {
        -magnitude
    } else {
        magnitude
    }
}

fn resolve_component(
    component: UnresolvedComponentProgram,
    sampled_indices: &TreeVec<Vec<Vec<usize>>>,
) -> Result<RecursionComponentProgram, RecursionAirProgramError> {
    let sampled_mask = component.sampled_mask.map_cols(|column| {
        column
            .into_iter()
            .map(|sample| sampled_index(sampled_indices, sample.tree, sample.column, sample.point))
            .collect::<Result<Vec<_>, _>>()
    });
    let sampled_mask = TreeVec::new(
        sampled_mask
            .0
            .into_iter()
            .map(|tree| tree.into_iter().collect::<Result<Vec<_>, _>>())
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(RecursionComponentProgram {
        name: component.name,
        log_size: component.log_size,
        constraint_count: component.constraint_count,
        sampled_mask,
        mask_offsets: component.mask_offsets,
        preprocessed_column_ids: component.preprocessed_column_ids,
        evaluation: component.evaluation,
    })
}

fn sampled_index(
    sampled_indices: &TreeVec<Vec<Vec<usize>>>,
    tree: usize,
    column: usize,
    point: usize,
) -> Result<usize, RecursionAirProgramError> {
    sampled_indices
        .get(tree)
        .and_then(|columns| columns.get(column))
        .and_then(|points| points.get(point))
        .copied()
        .ok_or(RecursionAirProgramError::SampleCoordinateOutOfRange {
            tree,
            column,
            point,
        })
}

/// Invalid fixed universal profile, mask layout, or per-proof assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecursionAirProgramError {
    ComponentLogSizeOutOfRange {
        component: usize,
        log_size: u32,
    },
    ComponentCountMismatch {
        expected: usize,
        actual: usize,
    },
    CompositionSplitUnderflow {
        composition_log_degree_bound: u32,
    },
    MaxLogDegreeBoundOutOfRange {
        minimum: u32,
        actual: u32,
    },
    AirInstructionCountOverflow,
    SampledValueCountMismatch {
        expected: usize,
        actual: usize,
    },
    ClaimedSumCountMismatch {
        expected: usize,
        actual: usize,
    },
    SampleCoordinateOutOfRange {
        tree: usize,
        column: usize,
        point: usize,
    },
    ComponentMaskInteractionMissing {
        component: usize,
        interaction: usize,
    },
    ComponentMaskColumnCountMismatch {
        component: usize,
        interaction: usize,
        expected: usize,
        actual: usize,
    },
    ComponentMaskPointCountMismatch {
        component: usize,
        interaction: usize,
        column: usize,
        expected: usize,
        actual: usize,
    },
    SamplePointOffsetConflict {
        sample: usize,
        expected: usize,
        actual: usize,
    },
    SamplePointOffsetMissing {
        sample: usize,
    },
    DynamicConstraintCountMismatch {
        component: &'static str,
        expected: usize,
        actual: usize,
    },
    ComponentMaskNotFullyConsumed {
        component: &'static str,
        interaction: usize,
        expected: usize,
        actual: usize,
    },
    ComponentMaskColumnMissing {
        component: &'static str,
        interaction: usize,
        column: usize,
    },
    DynamicMaskInteractionMissing {
        component: &'static str,
        interaction: usize,
    },
    ComponentMaskOffsetMismatch {
        component: &'static str,
        interaction: usize,
        column: usize,
        expected: Vec<isize>,
        actual: Vec<isize>,
    },
    DynamicMaskPointCountMismatch {
        component: &'static str,
        interaction: usize,
        column: usize,
        expected: usize,
        actual: usize,
    },
    RelationDescriptorMissing {
        name: String,
    },
    RelationArityExceeded {
        name: String,
        maximum: usize,
        actual: usize,
    },
    RelationParameterMissing {
        name: String,
    },
    Oods(OodsCircuitError),
    AirExpression(AirExpressionError),
}

impl From<OodsCircuitError> for RecursionAirProgramError {
    fn from(value: OodsCircuitError) -> Self {
        Self::Oods(value)
    }
}

impl From<AirExpressionError> for RecursionAirProgramError {
    fn from(value: AirExpressionError) -> Self {
        Self::AirExpression(value)
    }
}

impl fmt::Display for RecursionAirProgramError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for RecursionAirProgramError {}

/// Circuit-valued point evaluator for components with a generated
/// dynamic-relation evaluation path.
///
/// Mirrors the VM composition circuit's evaluator: masks are consumed in
/// declaration order with offset validation, relation tuples are combined
/// from transcript-bound formal parameters looked up by name, and the LogUp
/// accumulation reuses the shared proxy so native and circuit claimed sums
/// follow identical constraint order.
struct CircuitPointEvaluator<'a> {
    component: &'static str,
    mask: TreeVec<Vec<Vec<Rec>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
    column_index: Vec<usize>,
    random_coefficient: Rec,
    denominator_inverse: Rec,
    accumulator: Rec,
    relation_parameters: &'a HashMap<String, Rec>,
    constraint_count: usize,
    error: Option<RecursionAirProgramError>,
    logup: crate::dynamic_logup::CircuitLogup,
}

impl<'a> CircuitPointEvaluator<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        component: &'static str,
        mask: TreeVec<Vec<Vec<Rec>>>,
        mask_offsets: TreeVec<Vec<Vec<isize>>>,
        accumulator: Rec,
        random_coefficient: Rec,
        denominator_inverse: Rec,
        claimed_sum: Rec,
        log_size: u32,
        relation_parameters: &'a HashMap<String, Rec>,
    ) -> Self {
        let column_size_inverse = BaseField::from_u32_unchecked(1_u32 << log_size).inverse();
        let cumsum_shift = claimed_sum * column_size_inverse;
        let column_index = vec![0; mask.len()];
        Self {
            component,
            mask,
            mask_offsets,
            column_index,
            random_coefficient,
            denominator_inverse,
            accumulator,
            relation_parameters,
            constraint_count: 0,
            error: None,
            logup: crate::dynamic_logup::CircuitLogup::new(
                stwo_constraint_framework::INTERACTION_TRACE_IDX,
                cumsum_shift,
            ),
        }
    }

    fn finish(self, expected_constraints: usize) -> Result<Rec, RecursionAirProgramError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        if self.constraint_count != expected_constraints {
            return Err(RecursionAirProgramError::DynamicConstraintCountMismatch {
                component: self.component,
                expected: expected_constraints,
                actual: self.constraint_count,
            });
        }
        for (interaction, (consumed, columns)) in
            self.column_index.iter().zip(self.mask.iter()).enumerate()
        {
            if *consumed != columns.len() {
                return Err(RecursionAirProgramError::ComponentMaskNotFullyConsumed {
                    component: self.component,
                    interaction,
                    expected: columns.len(),
                    actual: *consumed,
                });
            }
        }
        Ok(self.accumulator)
    }

    fn relation_parameter(&mut self, name: String) -> Rec {
        match self.relation_parameters.get(&name) {
            Some(value) => value.clone(),
            None => {
                self.error = Some(RecursionAirProgramError::RelationParameterMissing { name });
                Rec::zero()
            }
        }
    }
}

impl EvalAtRow for CircuitPointEvaluator<'_> {
    type F = Rec;
    type EF = Rec;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        offsets: [isize; N],
    ) -> [Self::F; N] {
        let Some(column_index) = self.column_index.get_mut(interaction) else {
            self.error = Some(RecursionAirProgramError::DynamicMaskInteractionMissing {
                component: self.component,
                interaction,
            });
            return core::array::from_fn(|_| Rec::zero());
        };
        let column = *column_index;
        *column_index += 1;
        let Some(expected_offsets) = self
            .mask_offsets
            .get(interaction)
            .and_then(|columns| columns.get(column))
        else {
            self.error = Some(RecursionAirProgramError::ComponentMaskColumnMissing {
                component: self.component,
                interaction,
                column,
            });
            return core::array::from_fn(|_| Rec::zero());
        };
        if expected_offsets.as_slice() != offsets {
            self.error = Some(RecursionAirProgramError::ComponentMaskOffsetMismatch {
                component: self.component,
                interaction,
                column,
                expected: expected_offsets.clone(),
                actual: offsets.to_vec(),
            });
            return core::array::from_fn(|_| Rec::zero());
        }
        let Some(values) = self
            .mask
            .get(interaction)
            .and_then(|columns| columns.get(column))
        else {
            self.error = Some(RecursionAirProgramError::ComponentMaskColumnMissing {
                component: self.component,
                interaction,
                column,
            });
            return core::array::from_fn(|_| Rec::zero());
        };
        if values.len() != N {
            self.error = Some(RecursionAirProgramError::DynamicMaskPointCountMismatch {
                component: self.component,
                interaction,
                column,
                expected: N,
                actual: values.len(),
            });
            return core::array::from_fn(|_| Rec::zero());
        }
        core::array::from_fn(|index| values[index].clone())
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: core::ops::Mul<G, Output = Self::EF> + From<G>,
    {
        self.constraint_count += 1;
        let constraint = Self::EF::from(constraint);
        let previous = <Rec as core::ops::Mul<Rec>>::mul(
            self.accumulator.clone(),
            self.random_coefficient.clone(),
        );
        let constraint =
            <Rec as core::ops::Mul<Rec>>::mul(self.denominator_inverse.clone(), constraint);
        self.accumulator = <Rec as core::ops::Add<Rec>>::add(previous, constraint);
    }

    fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        values
            .into_iter()
            .enumerate()
            .fold(Rec::zero(), |value, (index, limb)| {
                value + limb * secure_basis(index)
            })
    }

    crate::dynamic_logup::recursion_logup_proxy!();
}

impl air::relation_eval::DynamicRelationEvalAtRow for CircuitPointEvaluator<'_> {
    fn add_to_named_relation(
        &mut self,
        relation: &'static str,
        multiplicity: Self::EF,
        values: &[Self::F],
    ) {
        let Some(descriptor) = prover::relations::Relations::DESCRIPTORS
            .iter()
            .find(|descriptor| descriptor.name == relation)
        else {
            self.error = Some(RecursionAirProgramError::RelationDescriptorMissing {
                name: relation.into(),
            });
            return;
        };
        if values.len() > descriptor.size {
            self.error = Some(RecursionAirProgramError::RelationArityExceeded {
                name: relation.into(),
                maximum: descriptor.size,
                actual: values.len(),
            });
            return;
        }
        let mut denominator = Rec::zero();
        for (index, value) in values.iter().enumerate() {
            let alpha_power = self.relation_parameter(format!("{relation}_alpha{index}"));
            denominator += value.clone() * alpha_power;
        }
        denominator = denominator - self.relation_parameter(format!("{relation}_z"));
        self.write_logup_frac(Fraction::new(multiplicity, denominator));
    }
}

fn secure_basis(index: usize) -> SecureField {
    SecureField::from_m31_array(core::array::from_fn(|limb| {
        BaseField::from(u32::from(limb == index))
    }))
}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use stwo::core::channel::Channel;
    use stwo::core::fields::m31::M31;

    use super::*;
    use crate::air_relation_parameters::{RelationChallengeCircuit, bind_relation_parameters};
    use crate::oods_circuit::oods_point_from_seed;
    use crate::recorder::CircuitBuilder;
    use crate::universal_relations::universal_relation_descriptors;

    const LOG_SIZE: u32 = 5;

    fn log_sizes() -> UniversalComponentLogSizes {
        [LOG_SIZE; UNIVERSAL_COMPONENT_COUNT]
    }

    fn preprocessed_ids() -> Vec<PreProcessedColumnId> {
        universal_preprocessed_column_ids(&log_sizes())
    }

    fn program() -> RecursionAirProgram {
        RecursionAirProgram::new(log_sizes(), &preprocessed_ids())
            .expect("fixture universal profile is valid")
    }

    fn build_native_components(
        relations: &UniversalRelations,
        claimed_sums: &[SecureField; UNIVERSAL_COMPONENT_COUNT],
    ) -> UniversalComponents {
        universal_components(
            &preprocessed_ids(),
            relations,
            ProofKind::SegmentLeaf,
            &log_sizes(),
            claimed_sums,
        )
    }

    fn drawn_relation_parameters(
        descriptors: &[prover::relations::RelationDescriptor],
    ) -> HashMap<String, Rec> {
        let mut channel = Poseidon2M31Channel::default();
        let challenges = descriptors
            .iter()
            .map(|_| {
                let [z, alpha] = channel
                    .draw_secure_felts(2)
                    .try_into()
                    .expect("each relation draw has z and alpha");
                RelationChallengeCircuit::new(
                    z.to_m31_array()
                        .into_iter()
                        .chain(alpha.to_m31_array())
                        .map(Rec::from)
                        .collect::<Vec<_>>()
                        .try_into()
                        .expect("two secure values have eight limbs"),
                )
            })
            .collect::<Vec<_>>();
        bind_relation_parameters(descriptors, &challenges)
            .expect("the universal registry owns every native draw")
    }

    fn inflate_samples(
        coordinates: &[SampleCoordinate],
        values: &[SecureField],
    ) -> TreeVec<Vec<Vec<SecureField>>> {
        let tree_count = coordinates
            .iter()
            .map(|coordinate| coordinate.tree)
            .max()
            .expect("universal AIR has sampled columns")
            + 1;
        let mut samples = TreeVec::new(vec![Vec::new(); tree_count]);
        for (coordinate, &value) in coordinates.iter().zip(values) {
            if samples[coordinate.tree].len() <= coordinate.column {
                samples[coordinate.tree].resize(coordinate.column + 1, Vec::new());
            }
            samples[coordinate.tree][coordinate.column].push(value);
        }
        samples
    }

    #[test]
    fn component_order_is_the_canonical_roster() {
        assert_eq!(
            program().component_names().collect::<Vec<_>>(),
            UNIVERSAL_COMPONENT_NAMES
        );
    }

    #[test]
    fn preprocessed_ids_are_unique_and_deterministic() {
        let first = preprocessed_ids();
        let second = preprocessed_ids();
        assert_eq!(first, second);
        let unique: std::collections::HashSet<_> = first.iter().map(|column| &column.id).collect();
        assert_eq!(unique.len(), first.len());
    }

    #[test]
    fn recorder_matches_framework_component_info() {
        let relations = UniversalRelations::dummy();
        let claimed_sums = [SecureField::zero(); UNIVERSAL_COMPONENT_COUNT];
        let mut allocator =
            TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_ids());
        let mut collector = RosterCollector::default();
        collector.push_all(
            &mut allocator,
            &relations,
            ProofKind::SegmentLeaf,
            &log_sizes(),
            &claimed_sums,
        );
        for (program, component) in collector
            .components
            .iter()
            .zip(collector.component_refs.iter())
        {
            assert_eq!(
                program.constraint_count,
                component.as_verifier().n_constraints(),
                "constraint count mismatch for {}",
                program.name
            );
        }
    }

    #[test]
    fn sample_layout_has_four_commitment_trees() {
        assert_eq!(
            program()
                .sample_coordinates()
                .iter()
                .map(|coordinate| coordinate.tree)
                .max(),
            Some(3)
        );
    }

    #[test]
    fn universal_composition_matches_stwo_point_evaluation() {
        let program = program();
        let mut native_channel = Poseidon2M31Channel::default();
        let relations = UniversalRelations::draw(&mut native_channel);
        let claimed_sum_values = core::array::from_fn(|index| {
            SecureField::from_m31_array([
                M31::from(index as u32 + 2),
                M31::from(index as u32 + 3),
                M31::from(index as u32 + 4),
                M31::from(index as u32 + 5),
            ])
        });
        let native_components = build_native_components(&relations, &claimed_sum_values);
        let core_components = stwo::core::air::Components {
            components: native_components.verifiers(),
            n_preprocessed_columns: preprocessed_ids().len(),
        };
        let seed = SecureField::from_m31_array([
            M31::from(31),
            M31::from(37),
            M31::from(41),
            M31::from(43),
        ]);
        let oods = oods_point_from_seed(Rec::from(seed)).expect("fixture seed maps to the circle");
        let native_point = CirclePoint {
            x: oods.x.value(),
            y: oods.y.value(),
        };
        let random_coefficient = SecureField::from_m31_array([
            M31::from(47),
            M31::from(53),
            M31::from(59),
            M31::from(61),
        ]);
        let flat_samples = (0..program.sample_coordinates().len())
            .map(|index| {
                SecureField::from_m31_array([
                    M31::from(index as u32 + 2),
                    M31::from(index as u32 + 3),
                    M31::from(index as u32 + 5),
                    M31::from(index as u32 + 7),
                ])
            })
            .collect::<Vec<_>>();
        let native_samples = inflate_samples(program.sample_coordinates(), &flat_samples);
        let native = core_components.eval_composition_polynomial_at_point(
            native_point,
            &native_samples,
            random_coefficient,
            program.max_log_degree_bound(),
        );

        let mut builder = CircuitBuilder::default();
        let sampled_inputs = flat_samples
            .iter()
            .map(|&value| builder.input(value).1)
            .collect::<Vec<_>>();
        let claimed_sum_inputs = claimed_sum_values
            .iter()
            .map(|&value| builder.input(value).1)
            .collect::<Vec<_>>();
        let random_input = builder.input(random_coefficient).1;
        let actual = program
            .evaluate(
                &sampled_inputs,
                &claimed_sum_inputs,
                &drawn_relation_parameters(&universal_relation_descriptors()),
                random_input,
                &oods,
            )
            .expect("complete streaming inputs evaluate");
        assert_eq!(actual.air_value.value(), native);
    }
}
