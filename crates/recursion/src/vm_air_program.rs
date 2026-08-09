//! Streaming VM AIR composition evaluation for recursion.
//!
//! The verifier visits macro-generated prover components in native composition
//! order and executes the dynamic-relation evaluator generated from the same
//! AIR declaration. Fixed metadata maps STWO's flat sampled-value order back
//! to each component mask without materializing a symbolic expression forest.

use core::fmt;
use std::collections::HashMap;

use air::relation_eval::{DynamicRelationEvalAtRow, DynamicRelationFrameworkEval};
use num_traits::{One, Zero};
use prover::components::{
    COMPONENT_COUNT, COMPONENT_NAMES, Claim, ClaimedSum, ComponentVisitor, Components,
    DynamicRelationComponentVisitor,
};
use prover::relations::{PreProcessedTrace, RelationDescriptor, Relations};
use stwo::core::Fraction;
use stwo::core::air::Components as CoreComponents;
use stwo::core::circle::{CirclePoint, CirclePointIndex};
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo::core::pcs::TreeVec;
use stwo::core::poly::circle::{MAX_CIRCLE_DOMAIN_LOG_SIZE, MIN_CIRCLE_DOMAIN_LOG_SIZE};
use stwo::core::verifier::COMPOSITION_LOG_SPLIT;
use stwo_constraint_framework::{
    EvalAtRow, FrameworkComponent, FrameworkEval, INTERACTION_TRACE_IDX, InfoEvaluator,
    PREPROCESSED_TRACE_IDX, TraceLocationAllocator,
};

use super::oods_circuit::{
    OodsCircuitError, OodsPointCircuit, combine_split_composition, coset_vanishing_inverse,
};
use crate::dynamic_logup::CircuitLogup;
use crate::recorder::Rec;

/// Number of VM component claims and interaction claimed sums.
pub const VM_AIR_COMPONENT_COUNT: usize = COMPONENT_COUNT;
/// Number of split-composition coordinate samples appended by STWO.
pub const COMPOSITION_SAMPLE_COUNT: usize = 2 * SECURE_EXTENSION_DEGREE;

/// One value in STWO's tree-major, column-major, point-major sample order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SampleCoordinate {
    pub tree: usize,
    pub column: usize,
    pub point: usize,
}

#[derive(Clone, Debug)]
struct ComponentProgram {
    name: &'static str,
    log_size: u32,
    constraint_count: usize,
    sampled_mask: TreeVec<Vec<Vec<usize>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
}

#[derive(Clone, Debug)]
struct UnresolvedComponentProgram {
    name: &'static str,
    log_size: u32,
    constraint_count: usize,
    sampled_mask: TreeVec<Vec<Vec<UnresolvedSample>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
    preprocessed_columns: Vec<usize>,
}

#[derive(Clone, Copy, Debug)]
struct UnresolvedSample {
    tree: usize,
    column: usize,
    point: usize,
}

/// Verifier-owned VM component program and exact STWO sample layout.
pub struct VmAirProgram {
    component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
    components: Vec<ComponentProgram>,
    column_log_sizes: TreeVec<Vec<u32>>,
    sample_coordinates: Vec<SampleCoordinate>,
    sample_point_offsets: Vec<CirclePointIndex>,
    composition_samples: [usize; COMPOSITION_SAMPLE_COUNT],
    max_log_degree_bound: u32,
    air_instruction_count: usize,
}

impl VmAirProgram {
    /// Compiles one fixed component-log-size profile into a compact mask map.
    pub fn new(
        component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
    ) -> Result<Self, VmAirProgramError> {
        Self::build(component_log_sizes, None)
    }

    /// Compiles a profile for an explicitly lifted PCS degree bound.
    pub fn new_with_max_log_degree_bound(
        component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
        max_log_degree_bound: u32,
    ) -> Result<Self, VmAirProgramError> {
        Self::build(component_log_sizes, Some(max_log_degree_bound))
    }

    fn build(
        component_log_sizes: [u32; VM_AIR_COMPONENT_COUNT],
        requested_max_log_degree_bound: Option<u32>,
    ) -> Result<Self, VmAirProgramError> {
        for (component, log_size) in component_log_sizes.iter().copied().enumerate() {
            if !(MIN_CIRCLE_DOMAIN_LOG_SIZE..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&log_size) {
                return Err(VmAirProgramError::ComponentLogSizeOutOfRange {
                    component,
                    log_size,
                });
            }
        }

        let preprocessed_ids = PreProcessedTrace::column_ids();
        let preprocessed_log_sizes = PreProcessedTrace::column_log_sizes();
        if preprocessed_ids.len() != preprocessed_log_sizes.len() {
            return Err(VmAirProgramError::PreprocessedRegistryLengthMismatch {
                ids: preprocessed_ids.len(),
                log_sizes: preprocessed_log_sizes.len(),
            });
        }
        let claim = Claim::from_component_log_sizes(component_log_sizes);
        let claimed_sums = zero_claimed_sums();
        let components = build_components(&claim, Relations::dummy(), &claimed_sums);

        let mut collector = ProgramCollector::default();
        components.visit_components(&claimed_sums, &mut collector);
        if let Some(error) = collector.error {
            return Err(error);
        }
        if collector.components.len() != VM_AIR_COMPONENT_COUNT {
            return Err(VmAirProgramError::ComponentCountMismatch {
                expected: VM_AIR_COMPONENT_COUNT,
                actual: collector.components.len(),
            });
        }
        validate_preprocessed_log_sizes(&collector.components, &preprocessed_log_sizes)?;

        let core_components = CoreComponents {
            components: components.verifiers(),
            n_preprocessed_columns: preprocessed_ids.len(),
        };
        let composition_log_degree_bound = core_components.composition_log_degree_bound();
        let minimum_max_log_degree_bound = composition_log_degree_bound
            .checked_sub(COMPOSITION_LOG_SPLIT)
            .ok_or(VmAirProgramError::CompositionSplitUnderflow {
                composition_log_degree_bound,
            })?;
        let max_log_degree_bound =
            requested_max_log_degree_bound.unwrap_or(minimum_max_log_degree_bound);
        if !(minimum_max_log_degree_bound..=MAX_CIRCLE_DOMAIN_LOG_SIZE)
            .contains(&max_log_degree_bound)
        {
            return Err(VmAirProgramError::MaxLogDegreeBoundOutOfRange {
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
            &collector.components,
            &sampled_indices,
            sample_coordinates.len(),
            composition_samples,
            max_log_degree_bound,
        )?;
        let components = collector
            .components
            .into_iter()
            .map(|component| resolve_component(component, &sampled_indices))
            .collect::<Result<Vec<_>, _>>()?;
        let air_instruction_count = components
            .iter()
            .try_fold(0_usize, |count, component| {
                count.checked_add(component.constraint_count)
            })
            .ok_or(VmAirProgramError::AirInstructionCountOverflow)?;

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

    pub fn component_names(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.components.iter().map(|component| component.name)
    }

    /// Evaluates every VM component and the split-composition equality.
    pub fn evaluate(
        &self,
        sampled_values: &[Rec],
        claimed_sums: &[Rec],
        relation_parameters: &HashMap<String, Rec>,
        random_coefficient: Rec,
        oods_point: &OodsPointCircuit,
    ) -> Result<VmAirEvaluation, VmAirProgramError> {
        if sampled_values.len() != self.sample_coordinates.len() {
            return Err(VmAirProgramError::SampledValueCountMismatch {
                expected: self.sample_coordinates.len(),
                actual: sampled_values.len(),
            });
        }
        if claimed_sums.len() != self.components.len() {
            return Err(VmAirProgramError::ClaimedSumCountMismatch {
                expected: self.components.len(),
                actual: claimed_sums.len(),
            });
        }
        validate_relation_parameters(Relations::DESCRIPTORS.as_slice(), relation_parameters)?;

        let denominator_inverse = coset_vanishing_inverse(oods_point, self.max_log_degree_bound)?;
        let claim = Claim::from_component_log_sizes(self.component_log_sizes);
        let native_claimed_sums = zero_claimed_sums();
        let components = build_components(&claim, Relations::dummy(), &native_claimed_sums);
        let mut visitor = CircuitEvaluationVisitor {
            program: &self.components,
            sampled_values,
            claimed_sums,
            relation_parameters,
            random_coefficient,
            denominator_inverse,
            accumulator: Rec::zero(),
            next_component: 0,
            error: None,
        };
        components.visit_dynamic_relation_components(&native_claimed_sums, &mut visitor);
        let air_value = visitor.finish()?;

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
        let equality = air_value.clone() - claimed_value.clone();
        Ok(VmAirEvaluation {
            air_value,
            claimed_value,
            equality,
        })
    }
}

/// Verifier-owned composition program for the detached Poseidon2 AIR.
pub struct Poseidon2AirProgram {
    log_size: u32,
    component: ComponentProgram,
    column_log_sizes: TreeVec<Vec<u32>>,
    sample_coordinates: Vec<SampleCoordinate>,
    sample_point_offsets: Vec<CirclePointIndex>,
    composition_samples: [usize; COMPOSITION_SAMPLE_COUNT],
    max_log_degree_bound: u32,
}

impl Poseidon2AirProgram {
    /// Compiles the direct DSL component at its frozen segment capacity.
    pub fn new(log_size: u32) -> Result<Self, VmAirProgramError> {
        if !(MIN_CIRCLE_DOMAIN_LOG_SIZE..=MAX_CIRCLE_DOMAIN_LOG_SIZE).contains(&log_size) {
            return Err(VmAirProgramError::ComponentLogSizeOutOfRange {
                component: 0,
                log_size,
            });
        }
        let component = poseidon2_component(log_size);
        let unresolved = compile_component(0, "poseidon2", &component)?;
        let core_components = CoreComponents {
            components: vec![&component],
            n_preprocessed_columns: 0,
        };
        let composition_log_degree_bound = core_components.composition_log_degree_bound();
        let max_log_degree_bound = composition_log_degree_bound
            .checked_sub(COMPOSITION_LOG_SPLIT)
            .ok_or(VmAirProgramError::CompositionSplitUnderflow {
                composition_log_degree_bound,
            })?;
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
            core::slice::from_ref(&unresolved),
            &sampled_indices,
            sample_coordinates.len(),
            composition_samples,
            max_log_degree_bound,
        )?;
        let component = resolve_component(unresolved, &sampled_indices)?;
        Ok(Self {
            log_size,
            component,
            column_log_sizes,
            sample_coordinates,
            sample_point_offsets,
            composition_samples,
            max_log_degree_bound,
        })
    }

    pub const fn column_log_sizes(&self) -> &TreeVec<Vec<u32>> {
        &self.column_log_sizes
    }

    pub fn sample_coordinates(&self) -> &[SampleCoordinate] {
        &self.sample_coordinates
    }

    pub fn sample_point_offsets(&self) -> &[CirclePointIndex] {
        &self.sample_point_offsets
    }

    pub const fn max_log_degree_bound(&self) -> u32 {
        self.max_log_degree_bound
    }

    pub const fn air_instruction_count(&self) -> usize {
        self.component.constraint_count
    }

    /// Evaluates the detached AIR and its split-composition equality.
    pub fn evaluate(
        &self,
        sampled_values: &[Rec],
        claimed_sum: Rec,
        relation_parameters: &HashMap<String, Rec>,
        random_coefficient: Rec,
        oods_point: &OodsPointCircuit,
    ) -> Result<VmAirEvaluation, VmAirProgramError> {
        if sampled_values.len() != self.sample_coordinates.len() {
            return Err(VmAirProgramError::SampledValueCountMismatch {
                expected: self.sample_coordinates.len(),
                actual: sampled_values.len(),
            });
        }
        validate_relation_parameters(Relations::DESCRIPTORS.as_slice(), relation_parameters)?;
        let denominator_inverse = coset_vanishing_inverse(oods_point, self.max_log_degree_bound)?;
        let component = poseidon2_component(self.log_size);
        let mask = self
            .component
            .sampled_mask
            .clone()
            .map_cols(|sampled_column| {
                sampled_column
                    .into_iter()
                    .map(|sample| sampled_values[sample].clone())
                    .collect::<Vec<_>>()
            });
        let evaluator = CircuitPointEvaluator::new(
            0,
            mask,
            self.component.mask_offsets.clone(),
            Rec::zero(),
            random_coefficient,
            denominator_inverse,
            claimed_sum,
            self.log_size,
            relation_parameters,
        );
        let evaluator = (*component).evaluate_dynamic_relations(evaluator);
        let air_value = evaluator.finish(self.component.constraint_count)?;
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
        let equality = air_value.clone() - claimed_value.clone();
        Ok(VmAirEvaluation {
            air_value,
            claimed_value,
            equality,
        })
    }
}

fn poseidon2_component(log_size: u32) -> FrameworkComponent<air::poseidon2::component::air::Eval> {
    let mut allocator = TraceLocationAllocator::default();
    air::poseidon2::component::air::Component::new(
        &mut allocator,
        air::poseidon2::component::air::Eval {
            log_size,
            relations: Relations::dummy(),
        },
        SecureField::zero(),
    )
}

/// Computed and proof-claimed sides of the OODS composition assertion.
#[derive(Clone, Debug)]
pub struct VmAirEvaluation {
    pub air_value: Rec,
    pub claimed_value: Rec,
    pub equality: Rec,
}

fn zero_claimed_sums() -> ClaimedSum {
    ClaimedSum::from_component_values([SecureField::zero(); VM_AIR_COMPONENT_COUNT])
}

fn build_components(claim: &Claim, relations: Relations, claimed_sums: &ClaimedSum) -> Components {
    let ids = PreProcessedTrace::column_ids();
    let mut allocator = TraceLocationAllocator::new_with_preprocessed_columns(&ids);
    Components::new(claim, &mut allocator, relations, claimed_sums)
}

#[derive(Default)]
struct ProgramCollector {
    components: Vec<UnresolvedComponentProgram>,
    error: Option<VmAirProgramError>,
}

impl ComponentVisitor for ProgramCollector {
    fn visit<E: FrameworkEval>(
        &mut self,
        component: &FrameworkComponent<E>,
        _claimed_sum: SecureField,
    ) {
        if self.error.is_some() {
            return;
        }
        let index = self.components.len();
        let Some(&name) = COMPONENT_NAMES.get(index) else {
            self.error = Some(VmAirProgramError::ComponentNameMissing { index });
            return;
        };
        match compile_component(index, name, component) {
            Ok(component) => self.components.push(component),
            Err(error) => self.error = Some(error),
        }
    }
}

fn compile_component<E: FrameworkEval>(
    index: usize,
    name: &'static str,
    component: &FrameworkComponent<E>,
) -> Result<UnresolvedComponentProgram, VmAirProgramError> {
    let log_size = component.log_size();
    let info = (**component).evaluate(InfoEvaluator::new(
        log_size,
        Vec::new(),
        SecureField::zero(),
    ));
    let mut sampled_mask = TreeVec::new(vec![Vec::new(); info.mask_offsets.len().max(1)]);
    for (interaction, columns) in info.mask_offsets.iter().enumerate() {
        let location = component
            .trace_locations()
            .iter()
            .find(|location| location.tree_index == interaction)
            .ok_or(VmAirProgramError::TraceLocationMissing {
                component: index,
                interaction,
            })?;
        if location.col_end - location.col_start != columns.len() {
            return Err(VmAirProgramError::TraceColumnCountMismatch {
                component: index,
                interaction,
                expected: location.col_end - location.col_start,
                actual: columns.len(),
            });
        }
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
    if info.preprocessed_columns.len() != preprocessed_columns.len() {
        return Err(VmAirProgramError::ComponentPreprocessedLengthMismatch {
            component: index,
            formal: info.preprocessed_columns.len(),
            allocated: preprocessed_columns.len(),
        });
    }
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
    let mut mask_offsets = info.mask_offsets.clone();
    if mask_offsets.is_empty() {
        mask_offsets.push(Vec::new());
    }
    mask_offsets[PREPROCESSED_TRACE_IDX] = vec![vec![0]; preprocessed_columns.len()];
    Ok(UnresolvedComponentProgram {
        name,
        log_size,
        constraint_count: info.n_constraints,
        sampled_mask,
        mask_offsets,
        preprocessed_columns,
    })
}

fn validate_preprocessed_log_sizes(
    components: &[UnresolvedComponentProgram],
    preprocessed_log_sizes: &[u32],
) -> Result<(), VmAirProgramError> {
    for (component, program) in components.iter().enumerate() {
        for &column in &program.preprocessed_columns {
            let expected = *preprocessed_log_sizes
                .get(column)
                .ok_or(VmAirProgramError::PreprocessedColumnOutOfRange { component, column })?;
            if program.log_size != expected {
                return Err(VmAirProgramError::PreprocessedLogSizeMismatch {
                    component,
                    column,
                    expected,
                    actual: program.log_size,
                });
            }
        }
    }
    Ok(())
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
            for point in 0..points.len() {
                column_indices.push(coordinates.len());
                coordinates.push(SampleCoordinate {
                    tree,
                    column,
                    point,
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
) -> Result<Vec<CirclePointIndex>, VmAirProgramError> {
    let trace_step = stwo::core::poly::circle::CanonicCoset::new(max_log_degree_bound).step_size();
    let mut offsets: Vec<Option<CirclePointIndex>> = vec![None; sample_count];
    for (component_index, component) in components.iter().enumerate() {
        for (interaction, columns) in component.sampled_mask.iter().enumerate() {
            let component_offsets = component.mask_offsets.get(interaction).ok_or(
                VmAirProgramError::ComponentMaskInteractionMissing {
                    component: component_index,
                    interaction,
                },
            )?;
            if component_offsets.len() != columns.len() {
                return Err(VmAirProgramError::ComponentMaskColumnCountMismatch {
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
                    return Err(VmAirProgramError::ComponentMaskPointCountMismatch {
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
                            return Err(VmAirProgramError::SamplePointOffsetConflict {
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
            offset.ok_or(VmAirProgramError::SamplePointOffsetMissing { sample })
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
) -> Result<ComponentProgram, VmAirProgramError> {
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
    Ok(ComponentProgram {
        name: component.name,
        log_size: component.log_size,
        constraint_count: component.constraint_count,
        sampled_mask,
        mask_offsets: component.mask_offsets,
    })
}

fn sampled_index(
    sampled_indices: &TreeVec<Vec<Vec<usize>>>,
    tree: usize,
    column: usize,
    point: usize,
) -> Result<usize, VmAirProgramError> {
    sampled_indices
        .get(tree)
        .and_then(|columns| columns.get(column))
        .and_then(|points| points.get(point))
        .copied()
        .ok_or(VmAirProgramError::SampleCoordinateOutOfRange {
            tree,
            column,
            point,
        })
}

fn validate_relation_parameters(
    descriptors: &[RelationDescriptor],
    parameters: &HashMap<String, Rec>,
) -> Result<(), VmAirProgramError> {
    for descriptor in descriptors {
        require_relation_parameter(parameters, &format!("{}_z", descriptor.name))?;
        for index in 0..descriptor.size {
            require_relation_parameter(parameters, &format!("{}_alpha{index}", descriptor.name))?;
        }
    }
    Ok(())
}

fn require_relation_parameter(
    parameters: &HashMap<String, Rec>,
    name: &str,
) -> Result<(), VmAirProgramError> {
    if parameters.contains_key(name) {
        Ok(())
    } else {
        Err(VmAirProgramError::RelationParameterMissing { name: name.into() })
    }
}

struct CircuitEvaluationVisitor<'a> {
    program: &'a [ComponentProgram],
    sampled_values: &'a [Rec],
    claimed_sums: &'a [Rec],
    relation_parameters: &'a HashMap<String, Rec>,
    random_coefficient: Rec,
    denominator_inverse: Rec,
    accumulator: Rec,
    next_component: usize,
    error: Option<VmAirProgramError>,
}

impl CircuitEvaluationVisitor<'_> {
    fn finish(self) -> Result<Rec, VmAirProgramError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        if self.next_component != self.program.len() {
            return Err(VmAirProgramError::ComponentCountMismatch {
                expected: self.program.len(),
                actual: self.next_component,
            });
        }
        Ok(self.accumulator)
    }
}

impl DynamicRelationComponentVisitor for CircuitEvaluationVisitor<'_> {
    fn visit<E>(&mut self, component: &FrameworkComponent<E>, _claimed_sum: SecureField)
    where
        E: FrameworkEval + DynamicRelationFrameworkEval,
    {
        if self.error.is_some() {
            return;
        }
        let index = self.next_component;
        self.next_component += 1;
        let Some(program) = self.program.get(index) else {
            self.error = Some(VmAirProgramError::UnexpectedComponent { index });
            return;
        };
        if component.log_size() != program.log_size {
            self.error = Some(VmAirProgramError::ComponentLogSizeMismatch {
                component: index,
                expected: program.log_size,
                actual: component.log_size(),
            });
            return;
        }
        let mask = program.sampled_mask.clone().map_cols(|sampled_column| {
            sampled_column
                .into_iter()
                .map(|sample| self.sampled_values[sample].clone())
                .collect::<Vec<_>>()
        });
        let evaluator = CircuitPointEvaluator::new(
            index,
            mask,
            program.mask_offsets.clone(),
            self.accumulator.clone(),
            self.random_coefficient.clone(),
            self.denominator_inverse.clone(),
            self.claimed_sums[index].clone(),
            program.log_size,
            self.relation_parameters,
        );
        let evaluator = (**component).evaluate_dynamic_relations(evaluator);
        match evaluator.finish(program.constraint_count) {
            Ok(accumulator) => self.accumulator = accumulator,
            Err(error) => self.error = Some(error),
        }
    }
}

struct CircuitPointEvaluator<'a> {
    component: usize,
    mask: TreeVec<Vec<Vec<Rec>>>,
    mask_offsets: TreeVec<Vec<Vec<isize>>>,
    column_index: Vec<usize>,
    random_coefficient: Rec,
    denominator_inverse: Rec,
    accumulator: Rec,
    relation_parameters: &'a HashMap<String, Rec>,
    constraint_count: usize,
    error: Option<VmAirProgramError>,
    logup: CircuitLogup,
}

impl<'a> CircuitPointEvaluator<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        component: usize,
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
            logup: CircuitLogup::new(INTERACTION_TRACE_IDX, cumsum_shift),
        }
    }

    fn finish(self, expected_constraints: usize) -> Result<Rec, VmAirProgramError> {
        if let Some(error) = self.error {
            return Err(error);
        }
        if self.constraint_count != expected_constraints {
            return Err(VmAirProgramError::DynamicConstraintCountMismatch {
                component: self.component,
                expected: expected_constraints,
                actual: self.constraint_count,
            });
        }
        for (interaction, (consumed, columns)) in
            self.column_index.iter().zip(self.mask.iter()).enumerate()
        {
            if *consumed != columns.len() {
                return Err(VmAirProgramError::ComponentMaskNotFullyConsumed {
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
                self.error = Some(VmAirProgramError::RelationParameterMissing { name });
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
            self.error = Some(VmAirProgramError::ComponentMaskInteractionMissing {
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
            self.error = Some(VmAirProgramError::ComponentMaskColumnMissing {
                component: self.component,
                interaction,
                column,
            });
            return core::array::from_fn(|_| Rec::zero());
        };
        if expected_offsets.as_slice() != offsets {
            self.error = Some(VmAirProgramError::DynamicMaskOffsetMismatch {
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
            self.error = Some(VmAirProgramError::ComponentMaskColumnMissing {
                component: self.component,
                interaction,
                column,
            });
            return core::array::from_fn(|_| Rec::zero());
        };
        if values.len() != N {
            self.error = Some(VmAirProgramError::ComponentMaskPointCountMismatch {
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
        let Some(constraint_count) = self.constraint_count.checked_add(1) else {
            self.error = Some(VmAirProgramError::DynamicConstraintCountOverflow {
                component: self.component,
            });
            return;
        };
        self.constraint_count = constraint_count;
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

impl DynamicRelationEvalAtRow for CircuitPointEvaluator<'_> {
    fn add_to_named_relation(
        &mut self,
        relation: &'static str,
        multiplicity: Self::EF,
        values: &[Self::F],
    ) {
        let Some(descriptor) = Relations::DESCRIPTORS
            .iter()
            .find(|descriptor| descriptor.name == relation)
        else {
            self.error = Some(VmAirProgramError::RelationDescriptorMissing {
                name: relation.into(),
            });
            return;
        };
        if values.len() > descriptor.size {
            self.error = Some(VmAirProgramError::RelationArityExceeded {
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

/// Invalid fixed VM AIR profile, mask layout, or per-proof assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VmAirProgramError {
    ComponentLogSizeOutOfRange {
        component: usize,
        log_size: u32,
    },
    PreprocessedRegistryLengthMismatch {
        ids: usize,
        log_sizes: usize,
    },
    ComponentCountMismatch {
        expected: usize,
        actual: usize,
    },
    ComponentNameMissing {
        index: usize,
    },
    TraceLocationMissing {
        component: usize,
        interaction: usize,
    },
    TraceColumnCountMismatch {
        component: usize,
        interaction: usize,
        expected: usize,
        actual: usize,
    },
    ComponentPreprocessedLengthMismatch {
        component: usize,
        formal: usize,
        allocated: usize,
    },
    PreprocessedColumnOutOfRange {
        component: usize,
        column: usize,
    },
    PreprocessedLogSizeMismatch {
        component: usize,
        column: usize,
        expected: u32,
        actual: u32,
    },
    AirInstructionCountOverflow,
    CompositionSplitUnderflow {
        composition_log_degree_bound: u32,
    },
    MaxLogDegreeBoundOutOfRange {
        minimum: u32,
        actual: u32,
    },
    SampleCoordinateOutOfRange {
        tree: usize,
        column: usize,
        point: usize,
    },
    SampledValueCountMismatch {
        expected: usize,
        actual: usize,
    },
    ClaimedSumCountMismatch {
        expected: usize,
        actual: usize,
    },
    RelationParameterMissing {
        name: String,
    },
    UnexpectedComponent {
        index: usize,
    },
    ComponentLogSizeMismatch {
        component: usize,
        expected: u32,
        actual: u32,
    },
    ComponentMaskInteractionMissing {
        component: usize,
        interaction: usize,
    },
    ComponentMaskColumnMissing {
        component: usize,
        interaction: usize,
        column: usize,
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
    DynamicMaskOffsetMismatch {
        component: usize,
        interaction: usize,
        column: usize,
        expected: Vec<isize>,
        actual: Vec<isize>,
    },
    ComponentMaskNotFullyConsumed {
        component: usize,
        interaction: usize,
        expected: usize,
        actual: usize,
    },
    DynamicConstraintCountMismatch {
        component: usize,
        expected: usize,
        actual: usize,
    },
    DynamicConstraintCountOverflow {
        component: usize,
    },
    SamplePointOffsetConflict {
        sample: usize,
        expected: usize,
        actual: usize,
    },
    SamplePointOffsetMissing {
        sample: usize,
    },
    RelationDescriptorMissing {
        name: String,
    },
    RelationArityExceeded {
        name: String,
        maximum: usize,
        actual: usize,
    },
    Oods(OodsCircuitError),
}

impl From<OodsCircuitError> for VmAirProgramError {
    fn from(value: OodsCircuitError) -> Self {
        Self::Oods(value)
    }
}

impl fmt::Display for VmAirProgramError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for VmAirProgramError {}

#[cfg(test)]
mod tests {
    use prover::poseidon2_channel::Poseidon2M31Channel;
    use stwo::core::channel::Channel;
    use stwo::core::fields::m31::M31;

    use super::*;
    use crate::air_relation_parameters::{RelationChallengeCircuit, bind_relation_parameters};
    use crate::oods_circuit::oods_point_from_seed;
    use crate::recorder::CircuitBuilder;

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

    fn relation_parameters() -> HashMap<String, Rec> {
        let mut channel = Poseidon2M31Channel::default();
        let challenges = Relations::DESCRIPTORS
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
        bind_relation_parameters(&Relations::DESCRIPTORS, &challenges)
            .expect("the generated registry owns every native draw")
    }

    fn inflate_samples(
        coordinates: &[SampleCoordinate],
        values: &[SecureField],
    ) -> TreeVec<Vec<Vec<SecureField>>> {
        let tree_count = coordinates
            .iter()
            .map(|coordinate| coordinate.tree)
            .max()
            .expect("VM AIR has sampled columns")
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
    fn generated_component_order_is_preserved() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        assert_eq!(
            program.component_names().collect::<Vec<_>>(),
            COMPONENT_NAMES
        );
    }

    #[test]
    fn sample_layout_has_four_commitment_trees() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        assert_eq!(
            program
                .sample_coordinates()
                .iter()
                .map(|coordinate| coordinate.tree)
                .max(),
            Some(3)
        );
    }

    #[test]
    fn sample_point_offsets_match_stwo_mask_geometry() {
        let log_sizes = component_log_sizes();
        let claim = Claim::from_component_log_sizes(log_sizes);
        let components = build_components(&claim, Relations::dummy(), &zero_claimed_sums());
        let core_components = CoreComponents {
            components: components.verifiers(),
            n_preprocessed_columns: PreProcessedTrace::column_ids().len(),
        };
        let program = VmAirProgram::new(log_sizes).expect("fixture profile is valid");
        let seed = SecureField::from_m31_array([
            M31::from(11),
            M31::from(13),
            M31::from(17),
            M31::from(19),
        ]);
        let oods = oods_point_from_seed(Rec::from(seed)).expect("fixture seed maps to the circle");
        let point = CirclePoint {
            x: oods.x.value(),
            y: oods.y.value(),
        };
        let mut native = core_components.mask_points(point, program.max_log_degree_bound(), false);
        native.push(vec![vec![point]; COMPOSITION_SAMPLE_COUNT]);
        let native = native
            .iter()
            .flatten()
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let reconstructed = program
            .sample_point_offsets()
            .iter()
            .map(|offset| point + offset.to_point().into_ef())
            .collect::<Vec<_>>();
        assert_eq!(reconstructed, native);
    }

    #[test]
    fn default_degree_bound_matches_stwo_split_composition_geometry() {
        let log_sizes = component_log_sizes();
        let claim = Claim::from_component_log_sizes(log_sizes);
        let components = build_components(&claim, Relations::dummy(), &zero_claimed_sums());
        let core_components = CoreComponents {
            components: components.verifiers(),
            n_preprocessed_columns: PreProcessedTrace::column_ids().len(),
        };
        let program = VmAirProgram::new(log_sizes).expect("fixture profile is valid");
        assert_eq!(
            program.max_log_degree_bound(),
            core_components.composition_log_degree_bound() - COMPOSITION_LOG_SPLIT
        );
    }

    #[test]
    fn explicit_lifting_bound_controls_composition_column_degrees() {
        let baseline = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let lifted = VmAirProgram::new_with_max_log_degree_bound(
            component_log_sizes(),
            baseline.max_log_degree_bound() + 1,
        )
        .expect("one extra lifting bit is supported");
        assert_eq!(
            lifted.column_log_sizes().last(),
            Some(&vec![
                baseline.max_log_degree_bound() + 1;
                COMPOSITION_SAMPLE_COUNT
            ])
        );
    }

    #[test]
    fn degree_bound_below_the_split_composition_minimum_is_rejected() {
        let baseline = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        assert_eq!(
            VmAirProgram::new_with_max_log_degree_bound(
                component_log_sizes(),
                baseline.max_log_degree_bound() - 1,
            )
            .map(|_| ()),
            Err(VmAirProgramError::MaxLogDegreeBoundOutOfRange {
                minimum: baseline.max_log_degree_bound(),
                actual: baseline.max_log_degree_bound() - 1,
            })
        );
    }

    #[test]
    fn lookup_component_cannot_select_a_false_preprocessed_size() {
        let mut log_sizes = component_log_sizes();
        let bitwise = COMPONENT_NAMES
            .iter()
            .position(|name| *name == "bitwise")
            .expect("bitwise is a generated lookup component");
        log_sizes[bitwise] -= 1;
        assert!(matches!(
            VmAirProgram::new(log_sizes),
            Err(VmAirProgramError::PreprocessedLogSizeMismatch { component, .. })
                if component == bitwise
        ));
    }

    #[test]
    fn dynamic_vm_composition_matches_stwo_point_evaluation() {
        let log_sizes = component_log_sizes();
        let program = VmAirProgram::new(log_sizes).expect("fixture profile is valid");
        let mut native_channel = Poseidon2M31Channel::default();
        let relations = Relations::draw(&mut native_channel);
        let claimed_sum_values = core::array::from_fn(|index| {
            SecureField::from_m31_array([
                M31::from(index as u32 + 2),
                M31::from(index as u32 + 3),
                M31::from(index as u32 + 4),
                M31::from(index as u32 + 5),
            ])
        });
        let claimed_sums = ClaimedSum::from_component_values(claimed_sum_values);
        let components = build_components(
            &Claim::from_component_log_sizes(log_sizes),
            relations,
            &claimed_sums,
        );
        let core_components = CoreComponents {
            components: components.verifiers(),
            n_preprocessed_columns: PreProcessedTrace::column_ids().len(),
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
                &relation_parameters(),
                random_input,
                &oods,
            )
            .expect("complete streaming inputs evaluate");
        assert_eq!(actual.air_value.value(), native);
    }

    #[test]
    fn missing_relation_power_is_rejected_before_streaming() {
        let program = VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        let mut parameters = relation_parameters();
        parameters.remove("memory_access_alpha6");
        let sampled_values = vec![Rec::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![Rec::zero(); VM_AIR_COMPONENT_COUNT];
        let oods = oods_point_from_seed(Rec::from(BaseField::from(3)))
            .expect("fixture seed maps to the circle");
        assert!(matches!(
            program.evaluate(
                &sampled_values,
                &claimed_sums,
                &parameters,
                Rec::one(),
                &oods,
            ),
            Err(VmAirProgramError::RelationParameterMissing { name })
                if name == "memory_access_alpha6"
        ));
    }

    #[test]
    fn dynamic_evaluator_rejects_mask_offset_drift() {
        let mut program =
            VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        program.components[0].mask_offsets[1][0][0] = 1;
        let sampled_values = vec![Rec::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![Rec::zero(); VM_AIR_COMPONENT_COUNT];
        let oods = oods_point_from_seed(Rec::from(BaseField::from(3)))
            .expect("fixture seed maps to the circle");
        assert!(matches!(
            program.evaluate(
                &sampled_values,
                &claimed_sums,
                &relation_parameters(),
                Rec::one(),
                &oods,
            ),
            Err(VmAirProgramError::DynamicMaskOffsetMismatch { component: 0, .. })
        ));
    }

    #[test]
    fn dynamic_evaluator_rejects_constraint_count_drift() {
        let mut program =
            VmAirProgram::new(component_log_sizes()).expect("fixture profile is valid");
        program.components[0].constraint_count += 1;
        let sampled_values = vec![Rec::zero(); program.sample_coordinates().len()];
        let claimed_sums = vec![Rec::zero(); VM_AIR_COMPONENT_COUNT];
        let oods = oods_point_from_seed(Rec::from(BaseField::from(3)))
            .expect("fixture seed maps to the circle");
        assert!(matches!(
            program.evaluate(
                &sampled_values,
                &claimed_sums,
                &relation_parameters(),
                Rec::one(),
                &oods,
            ),
            Err(VmAirProgramError::DynamicConstraintCountMismatch { component: 0, .. })
        ));
    }

    #[test]
    fn detached_poseidon2_program_has_frozen_dimensions() {
        let program = Poseidon2AirProgram::new(11).expect("Poseidon2 profile is valid");
        assert_eq!(
            (
                program.column_log_sizes().iter().flatten().count(),
                program.sample_coordinates().len(),
                program.air_instruction_count(),
                program.max_log_degree_bound(),
            ),
            (461, 465, 432, 11),
        );
    }
}
