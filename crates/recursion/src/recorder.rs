//! Operation recorder: compiles an inner AIR's `evaluate()` into an
//! arithmetic-operation arena (docs/recursion.md, M5).
//!
//! `Recorder` implements `EvalAtRow` with a handle field type, so running any
//! component's `FrameworkEval::evaluate` — the same single-source code the
//! prover and verifier execute — records the composition-polynomial
//! computation as explicit QM31 operations over mask inputs. The arena is the
//! circuit the composition-check component lowers into recursion-AIR rows
//! (mul/inv via the existing components, wiring via relations); an edit to
//! `define_trace_tables!` changes the recorded circuit in the same
//! compilation, with no constraint copy.

use core::cell::RefCell;
use core::ops::{Add, AddAssign, Mul, Neg, Sub};
use std::rc::Rc;

use num_traits::{One, Zero};
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::{SECURE_EXTENSION_DEGREE, SecureField};
use stwo_constraint_framework::logup::LogupAtRow;
use stwo_constraint_framework::{EvalAtRow, INTERACTION_TRACE_IDX};

/// One recorded operation over arena nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// A mask input (interaction, column, offset slot).
    Input,
    /// A constant embedded in the constraint system.
    Const,
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Neg(usize),
    Inverse(usize),
}

/// A recorded node: the operation and its evaluated value.
#[derive(Clone, Copy, Debug)]
pub struct Node {
    pub op: Op,
    pub value: SecureField,
}

/// The growing list of operations.
#[derive(Default, Debug)]
pub struct Arena {
    pub nodes: Vec<Node>,
}

impl Arena {
    fn push(&mut self, op: Op, value: SecureField) -> usize {
        self.nodes.push(Node { op, value });
        self.nodes.len() - 1
    }
}

type SharedArena = Rc<RefCell<Arena>>;

/// Fixed arithmetic circuit whose designated outputs must all be zero.
#[derive(Debug)]
pub struct ConstraintCircuit {
    arena: SharedArena,
    outputs: Vec<usize>,
}

impl ConstraintCircuit {
    pub fn arena(&self) -> core::cell::Ref<'_, Arena> {
        self.arena.borrow()
    }

    pub fn outputs(&self) -> &[usize] {
        &self.outputs
    }
}

/// Value-aware builder for fixed zero-constraint circuits.
#[derive(Debug, Default)]
pub struct CircuitBuilder {
    arena: SharedArena,
    outputs: Vec<usize>,
}

impl CircuitBuilder {
    pub fn input(&mut self, value: SecureField) -> (usize, Rec) {
        let id = self.arena.borrow_mut().push(Op::Input, value);
        (
            id,
            Rec::Node {
                id,
                value,
                arena: self.arena.clone(),
            },
        )
    }

    pub fn constrain_zero(&mut self, constraint: Rec) {
        let output = constraint.node_id(&self.arena);
        self.outputs.push(output);
    }

    pub fn finish(self) -> ConstraintCircuit {
        ConstraintCircuit {
            arena: self.arena,
            outputs: self.outputs,
        }
    }
}

/// A value handle: either a pure constant or a node in the shared arena.
///
/// Constants fold eagerly; any operation touching a node records a new node.
#[derive(Clone, Debug)]
pub enum Rec {
    Const(SecureField),
    Node {
        id: usize,
        value: SecureField,
        arena: SharedArena,
    },
}

impl Rec {
    pub fn value(&self) -> SecureField {
        match self {
            Rec::Const(value) => *value,
            Rec::Node { value, .. } => *value,
        }
    }

    /// Materialize this handle as an arena node (constants become Const nodes).
    fn node_id(&self, arena: &SharedArena) -> usize {
        match self {
            Rec::Const(value) => arena.borrow_mut().push(Op::Const, *value),
            Rec::Node { id, .. } => *id,
        }
    }

    fn arena(&self) -> Option<&SharedArena> {
        match self {
            Rec::Const(_) => None,
            Rec::Node { arena, .. } => Some(arena),
        }
    }

    fn binary(
        lhs: &Rec,
        rhs: &Rec,
        fold: impl Fn(SecureField, SecureField) -> SecureField,
        op: impl Fn(usize, usize) -> Op,
    ) -> Rec {
        let value = fold(lhs.value(), rhs.value());
        let arena = match lhs.arena().or_else(|| rhs.arena()) {
            // Both constants: fold without recording.
            None => return Rec::Const(value),
            Some(arena) => arena.clone(),
        };
        let lhs_id = lhs.node_id(&arena);
        let rhs_id = rhs.node_id(&arena);
        let id = arena.borrow_mut().push(op(lhs_id, rhs_id), value);
        Rec::Node { id, value, arena }
    }
}

impl PartialEq for Rec {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl From<BaseField> for Rec {
    fn from(value: BaseField) -> Self {
        Rec::Const(value.into())
    }
}

impl From<SecureField> for Rec {
    fn from(value: SecureField) -> Self {
        Rec::Const(value)
    }
}

impl Add for Rec {
    type Output = Rec;
    fn add(self, rhs: Rec) -> Rec {
        Rec::binary(&self, &rhs, |a, b| a + b, Op::Add)
    }
}

impl Sub for Rec {
    type Output = Rec;
    fn sub(self, rhs: Rec) -> Rec {
        Rec::binary(&self, &rhs, |a, b| a - b, Op::Sub)
    }
}

impl Mul for Rec {
    type Output = Rec;
    fn mul(self, rhs: Rec) -> Rec {
        Rec::binary(&self, &rhs, |a, b| a * b, Op::Mul)
    }
}

impl AddAssign for Rec {
    fn add_assign(&mut self, rhs: Rec) {
        *self = self.clone() + rhs;
    }
}

impl AddAssign<BaseField> for Rec {
    fn add_assign(&mut self, rhs: BaseField) {
        *self = self.clone() + Rec::from(rhs);
    }
}

impl Mul<BaseField> for Rec {
    type Output = Rec;
    fn mul(self, rhs: BaseField) -> Rec {
        self * Rec::from(rhs)
    }
}

impl Mul<SecureField> for Rec {
    type Output = Rec;
    fn mul(self, rhs: SecureField) -> Rec {
        self * Rec::from(rhs)
    }
}

impl Add<SecureField> for Rec {
    type Output = Rec;
    fn add(self, rhs: SecureField) -> Rec {
        self + Rec::from(rhs)
    }
}

impl Add<BaseField> for Rec {
    type Output = Rec;
    fn add(self, rhs: BaseField) -> Rec {
        self + Rec::from(rhs)
    }
}

impl Sub<SecureField> for Rec {
    type Output = Rec;
    fn sub(self, rhs: SecureField) -> Rec {
        self - Rec::from(rhs)
    }
}

impl Neg for Rec {
    type Output = Rec;
    fn neg(self) -> Rec {
        match self {
            Rec::Const(value) => Rec::Const(-value),
            Rec::Node { id, value, arena } => {
                let id = arena.borrow_mut().push(Op::Neg(id), -value);
                Rec::Node {
                    id,
                    value: -value,
                    arena,
                }
            }
        }
    }
}

impl Zero for Rec {
    fn zero() -> Self {
        Rec::Const(SecureField::zero())
    }
    fn is_zero(&self) -> bool {
        self.value().is_zero()
    }
}

impl One for Rec {
    fn one() -> Self {
        Rec::Const(SecureField::one())
    }
}

impl core::ops::MulAssign for Rec {
    fn mul_assign(&mut self, rhs: Rec) {
        *self = self.clone() * rhs;
    }
}

impl FieldExpOps for Rec {
    fn inverse(&self) -> Self {
        match self {
            Rec::Const(value) => Rec::Const(value.inverse()),
            Rec::Node { id, value, arena } => {
                let inv = value.inverse();
                let new_id = arena.borrow_mut().push(Op::Inverse(*id), inv);
                Rec::Node {
                    id: new_id,
                    value: inv,
                    arena: arena.clone(),
                }
            }
        }
    }
}

/// Records an inner AIR's composition evaluation over given mask values.
pub struct Recorder {
    pub arena: SharedArena,
    /// Mask values per interaction per column (offsets flattened in order).
    pub mask: Vec<Vec<Vec<SecureField>>>,
    pub col_index: Vec<usize>,
    /// alpha (the constraint-combination coefficient) as a recorded input.
    alpha: Rec,
    /// 1 / V(oods_point) as a recorded input.
    denom_inverse: Rec,
    /// Accumulated combination: acc = acc * alpha + denom_inverse * constraint.
    pub accumulation: Rec,
    pub logup: LogupAtRow<Self>,
}

impl Recorder {
    pub fn new(
        mask: Vec<Vec<Vec<SecureField>>>,
        alpha: SecureField,
        denom_inverse: SecureField,
        log_size: u32,
        claimed_sum: SecureField,
    ) -> Self {
        let arena: SharedArena = Rc::new(RefCell::new(Arena::default()));
        let input = |value: SecureField, arena: &SharedArena| {
            let id = arena.borrow_mut().push(Op::Input, value);
            Rec::Node {
                id,
                value,
                arena: arena.clone(),
            }
        };
        let alpha = input(alpha, &arena);
        let denom_inverse = input(denom_inverse, &arena);
        let col_index = vec![0; mask.len()];
        Self {
            arena,
            mask,
            col_index,
            alpha,
            denom_inverse,
            accumulation: Rec::Const(SecureField::zero()),
            logup: LogupAtRow::new(INTERACTION_TRACE_IDX, claimed_sum, log_size),
        }
    }

    fn input(&self, value: SecureField) -> Rec {
        let id = self.arena.borrow_mut().push(Op::Input, value);
        Rec::Node {
            id,
            value,
            arena: self.arena.clone(),
        }
    }

    /// Start recording the next component of a composition: a new vanishing
    /// denominator (each component has its own domain) and a fresh LogUp
    /// context with that component's claimed sum, while the accumulation and
    /// mask cursor carry over — the semantics of
    /// `Components::eval_composition_polynomial_at_point`.
    pub fn next_component(
        &mut self,
        denom_inverse: SecureField,
        log_size: u32,
        claimed_sum: SecureField,
    ) {
        self.denom_inverse = self.input(denom_inverse);
        self.logup = LogupAtRow::new(INTERACTION_TRACE_IDX, claimed_sum, log_size);
    }
}

impl EvalAtRow for Recorder {
    type F = Rec;
    type EF = Rec;

    fn next_interaction_mask<const N: usize>(
        &mut self,
        interaction: usize,
        _offsets: [isize; N],
    ) -> [Self::F; N] {
        let col_index = self.col_index[interaction];
        self.col_index[interaction] += 1;
        let values = &self.mask[interaction][col_index];
        assert_eq!(values.len(), N);
        std::array::from_fn(|i| self.input(values[i]))
    }

    fn add_constraint<G>(&mut self, constraint: G)
    where
        Self::EF: Mul<G, Output = Self::EF>,
    {
        let weighted = self.denom_inverse.clone() * constraint;
        let scaled = Rec::binary(&self.accumulation, &self.alpha, |a, b| a * b, Op::Mul);
        self.accumulation = scaled + weighted;
    }

    fn combine_ef(values: [Self::F; SECURE_EXTENSION_DEGREE]) -> Self::EF {
        // (v0 + i v1) + (v2 + i v3) u over the secure field basis constants.
        let [v0, v1, v2, v3] = values;
        let u_0 = SecureField::from_m31_array([0.into(), 1.into(), 0.into(), 0.into()]);
        let u_1 = SecureField::from_m31_array([0.into(), 0.into(), 1.into(), 0.into()]);
        let u_2 = SecureField::from_m31_array([0.into(), 0.into(), 0.into(), 1.into()]);
        v0 + v1 * u_0 + v2 * u_1 + v3 * u_2
    }

    fn write_logup_frac(&mut self, fraction: stwo::core::Fraction<Self::EF, Self::EF>) {
        if self.logup.fracs.is_empty() {
            self.logup.is_finalized = false;
        }
        self.logup.fracs.push(fraction);
    }

    /// Same batching semantics as the framework's `logup_proxy!` (which is
    /// crate-private): per-fraction batch assignments, batches summed in
    /// order with cumulative-sum columns from the interaction masks, the
    /// shifted check on the last batch.
    fn finalize_logup_batched(&mut self, batching: &Vec<usize>) {
        assert!(!self.logup.is_finalized, "LogupAtRow was already finalized");
        let fracs = core::mem::take(&mut self.logup.fracs);
        assert_eq!(
            batching.len(),
            fracs.len(),
            "Batching must be of the same length as the number of entries"
        );
        let last_batch = *batching.iter().max().expect("at least one fraction");

        let mut fracs_by_batch: Vec<Vec<stwo::core::Fraction<Self::EF, Self::EF>>> =
            vec![Vec::new(); last_batch + 1];
        for (&batch, frac) in batching.iter().zip(fracs.iter()) {
            fracs_by_batch[batch].push(frac.clone());
        }
        assert!(
            fracs_by_batch.iter().all(|batch| !batch.is_empty()),
            "Batching must contain all consecutive batches"
        );

        let mut prev_col_cumsum = <Self::EF as Zero>::zero();
        for batch in &fracs_by_batch[..last_batch] {
            let cur_frac: stwo::core::Fraction<Self::EF, Self::EF> = batch.iter().cloned().sum();
            let [cur_cumsum] = self.next_extension_interaction_mask(self.logup.interaction, [0]);
            let diff = cur_cumsum.clone() - prev_col_cumsum.clone();
            prev_col_cumsum = cur_cumsum;
            self.add_constraint(diff * cur_frac.denominator - cur_frac.numerator);
        }
        let cur_frac: stwo::core::Fraction<Self::EF, Self::EF> =
            fracs_by_batch[last_batch].iter().cloned().sum();
        let [prev_row_cumsum, cur_cumsum] =
            self.next_extension_interaction_mask(self.logup.interaction, [-1, 0]);
        let diff = cur_cumsum - prev_row_cumsum - prev_col_cumsum.clone();
        let shifted_diff = diff + self.logup.cumsum_shift;
        self.add_constraint(shifted_diff * cur_frac.denominator - cur_frac.numerator);
        self.logup.is_finalized = true;
    }

    fn finalize_logup(&mut self) {
        let batches = (0..self.logup.fracs.len()).collect();
        self.finalize_logup_batched(&batches)
    }

    fn finalize_logup_in_pairs(&mut self) {
        let batches = (0..self.logup.fracs.len()).map(|n| n / 2).collect();
        self.finalize_logup_batched(&batches)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};
    use stwo::core::air::accumulation::PointEvaluationAccumulator;
    use stwo::core::pcs::TreeVec;
    use stwo_constraint_framework::{FrameworkEval, InfoEvaluator, PointEvaluator};

    fn random_secure(rng: &mut SmallRng) -> SecureField {
        SecureField::from_m31_array(std::array::from_fn(|_| {
            BaseField::from_u32_unchecked(rng.gen_range(0..(1 << 30)))
        }))
    }

    /// Record an inner component and check the accumulated value matches
    /// stwo's own PointEvaluator over the same masks — i.e. the recorded
    /// circuit faithfully computes the inner composition.
    #[test]
    fn test_recorder_matches_point_evaluator_on_lui() {
        let mut rng = SmallRng::seed_from_u64(0);
        let eval = prover::components::lui::air::Eval {
            log_size: 6,
            relations: prover::relations::Relations::dummy(),
        };

        // Mask shape from the single-source InfoEvaluator.
        let info = eval.evaluate(InfoEvaluator::empty());
        let mask_values: Vec<Vec<Vec<SecureField>>> = info
            .mask_offsets
            .iter()
            .map(|interaction| {
                interaction
                    .iter()
                    .map(|offsets| {
                        (0..offsets.len())
                            .map(|_| random_secure(&mut rng))
                            .collect()
                    })
                    .collect()
            })
            .collect();

        let alpha = random_secure(&mut rng);
        let denom_inverse = random_secure(&mut rng);
        let claimed_sum = random_secure(&mut rng);
        let log_size = 6;

        // Ground truth: stwo's point evaluation.
        let mut accumulator = PointEvaluationAccumulator::new(alpha);
        let mask_refs: TreeVec<Vec<&Vec<SecureField>>> =
            TreeVec::new(mask_values.iter().map(|t| t.iter().collect()).collect());
        let point_eval = PointEvaluator::new(
            mask_refs,
            &mut accumulator,
            denom_inverse,
            log_size,
            claimed_sum,
        );
        eval.evaluate(point_eval);
        let expected = accumulator.finalize();

        // Recorded circuit.
        let recorder = Recorder::new(mask_values, alpha, denom_inverse, log_size, claimed_sum);
        let recorder = eval.evaluate(recorder);
        assert_eq!(recorder.accumulation.value(), expected);
    }

    #[test]
    fn test_recorder_chains_components_like_the_host_accumulator() {
        let mut rng = SmallRng::seed_from_u64(2);
        let lui = prover::components::lui::air::Eval {
            log_size: 6,
            relations: prover::relations::Relations::dummy(),
        };
        let alu = prover::components::base_alu_imm::air::Eval {
            log_size: 5,
            relations: prover::relations::Relations::dummy(),
        };

        let masks_for = |eval: &dyn Fn() -> InfoEvaluator, rng: &mut SmallRng| {
            eval()
                .mask_offsets
                .iter()
                .map(|interaction| {
                    interaction
                        .iter()
                        .map(|offsets| (0..offsets.len()).map(|_| random_secure(rng)).collect())
                        .collect()
                })
                .collect::<Vec<Vec<Vec<SecureField>>>>()
        };
        let lui_masks = masks_for(&|| lui.evaluate(InfoEvaluator::empty()), &mut rng);
        let alu_masks = masks_for(&|| alu.evaluate(InfoEvaluator::empty()), &mut rng);

        let alpha = random_secure(&mut rng);
        let denoms = [random_secure(&mut rng), random_secure(&mut rng)];
        let sums = [random_secure(&mut rng), random_secure(&mut rng)];

        // Host ground truth: two PointEvaluators sharing one accumulator.
        let mut accumulator = PointEvaluationAccumulator::new(alpha);
        let lui_refs: TreeVec<Vec<&Vec<SecureField>>> =
            TreeVec::new(lui_masks.iter().map(|t| t.iter().collect()).collect());
        lui.evaluate(PointEvaluator::new(
            lui_refs,
            &mut accumulator,
            denoms[0],
            6,
            sums[0],
        ));
        let alu_refs: TreeVec<Vec<&Vec<SecureField>>> =
            TreeVec::new(alu_masks.iter().map(|t| t.iter().collect()).collect());
        alu.evaluate(PointEvaluator::new(
            alu_refs,
            &mut accumulator,
            denoms[1],
            5,
            sums[1],
        ));
        let expected = accumulator.finalize();

        // Recorded: one shared arena, next_component between evaluations.
        let mut recorder = Recorder::new(lui_masks, alpha, denoms[0], 6, sums[0]);
        recorder = lui.evaluate(recorder);
        recorder.mask = alu_masks;
        recorder.col_index = vec![0; recorder.mask.len()];
        recorder.next_component(denoms[1], 5, sums[1]);
        let recorder = alu.evaluate(recorder);
        assert_eq!(recorder.accumulation.value(), expected);
    }

    #[test]
    fn test_recorder_arena_contains_operations() {
        let eval = prover::components::lui::air::Eval {
            log_size: 4,
            relations: prover::relations::Relations::dummy(),
        };
        let info = eval.evaluate(InfoEvaluator::empty());
        let mut rng = SmallRng::seed_from_u64(1);
        let mask_values: Vec<Vec<Vec<SecureField>>> = info
            .mask_offsets
            .iter()
            .map(|interaction| {
                interaction
                    .iter()
                    .map(|offsets| {
                        (0..offsets.len())
                            .map(|_| random_secure(&mut rng))
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let recorder = Recorder::new(
            mask_values,
            random_secure(&mut rng),
            random_secure(&mut rng),
            4,
            random_secure(&mut rng),
        );
        let recorder = eval.evaluate(recorder);
        let arena = recorder.arena.borrow();
        // The circuit has inputs and arithmetic: a faithful compilation of
        // the inner constraints, produced by running the same evaluate().
        assert!(arena.nodes.iter().any(|n| matches!(n.op, Op::Mul(_, _))));
    }

    #[test]
    fn constraint_builder_keeps_each_zero_check_as_a_distinct_output() {
        let mut builder = CircuitBuilder::default();
        let (_, three) = builder.input(SecureField::from(BaseField::from(3)));
        let (_, four) = builder.input(SecureField::from(BaseField::from(4)));
        builder.constrain_zero(three + four - Rec::from(BaseField::from(7)));
        let circuit = builder.finish();
        let output = circuit.outputs()[0];
        assert_eq!(
            (circuit.outputs().len(), circuit.arena().nodes[output].value),
            (1, SecureField::zero())
        );
    }
}
