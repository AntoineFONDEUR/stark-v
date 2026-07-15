//! Arena lowering: turn a recorded composition circuit into recursion-AIR
//! witness rows and public claims (docs/recursion.md, M5).
//!
//! Arithmetic nodes become rows of `qm31_mul`, `qm31_inv`, and `linear_ops`;
//! inputs and constants become public `wire` emissions; the structure of
//! every arithmetic node is a public `op_def` emission; and the accumulated
//! output is publicly consumed. The verifier re-records the canonical arena
//! by running the same inner `evaluate()` over the public input values —
//! structure and values alike flow from the single source.

use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::SecureField;
use stwo_constraint_framework::Relation;

use crate::prover::RecursionTraces;
use crate::recorder::{Arena, Op};
use crate::relations::{RecursionRelations, op_kind};

/// Public interface of a lowered circuit: input/constant values and the
/// claimed output, all bound as wire claims.
#[derive(Clone, Debug)]
pub struct CircuitClaim {
    pub circuit_id: u32,
    /// (node_id, value) of every Input node, in arena order
    /// (alpha, denom_inverse, then masks in evaluate order).
    pub inputs: Vec<(u32, SecureField)>,
    /// The inner component's log size (fixes the cumsum-shift constant).
    pub inner_log_size: u32,
    /// The inner component's claimed LogUp sum (same role).
    pub inner_claimed_sum: SecureField,
    /// The accumulated output node and its claimed value.
    pub output: (u32, SecureField),
}

/// Re-record the canonical arena of an inner component from a claim's
/// public input values. The structure is mask-independent (no
/// data-dependent branching in `evaluate`), so the prover cannot present a
/// different circuit than the inner component's.
pub fn record_from_claim<E: stwo_constraint_framework::FrameworkEval>(
    eval: &E,
    claim: &CircuitClaim,
) -> (std::rc::Rc<core::cell::RefCell<Arena>>, usize) {
    use stwo_constraint_framework::InfoEvaluator;

    let info = eval.evaluate(InfoEvaluator::empty());
    let mut values = claim.inputs.iter().map(|(_, v)| *v);
    let alpha = values.next().expect("alpha input");
    let denom_inverse = values.next().expect("denom_inverse input");
    let mask: Vec<Vec<Vec<SecureField>>> = info
        .mask_offsets
        .iter()
        .map(|interaction| {
            interaction
                .iter()
                .map(|offsets| {
                    (0..offsets.len())
                        .map(|_| values.next().expect("mask input"))
                        .collect()
                })
                .collect()
        })
        .collect();
    assert!(values.next().is_none(), "extra input values in claim");

    let recorder = crate::recorder::Recorder::new(
        mask,
        alpha,
        denom_inverse,
        claim.inner_log_size,
        claim.inner_claimed_sum,
    );
    let recorder = eval.evaluate(recorder);
    let output = match &recorder.accumulation {
        crate::recorder::Rec::Node { id, .. } => *id,
        crate::recorder::Rec::Const(_) => panic!("composition accumulated to a constant"),
    };
    (recorder.arena, output)
}

pub(crate) fn limbs(value: SecureField) -> [u32; 4] {
    let array = value.to_m31_array();
    [array[0].0, array[1].0, array[2].0, array[3].0]
}

/// Use counts: how many times each node is consumed as an operand, plus one
/// for the output node (publicly consumed).
fn use_counts(arena: &Arena, output: usize) -> Vec<u32> {
    use_counts_for_outputs(arena, &[output])
}

/// Operand multiplicities plus one public consumption for every zero output.
pub(crate) fn use_counts_for_outputs(arena: &Arena, outputs: &[usize]) -> Vec<u32> {
    let mut uses = vec![0u32; arena.nodes.len()];
    for node in &arena.nodes {
        match node.op {
            Op::Add(a, b) | Op::Sub(a, b) | Op::Mul(a, b) => {
                uses[a] += 1;
                uses[b] += 1;
            }
            Op::Neg(a) | Op::Inverse(a) => uses[a] += 1,
            Op::Input | Op::Const => {}
        }
    }
    for output in outputs {
        uses[*output] += 1;
    }
    uses
}

/// Lower a recorded arena into witness rows, returning the public claim.
pub fn lower_arena(
    traces: &mut RecursionTraces,
    circuit_id: u32,
    arena: &Arena,
    output: usize,
    inner_log_size: u32,
    inner_claimed_sum: SecureField,
) -> CircuitClaim {
    lower_arena_operations(traces, circuit_id, arena, &[output]);
    let inputs = arena
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(id, node)| matches!(node.op, Op::Input).then_some((id as u32, node.value)))
        .collect();

    CircuitClaim {
        circuit_id,
        inputs,
        inner_log_size,
        inner_claimed_sum,
        output: (output as u32, arena.nodes[output].value),
    }
}

/// Lowers every arithmetic node for a circuit with one or more public outputs.
pub(crate) fn lower_arena_operations(
    traces: &mut RecursionTraces,
    circuit_id: u32,
    arena: &Arena,
    outputs: &[usize],
) {
    let uses = use_counts_for_outputs(arena, outputs);
    for (id, node) in arena.nodes.iter().enumerate() {
        let node_id = id as u32;
        let out = limbs(node.value);
        match node.op {
            Op::Input | Op::Const => {}
            Op::Mul(a, b) => {
                let av = limbs(arena.nodes[a].value);
                let bv = limbs(arena.nodes[b].value);
                traces.qm31_mul.push(
                    av[0], av[1], av[2], av[3], bv[0], bv[1], bv[2], bv[3], out[0], out[1], out[2],
                    out[3], circuit_id, node_id, a as u32, b as u32, uses[id], 1,
                );
            }
            Op::Inverse(a) => {
                let av = limbs(arena.nodes[a].value);
                traces.qm31_inv.push(
                    av[0], av[1], av[2], av[3], out[0], out[1], out[2], out[3], circuit_id,
                    node_id, a as u32, uses[id], 1,
                );
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                let av = limbs(arena.nodes[a].value);
                let bv = limbs(arena.nodes[b].value);
                let (is_add, is_sub) = if matches!(node.op, Op::Add(_, _)) {
                    (1, 0)
                } else {
                    (0, 1)
                };
                traces.linear_ops.push(
                    circuit_id, node_id, is_add, is_sub, 0, a as u32, b as u32, av[0], av[1],
                    av[2], av[3], bv[0], bv[1], bv[2], bv[3], out[0], out[1], out[2], out[3],
                    uses[id],
                );
            }
            Op::Neg(a) => {
                let av = limbs(arena.nodes[a].value);
                traces.linear_ops.push(
                    circuit_id, node_id, 0, 0, 1, a as u32, 0, av[0], av[1], av[2], av[3], 0, 0, 0,
                    0, out[0], out[1], out[2], out[3], uses[id],
                );
            }
        }
    }
}

/// The LogUp contribution of a circuit's public side, computed against the
/// canonical arena the verifier re-records from the claim's input values.
pub fn public_circuit_terms(
    claim: &CircuitClaim,
    arena: &Arena,
    output: usize,
    recursion_relations: &RecursionRelations,
) -> SecureField {
    use num_traits::Zero;

    let uses = use_counts(arena, output);
    let cid = M31::from(claim.circuit_id);
    let mut total = SecureField::zero();

    let wire_term = |node_id: u32, value: SecureField| -> SecureField {
        let value = limbs(value);
        let tuple = [
            cid,
            M31::from(node_id),
            M31::from(value[0]),
            M31::from(value[1]),
            M31::from(value[2]),
            M31::from(value[3]),
        ];
        let denom: SecureField = recursion_relations.wire.combine(&tuple);
        denom.inverse()
    };

    for (id, node) in arena.nodes.iter().enumerate() {
        let node_id = id as u32;
        match node.op {
            // Inputs and constants: emit their wire claims once per use.
            Op::Input | Op::Const => {
                if uses[id] > 0 {
                    total +=
                        wire_term(node_id, node.value) * SecureField::from(M31::from(uses[id]));
                }
            }
            // Arithmetic nodes: emit their structure once.
            op => {
                let (kind, lhs, rhs) = match op {
                    Op::Add(a, b) => (op_kind::ADD, a as u32, b as u32),
                    Op::Sub(a, b) => (op_kind::SUB, a as u32, b as u32),
                    Op::Mul(a, b) => (op_kind::MUL, a as u32, b as u32),
                    Op::Neg(a) => (op_kind::NEG, a as u32, 0),
                    Op::Inverse(a) => (op_kind::INVERSE, a as u32, 0),
                    Op::Input | Op::Const => unreachable!(),
                };
                let tuple = [
                    cid,
                    M31::from(node_id),
                    M31::from(kind),
                    M31::from(lhs),
                    M31::from(rhs),
                ];
                let denom: SecureField = recursion_relations.op_def.combine(&tuple);
                total += denom.inverse();
            }
        }
    }

    // The output is consumed publicly (its one extra use).
    total -= wire_term(claim.output.0, claim.output.1);
    total
}
