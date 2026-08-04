//! Arithmetic-circuit lowering into recursion AIR witness rows.
//!
//! Recorded arithmetic nodes become rows of `qm31_mul`, `qm31_inv`, and
//! `linear_ops`. Inputs, constants, and outputs are connected to those rows by
//! the typed relations owned by each verifier component.

use stwo::core::fields::qm31::SecureField;

use crate::recorder::{Arena, Op};
use crate::{LinearOpsTable, Qm31InvTable, Qm31MulTable};

/// Witness tables shared by every lowered arithmetic circuit.
#[derive(Default)]
pub struct CircuitTraces {
    pub qm31_mul: Qm31MulTable,
    pub qm31_inv: Qm31InvTable,
    pub linear_ops: LinearOpsTable,
}

pub(crate) fn limbs(value: SecureField) -> [u32; 4] {
    let array = value.to_m31_array();
    [array[0].0, array[1].0, array[2].0, array[3].0]
}

/// Operand multiplicities plus one public consumption for every output.
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

/// Lowers every arithmetic node for a circuit with one or more public outputs.
pub(crate) fn lower_arena_operations(
    traces: &mut CircuitTraces,
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
