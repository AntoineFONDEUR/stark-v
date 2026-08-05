//! Arithmetic-circuit lowering into recursion AIR witness rows.
//!
//! Recorded arithmetic nodes become rows of `qm31_mul`, `qm31_inv`, and
//! `linear_ops`. Inputs, constants, and outputs are connected to those rows by
//! the typed relations owned by each verifier component.

use stwo::core::ColumnVec;
use stwo::core::fields::m31::BaseField;
use stwo::core::fields::qm31::SecureField;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::BitReversedOrder;
use stwo::prover::poly::circle::CircleEvaluation;

use crate::linear_ops::LinearOpsPreprocessed;
use crate::qm31_inv::Qm31InvPreprocessed;
use crate::qm31_mul::Qm31MulPreprocessed;
use crate::recorder::{Arena, Op};
use crate::{LinearOpsTable, Qm31InvTable, Qm31MulTable};

/// One committed or preprocessed recursion component trace.
pub type CircuitAirTrace = ColumnVec<CircleEvaluation<SimdBackend, BaseField, BitReversedOrder>>;

/// Witness tables shared by every lowered arithmetic circuit.
#[derive(Default)]
pub struct CircuitTraces {
    pub qm31_mul: Qm31MulTable,
    pub qm31_inv: Qm31InvTable,
    pub linear_ops: LinearOpsTable,
    pub qm31_mul_schedule: Vec<Qm31MulScheduleRow>,
    pub qm31_inv_schedule: Vec<Qm31InvScheduleRow>,
    pub linear_ops_schedule: Vec<LinearOpsScheduleRow>,
}

/// Lowered arithmetic witnesses paired with their verifier-owned schedules.
pub struct CircuitAirTraces {
    pub qm31_mul: CircuitAirTrace,
    pub qm31_mul_preprocessed: CircuitAirTrace,
    pub qm31_inv: CircuitAirTrace,
    pub qm31_inv_preprocessed: CircuitAirTrace,
    pub linear_ops: CircuitAirTrace,
    pub linear_ops_preprocessed: CircuitAirTrace,
}

impl CircuitTraces {
    /// Materialize committed traces and the matching fixed operation schedules.
    pub fn into_air_traces(self) -> Result<CircuitAirTraces, &'static str> {
        let Self {
            qm31_mul,
            qm31_inv,
            linear_ops,
            qm31_mul_schedule,
            qm31_inv_schedule,
            linear_ops_schedule,
        } = self;

        let qm31_mul = qm31_mul.into_witness();
        let qm31_inv = qm31_inv.into_witness();
        let linear_ops = linear_ops.into_witness();
        let qm31_mul_log_size = qm31_mul
            .first()
            .ok_or("multiplication trace has no committed columns")?
            .domain
            .log_size();
        let qm31_inv_log_size = qm31_inv
            .first()
            .ok_or("inversion trace has no committed columns")?
            .domain
            .log_size();
        let linear_ops_log_size = linear_ops
            .first()
            .ok_or("linear-operation trace has no committed columns")?
            .domain
            .log_size();

        Ok(CircuitAirTraces {
            qm31_mul,
            qm31_mul_preprocessed: Qm31MulPreprocessed::new(qm31_mul_log_size, qm31_mul_schedule)?
                .gen_columns(),
            qm31_inv,
            qm31_inv_preprocessed: Qm31InvPreprocessed::new(qm31_inv_log_size, qm31_inv_schedule)?
                .gen_columns(),
            linear_ops,
            linear_ops_preprocessed: LinearOpsPreprocessed::new(
                linear_ops_log_size,
                linear_ops_schedule,
            )?
            .gen_columns(),
        })
    }
}

/// Verifier-owned graph coordinates for one lowered multiplication node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Qm31MulScheduleRow {
    pub circuit_id: u32,
    pub node_id: u32,
    pub lhs_id: u32,
    pub rhs_id: u32,
    pub uses: u32,
}

/// Verifier-owned graph coordinates for one lowered inversion node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Qm31InvScheduleRow {
    pub circuit_id: u32,
    pub node_id: u32,
    pub lhs_id: u32,
    pub uses: u32,
}

/// Verifier-owned graph coordinates for one lowered linear node.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LinearOpsScheduleRow {
    pub circuit_id: u32,
    pub node_id: u32,
    pub is_add: u32,
    pub is_sub: u32,
    pub is_neg: u32,
    pub lhs_id: u32,
    pub rhs_id: u32,
    pub uses: u32,
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
                traces.qm31_mul_schedule.push(Qm31MulScheduleRow {
                    circuit_id,
                    node_id,
                    lhs_id: a as u32,
                    rhs_id: b as u32,
                    uses: uses[id],
                });
            }
            Op::Inverse(a) => {
                let av = limbs(arena.nodes[a].value);
                traces.qm31_inv.push(
                    av[0], av[1], av[2], av[3], out[0], out[1], out[2], out[3], circuit_id,
                    node_id, a as u32, uses[id], 1,
                );
                traces.qm31_inv_schedule.push(Qm31InvScheduleRow {
                    circuit_id,
                    node_id,
                    lhs_id: a as u32,
                    uses: uses[id],
                });
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
                traces.linear_ops_schedule.push(LinearOpsScheduleRow {
                    circuit_id,
                    node_id,
                    is_add,
                    is_sub,
                    is_neg: 0,
                    lhs_id: a as u32,
                    rhs_id: b as u32,
                    uses: uses[id],
                });
            }
            Op::Neg(a) => {
                let av = limbs(arena.nodes[a].value);
                traces.linear_ops.push(
                    circuit_id, node_id, 0, 0, 1, a as u32, 0, av[0], av[1], av[2], av[3], 0, 0, 0,
                    0, out[0], out[1], out[2], out[3], uses[id],
                );
                traces.linear_ops_schedule.push(LinearOpsScheduleRow {
                    circuit_id,
                    node_id,
                    is_add: 0,
                    is_sub: 0,
                    is_neg: 1,
                    lhs_id: a as u32,
                    rhs_id: 0,
                    uses: uses[id],
                });
            }
        }
    }
}
