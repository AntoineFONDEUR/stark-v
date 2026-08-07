//! Store decode adapters for felt-generated load/store execution.

use super::load::execute_load_store;

use crate::trace::Tracer;
use crate::{Cpu, DecodedInst, Memory};

pub fn sb(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(
        cpu,
        memory,
        inst,
        tracer,
        inst.rs2,
        [0, 0, 0, 0, 0, 1, 0, 0],
    );
}

pub fn sh(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(
        cpu,
        memory,
        inst,
        tracer,
        inst.rs2,
        [0, 0, 0, 0, 0, 0, 1, 0],
    );
}

pub fn sw(cpu: &mut Cpu, memory: &mut Memory, inst: &DecodedInst, tracer: &mut Tracer) {
    execute_load_store(
        cpu,
        memory,
        inst,
        tracer,
        inst.rs2,
        [0, 0, 0, 0, 0, 0, 0, 1],
    );
}
