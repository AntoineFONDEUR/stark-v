# RV32IM AIR architecture

> **Status: current architecture.** This document describes how the active VM
> AIR is organized. Exact columns, constraints, lookup signs, and component
> order are generated from source and must not be duplicated here.

## Source of truth

The active definition is split across these source files:

- `crates/air/src/schema.rs` declares VM relations, preprocessed lookups, the
  remaining trace tables, and external felt-generated tables through
  `define_air!`.
- `crates/air/src/opcodes/{lui,auipc,jal,jalr}.rs` declare upper-immediate and
  jump execution, witness generation, constraints, and relations through
  `define_air_fns!`.
- `crates/air/src/poseidon2.rs` declares Poseidon2 through `define_air_fns!`.
- `crates/prover/src/components/mod.rs` fixes the VM constituent roster and
  routes generated opcode components into the VM proof and Poseidon2 into its
  detached proof.
- `crates/runner/src/ops/` holds decode adapters for migrated functions and
  executes the remaining opcode handlers.
- `crates/prover/src/public_data.rs` defines verifier-owned boundary terms.

When prose and generated source disagree, the generated source is authoritative.
Changes to a relation, table, or constraint must update tests rather than add a
second handwritten specification.

## Supported instruction set

The decoder and AIR support RV32I integer arithmetic, shifts, comparisons,
loads, stores, branches, jumps, upper immediates, and the RV32M multiplication,
division, and remainder instructions. `crates/air/src/instructions.rs` is the
canonical opcode list. Canonical `ecall` dispatches internal syscalls; COMMIT ID
1 has a proof-bound execution row and advances the ordered Poseidon2 journal.

The active execution-table families are:

- base register and immediate ALU;
- register and immediate shifts;
- register and immediate comparisons;
- equality and ordered branches;
- `lui`, `auipc`, `jal`, and `jalr`;
- loads and stores;
- low and high multiplication;
- division and remainder;
- proof-bound COMMIT selector, argument, Poseidon2, and journal transitions;
- program, memory, Merkle, and clock-update support tables in the VM
  constituent, plus the detached Poseidon2 support table.

## Shared relations

Execution tables connect through LogUp relations rather than direct table
ordering:

- `registers_state` chains `(pc, clock)` transitions;
- `memory_access` chains register-file and read-write-memory accesses;
- `program_access` binds executed instructions to committed program words;
- `merkle` binds committed leaves and roots;
- `poseidon2` and `poseidon2_io` bind permutation calls;
- `journal` chains COMMIT digests in authenticated execution-clock order;
- preprocessed range and bitwise relations constrain bounded values.

The verifier mixes public data before relation challenges are drawn. Component
claimed sums plus verifier-owned public terms must add to zero before the STWO
proof is accepted.

## Representation invariants

- Program counters and memory addresses live in M31. Converting a raw `u32`
  requires proving that its canonical value is below the M31 modulus.
- RV32 register and memory values remain four little-endian byte limbs so all
  `u32` bit patterns are representable.
- Register zero is immutable. Writes to `x0` are discarded by the execution
  semantics and constrained accordingly.
- Each memory or register access consumes its previous `(value, clock)` tuple
  and emits its next tuple. Clock gaps are range checked.
- Program memory is read-only and committed separately from read-write memory.
- Padding rows have one constrained inactive representation and contribute no
  unmatched relation entry.
- Poseidon2 calls bind the full input and output atomically through
  `poseidon2_io`; input and output halves cannot be independently permuted.

## Single-source requirement

AIR, witness generation, column layout, and interaction-trace registration must
come from the macro DSL. New components use `define_air!` or `define_air_fns!`.
Handwritten `FrameworkEval` components, standalone `define_component_tables!`
declarations, and wrapper macros that conceal either pattern are not accepted.

Every AIR currently reachable from the recursion roster is authored directly
through one of the two accepted macros, including the inner VM components. The
structural guard in `crates/recursion/tests/air_dsl_guard.rs` pins both
component rosters to their owning sources and rejects violations. Future
components must extend that inventory and satisfy the same rule before joining
either roster.

## Verification expectations

Each opcode family has a guest execution and constraint test in
`crates/prover/src/components/mod.rs`. A migrated family also requires a real
prove/verify test and focused mutation coverage in `crates/prover/tests` before
its old schema and handler semantics are removed. Green witness-generation tests
alone do not establish soundness.
