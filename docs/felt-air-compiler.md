# A felt language that compiles to AIR (design)

> **Status: partially implemented compiler roadmap.** `define_air_fns!`
> implements static control flow, functions, hints, degree-budget
> materialization, relation statements, embedded components, and proof-bound VM
> register/aligned-memory access. Poseidon2 and every recursion-local AIR use it
> in production. Upper-immediate, jump, base ALU, comparison, and branch
> families have one felt-function source for execution, witness filling, and
> AIR; the remaining shift, memory, and RV32M opcode AIRs still use
> `define_air!` with separate runner handlers. Macro source and tests are
> authoritative for implemented syntax.

## The observation

Write-once (single-assignment) memory with Cairo-style call frames is already a
circuit description. Each frame only references values in the window
`[fp - arg_size, fp + frame_size)`; every cell is written exactly once as a felt
expression of earlier cells. That is precisely a row of an AIR table: the
frame's cells are the columns, the write expressions are the wires, and a
"function" is a reusable sub-circuit. The Cairo VM's memory model is not an
execution detail — it is the reason Cairo programs _define_ AIRs instead of
merely running on one.

So instead of writing components as flattened column lists plus hand-named
intermediates, we should write them as straight-line felt code and compile to
the AIR, with the **maximum constraint degree as a compiler parameter**.

## What the compiler does

The program is felt-valued single-assignment code over the table's input
columns. The compiler builds the expression DAG and decides, per node, whether
it stays **inline** (a derived expression, free) or is **materialized** (a
committed trace column plus one equality constraint):

- Multiplication compounds degree: `x * y * z` at `max_degree = 2` splits into
  `t = x * y` (materialized, constraint `t - x * y`) and the inline `t * z`.
- Addition does not: `a + b + c + d` stays one inline expression no matter its
  length — it never increases the degree.
- Common subexpressions that must be materialized are deduplicated. The compiler
  does not yet decide to materialize an otherwise valid expression based on
  prover cost; that cost model remains future work.

The generated backend contains a column list (inputs plus materialized
intermediates), inline derived expressions, materialization equalities and
program assertions, and LogUp entries for relation calls.

The same lowered program generates the AIR evaluation and the concrete
`BaseField` witness calls, so materialized cells and their constraints stay in
the same order.

## Poseidon2, the implemented reference

Poseidon2 is the production reference for the felt-function path. Its
permutation is written with static loops and helper functions in
`crates/air/src/poseidon2.rs`, and `define_air_fns!` generates its materialized
columns, constraints, witness calls, and embedded prover component. Its source
has this shape:

```text
fn poseidon2(state: [felt; 16]) -> [felt; 16] {
    state = external_matrix(state);
    for round in 0..4 {                       // static bound: unrolled
        state = add_round_constants(state, EXTERNAL[round]);
        for i in 0..16 { state[i] = sbox(state[i]); }   // x^5
        state = external_matrix(state);       // additive: stays inline
    }
    for round in 0..14 { state = partial_round(state, round); }
    for round in 4..8 { state = full_round(state, round); }
    state
}

fn sbox(x: felt) -> felt {
    x ** 5
}
```

At `max_degree = 3` the compiler materializes the cells needed to stay within
the constraint bound and derives the column layout, constraints, and witness
fill together. The flattened table is generated output, not source. Every
recursion-reachable AIR has the same single-source property, enforced by
`crates/recursion/tests/air_dsl_guard.rs`.

## Control flow: the calling convention is a LogUp relation

The Cairo frame layout completes the model. A call frame receives its inputs at
`[fp - n, fp - 3)` and leaves its outputs at the final `[ap - m, ap - 1)`; the
two remaining slots — `fp - 2` (saved fp) and `fp - 1` (return pc) — are pure
control-flow plumbing. In the AIR view those two slots disappear entirely: LogUp
replaces sequencing. What remains per activation is exactly one natural tuple,
`(inputs..., outputs...)`, and that tuple **is** the function's relation.

- Each function is an AIR table; each activation (call) is one row.
- A row starts by **consuming** its own activation tuple
  (`-enabler * fn_io(args..., rets...)`) and its constraints enforce
  `rets = body(args)`.
- A caller **emits** the tuple for every call it makes
  (`+enabler * callee_io(call_args..., call_rets...)`) — the returned values are
  witness columns in the caller's frame, received through the relation, and the
  callee's constraints are what make them right.
- A recursive call is the same emission against the function's own relation:
  rows of one AIR consuming and emitting each other, telescoping exactly like
  the recursion crate's `merkle_node` paths and transcript state relations.
- The program's public interface is the entry activations: the verifier emits
  `+fn_io(inputs, outputs)` as public claim terms (the `RootClaim` pattern), and
  the whole multiset must cancel.

Purity makes the unkeyed tuple sound: a function is a relation in the
mathematical sense, so two activations with the same inputs have the same
outputs and collapse into multiplicity — no call-site nonce needed.

The codebase already runs on this pattern without naming it: the opcode tables
are "functions" consuming `program_access` and `memory_access` tuples;
`poseidon2_io(in16, out16)` is precisely an activation tuple; the recursion
circuit's `wire` relation connects QM31 values across verifier-scheduled
arithmetic rows. The language makes the pattern first-class: `let c = cube(a)`
in source compiles to a column `c`, an emission into `cube`'s relation, and a
row in `cube`'s table — wiring, table layout, and witness fill all from one
line.

## Relation to the current DSL

`define_air!` provides the table-schema path used by most of the inner VM
roster. It generates the column layout, witness evaluation, constraints,
lookups, and component integration from one declaration.

`define_air_fns!` provides the felt-function path: degree-budget
materialization, static `for`/`map`/`sum`, inline functions and function I/O,
hints, external relation statements, canonical M31 splitting, byte-level lookup
operations, wrapping word arithmetic, embedded flag columns, and embedded
component integration. Poseidon2, the ten migrated VM opcode families, and every
recursion-local AIR use this path.

The remaining compiler work is opcode execution and runner migration. It is not
a recursion-local macro migration. Every component reachable from the recursion
roster is already authored directly through `define_air!` or `define_air_fns!`;
the structural guard rejects a handwritten `FrameworkEval`, standalone
`define_component_tables!`, or wrapper macro in an owner source.

## Migrating the opcode AIRs and runner

Target state: one function per opcode family, whose body **is** simultaneously
the executable semantics (the runner calls the generated fill and gets the right
result), the witness fill (the call pushes the table row), and the AIR (the same
body compiled to constraints). `define_air!`'s
`committed/derived/constraints/lookups` schema, the `components!` composition
macro, and the hand-written opcode handlers in `runner/src/ops/` all collapse
into these function definitions.

Opcode compiler capabilities, in dependency order:

1. **External relation statements.** ✅ _Implemented._ A system declares
   `relation name(arity);` at the top and function bodies use `emit name(args)`
   / `consume name(args)`; the entry is threaded through the same single-source
   `evaluation()` seam and the positional entry→relation mapping, drawn as an
   `AirFnRelations` field, and balanced across the proof. See the
   `extern_relation` tests in `crates/stwo-macros/tests/air_fns.rs` (a `source`
   function emits `pass(x)`, a `sink` consumes it, and the relation cancels).
   LUI now wires the zkVM relations directly from its production felt function:

   ```text
   fn lui(clock, pc, rd_addr, imm_0, imm_1, imm_2) {
       let imm = imm_0 + 16 * imm_1 + 4096 * imm_2;
       consume program_access(
           pc, constant(crate::instructions::Opcode::Lui as u32), rd_addr, imm, 0
       );
       consume registers_state(pc, clock);
       emit registers_state(pc + 4, clock + 1);
       consume range_check_8_8_4(imm_1, imm_2, imm_0);
       write_reg rd(clock, rd_addr, [0, 16 * imm_0, imm_1, imm_2]);
       return pc + 4;
   }
   ```

   `write_reg rd(...)` generates the `rd_addr`, `rd_prev`, `rd_clock_prev`, and
   `rd_next` bindings, the paired `memory_access` consume/emit entries, the
   `range_check_20` clock-diff entry, and x0-safe write constraints. `read_reg`
   additionally proves that a read cannot mutate the value. `read_mem` and
   `write_mem` provide the same behavior for aligned words in address space 1.
   Byte and half-word opcodes select and replace lanes in felt code before the
   aligned-word write. State transitions and opcode-specific range checks stay
   explicit relation statements.

2. **Witness-side access resolution.** ✅ _Implemented._ A `vm_access` block
   supplies the architectural-state trait and tracer paths. Generated calls read
   or update that state, invoke `Tracer::trace_reg_access` or
   `Tracer::trace_mem_access`, bind the returned access cells, and push the same
   function row into the configured tracer table in embedded mode. The tracer
   performs gap filling and preserves `mem_initial`; the `clock_gap:` section of
   `define_air!` generates the corresponding AIR component. `ClockGapTable` is
   its columnar witness container, not a separately authored AIR component.
   Adding a push-by-`Access` API to `define_air!` would duplicate this
   resolution path and is intentionally not part of the design.

3. **Witness hints.** ✅ _Implemented._ `hint name = expr;` declares a
   prover-chosen committed column, free in the AIR (the body constrains it with
   `assert`s) and filled by evaluating `expr` on the witness path — for the
   carry bits, sign decompositions, and `diff_inv` markers opcodes commit but do
   not derive in-row. See `test_hint_*` in
   `crates/stwo-macros/tests/air_fns.rs`.

4. **Word intrinsics.** ✅ _Implemented._ `split_m31(value)` commits the
   canonical four-byte representation, constrains its recomposition, and
   consumes `range_check_8_8` plus `range_check_m31`. `bitand`, `bitor`, and
   `bitxor` commit one byte output and consume the corresponding preprocessed
   `bitwise` row, optionally under an opcode multiplicity. `add_u32` and
   `sub_u32` commit four wrapping result limbs plus the carry/borrow chain,
   constrain every chain bit, and range-check an active result. AUIPC and JAL
   use the split for their written word; JALR splits its canonical target and
   binds the cleared low bit through `bitand`; the base ALU families compose the
   arithmetic and bitwise primitives under one-hot opcode flags. Comparisons use
   the terminal borrow from `sub_u32`; signed comparisons authenticate the
   standard sign-bit ordering transform through `bitxor`. Equality branches
   prove equality by checking that neither directional subtraction borrows.

5. **Dispatch.** Opcode families with flag columns (`base_alu_reg`'s
   add/sub/xor/or/and) are one function with one-hot felt parameters. Arithmetic
   selectors and relation multiplicities gate each variant; there is no dynamic
   branch in the AIR language. The decode step stays in the runner
   (`air::instructions`) and calls the generated family function with the
   selected flag tuple.

The capabilities (1) through (5) are in place. Tests in
`crates/stwo-macros/tests/air_fns.rs` prove generated register and memory
accesses through external relation boundaries, reject stale clocks, incorrect
prior values, read-side writes, and non-zero x0 writes, and exercise gap filling
with the real tracer. The `mini_vm` tests separately cover function activation,
state-relation telescoping, and hint-backed witness columns.

The **integration seam is also in place**. `define_air!` now takes an
`external:` section listing fn-DSL tables to fold into the `Tracer`:

```text
external: {
    auipc: crate::opcodes::auipc,
    base_alu_imm: crate::opcodes::base_alu_imm,
    base_alu_reg: crate::opcodes::base_alu_reg,
    branch_eq: crate::opcodes::branch_eq,
    branch_lt: crate::opcodes::branch_lt,
    jal: crate::opcodes::jal,
    jalr: crate::opcodes::jalr,
    lt_imm: crate::opcodes::lt_imm,
    lt_reg: crate::opcodes::lt_reg,
    poseidon2: crate::poseidon2,
    lui: crate::opcodes::lui,
}
```

Each entry generates the `Tracer` field, initialization, `total_traces`, debug,
and column re-export, so the monolithic `Tracer` is composable. The component
router assigns Poseidon2 to the detached hash proof and all ten generated opcode
tables to the VM proof. Migrating another opcode means defining it via
`define_air_fns!`, adding it to `external:`, routing its generated component,
and removing its schema and runner semantics after focused valid and malformed
tests pass.

### What this retires (the `components!` question)

`components!` is not redundant with `define_air!` — it generates the composition
layer (per-opcode `air`/`witness` modules, `Claim`, `Components`, trace
orchestration) that `define_air!` deliberately does not, because the composition
needs prover-side stwo types the air crate does not depend on. But
`define_air_fns!` with `embedded_component: true` already generates exactly that
composition for poseidon2. The retirement path is therefore not "merge
`components!` into `define_air!`" but:

1. `[done]` Migrate `lui`, `auipc`, `jal`, `jalr`, both base ALUs, both
   comparisons, and both branch families end to end: the air crate owns their
   felt functions, the prover uses their generated components, and the runner
   retains only decoding;
2. `[pending]` Migrate the remaining families in dependency order; the LogUp
   balance is checked by the existing component tests at every step;
3. `[pending]` When the last family is out of `define_air!`'s opcode list,
   delete `components!` (~1000 lines), the `define_air!` opcode syntax, and
   `runner/src/ops/`.

Until then `components!` stays; any interim investment in it (or in new
`define_air!` surface) should be weighed against this plan.

## Open questions

- **Materialization vs masks**: stwo also allows referencing neighboring rows
  (masks). A frame that reads its caller's cells maps naturally to a mask
  offset; deciding when a value crosses rows vs stays in-row is a layout
  question the compiler eventually owns.
- **Lookup placement**: relation calls inside loops/functions multiply entries;
  the batching parameter (`batch:`) should become a per-entry degree decision
  the compiler makes (quadratic denominators → singleton), not a table-level
  annotation.
- **Cost model**: columns are committed (Merkle + FRI cost per column); inline
  expressions cost composition-evaluation work. The right objective is prover
  time, with max_degree as the hard constraint.
