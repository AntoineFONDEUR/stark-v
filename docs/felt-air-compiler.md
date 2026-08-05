# A felt language that compiles to AIR (design)

> **Status: partially implemented compiler roadmap.** `define_air_fns!`
> implements static control flow, functions, hints, degree-budget
> materialization, relation statements, and embedded components. Poseidon2 and
> every recursion-local AIR use it in production, while the other inner VM AIRs
> use `define_air!`. Opcode execution still has separate runner handlers;
> unifying executable semantics and AIR witness generation remains planned work.
> Macro source and tests are authoritative for implemented syntax.

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

`define_air!` provides the table-schema path used by the inner VM roster. It
generates the column layout, witness evaluation, constraints, lookups, and
component integration from one declaration.

`define_air_fns!` provides the felt-function path: degree-budget
materialization, static `for`/`map`/`sum`, inline functions and function I/O,
hints, external relation statements, embedded flag columns, and embedded
component integration. Poseidon2 and every recursion-local AIR use this path.

The remaining compiler work is witness-side VM access plus opcode execution and
runner migration. It is not a recursion-local macro migration. Every component
reachable from the recursion roster is already authored directly through
`define_air!` or `define_air_fns!`; the structural guard rejects a handwritten
`FrameworkEval`, standalone `define_component_tables!`, or wrapper macro in an
owner source.

## Migrating the opcode AIRs and runner

Target state: one function per opcode family, whose body **is** simultaneously
the executable semantics (the runner calls `call_lui` and gets the right
result), the witness fill (the call pushes the table row), and the AIR (the same
body compiled to constraints). `define_air!`'s
`committed/derived/constraints/lookups` schema, the `components!` composition
macro, and the hand-written opcode handlers in `runner/src/ops/` all collapse
into these function definitions.

What `define_air_fns!` is missing for opcodes, in dependency order:

1. **External relation statements.** ✅ _Implemented._ A system declares
   `relation name(arity);` at the top and function bodies use `emit name(args)`
   / `consume name(args)`; the entry is threaded through the same single-source
   `evaluation()` seam and the positional entry→relation mapping, drawn as an
   `AirFnRelations` field, and balanced across the proof. See the
   `extern_relation` tests in `crates/stwo-macros/tests/air_fns.rs` (a `source`
   function emits `pass(x)`, a `sink` consumes it, and the relation cancels).
   What remains is wiring the _specific_ zkVM relations (`program_access`,
   `memory_access`, `registers_state`, range checks) — i.e. an opcode body
   reads:

   The schema entry

   ```text
   lui: {
       committed: { clock, pc, rd, imm_0, imm_1, imm_2 },
       derived: {
           imm: imm_0 + pow2(4) * imm_1 + pow2(12) * imm_2,
           pc_next: pc + 4, clock_next: clock + 1,
           rd_val_1: imm_0 * pow2(4),
           rd_clock_diff: clock - rd_clock_prev,
       },
       lookups: {
           -enabler * program_access(pc, LUI, rd_addr, imm, 0),
           -enabler * registers_state(pc, clock),
           enabler * registers_state(pc_next, clock_next),
           -enabler * range_check_8_8_4(imm_1, imm_2, imm_0),
           -enabler * memory_access(0, rd_addr, rd_clock_prev, rd_prev_0, ...),
           enabler * memory_access(0, rd_addr, clock, 0, rd_val_1, imm_1, imm_2),
           -enabler * range_check_20(rd_clock_diff),
       },
   }
   ```

   becomes a function whose parameters are the access tuple and whose body reads
   naturally:

   ```text
   fn lui(clock, pc, rd: Reg, imm_0, imm_1, imm_2) {
       range_check_8_8_4(imm_1, imm_2, imm_0);
       let imm = imm_0 + 2**4 * imm_1 + 2**12 * imm_2;
       consume program_access(pc, LUI, rd.addr, imm, 0);
       rd.write(clock, [0, imm_0 * 2**4, imm_1, imm_2]);
       step registers_state(pc -> pc + 4, clock -> clock + 1);
   }
   ```

   `Reg` is sugar for the 10-column access bundle (`addr`, `prev_0..3`,
   `clock_prev`, …) plus the paired `memory_access` consume/emit and the
   `range_check_20` clock-diff check — the pattern every opcode repeats today.
   `step` is sugar for the `registers_state` consume/emit pair. Range checks are
   statements, not lookups the author signs.

2. **Witness-side access resolution.** `rd.write(...)` on the fill path must ask
   the VM for `prev`/`clock_prev` — i.e. call
   `Tracer::trace_reg_access`/`trace_mem_access` (gap-filling included). The
   generated `call_lui(vm, pc, imm…)` therefore takes the machine state, not raw
   felts: the function body is the _only_ place opcode semantics are written,
   and `runner/src/ops/upper.rs` (and friends) are deleted. The clock catch-up
   rows become activations of a generated `clock_gap` function, which retires
   the hand-written `air::clock::ClockGapTable` (its layout is pinned to the
   generated columns by `crates/air/tests/clock_layout.rs` until then. A
   push-by-`Access` API in `define_air!` would duplicate the witness-side access
   resolution this step is intended to provide.

3. **Witness hints.** ✅ _Implemented._ `hint name = expr;` declares a
   prover-chosen committed column, free in the AIR (the body constrains it with
   `assert`s) and filled by evaluating `expr` on the witness path — for the
   carry bits, sign decompositions, and `diff_inv` markers opcodes commit but do
   not derive in-row. See `test_hint_*` in
   `crates/stwo-macros/tests/air_fns.rs`.

4. **Dispatch.** Opcode families with flag columns (`base_alu_reg`'s
   add/sub/xor/or/and) are one function with a one-hot flag parameter and
   `if`-on-flag selects — already expressible with the static control flow. The
   decode step stays in the runner (`air::instructions`); it just calls the
   right generated function.

The capabilities (1) and (3) are in place, and the `mini_vm` test in
`crates/stwo-macros/tests/air_fns.rs` exercises the whole target shape on a toy:
opcodes as functions (`step`), the `(pc, clock)` state carried by an external
`reg_state` relation that telescopes across rows, a `boundary` function closing
the chain, and a `hint`-backed witness column — proven and verified, with a
broken chain rejected.

The **integration seam is also in place**. `define_air!` now takes an
`external:` section listing fn-DSL tables to fold into the `Tracer`:

```text
external: { poseidon2: crate::poseidon2 }   // air/src/schema.rs
```

Each entry generates the `Tracer` field, initialization, `total_traces`, debug,
and column re-export, so the monolithic `Tracer` is composable. Poseidon2 (a
fn-DSL component wired through
`components! { … poseidon2: air::poseidon2::component … }`) is the first entry,
and the full e2e suite (a real prove+verify per opcode) passes through the
generalized path. Migrating an opcode is now additive: define it via
`define_air_fns!`, add it to `external:`, point its `components!` entry at the
generated module, and remove it from the `trace:` block — one family per PR,
each guarded by the existing e2e proofs, until `runner/src/ops/` and the
schema's opcode list are empty. The remaining per-opcode work is the witness
fill calling the runner's `Tracer` (`trace_reg_access`/`trace_mem_access`) for
access values and the range checks resolving against the preprocessed tables.

### What this retires (the `components!` question)

`components!` is not redundant with `define_air!` — it generates the composition
layer (per-opcode `air`/`witness` modules, `Claim`, `Components`, trace
orchestration) that `define_air!` deliberately does not, because the composition
needs prover-side stwo types the air crate does not depend on. But
`define_air_fns!` with `embedded_component: true` already generates exactly that
composition for poseidon2. The retirement path is therefore not "merge
`components!` into `define_air!`" but:

1. migrate one simple opcode (`lui`) end to end — function in the air crate,
   generated component in the prover, handler deleted from the runner;
2. migrate the remaining families one PR each (the LogUp balance is checked by
   the existing e2e constraint tests at every step);
3. when the last family is out of `define_air!`'s opcode list, delete
   `components!` (~1000 lines), the `define_air!` opcode syntax, and
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
