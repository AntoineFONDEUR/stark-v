# A felt language that compiles to AIR

> **Status: current compiler architecture.** `define_air_fns!` implements static
> control flow, functions, hints, degree-budget materialization, relation
> statements, embedded components, proof-bound VM access, and word intrinsics.
> Every ordinary RV32IM opcode family and Poseidon2 use it for execution,
> witness filling, and AIR generation. `define_air!` owns the common schema,
> lookup tables, COMMIT, and support tables. Macro source and tests are
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

`define_air!` provides the table-schema path for common relations, preprocessed
lookups, COMMIT, and VM support tables. It generates column layouts, witness
evaluation, constraints, lookups, and component integration from one
declaration.

`define_air_fns!` provides the felt-function path: degree-budget
materialization, static `for`/`map`/`sum`, inline functions and function I/O,
hints, external relation statements, canonical M31 splitting, byte-level lookup
operations, wrapping and selected word arithmetic, embedded flag columns, and
embedded component integration. Poseidon2 and every ordinary RV32IM opcode
family use this path.

Opcode and runner migration is complete. Every component reachable from either
proof roster is authored directly through `define_air!` or `define_air_fns!`;
the structural guard rejects a handwritten `FrameworkEval`, standalone
`define_component_tables!`, or wrapper macro in an owner source. Remaining
compiler work concerns reusable language features and measured cost, not a
second component-authoring path.

## Opcode AIR and runner path

Each ordinary opcode family has one function whose body **is** simultaneously
the executable semantics, witness fill, and AIR. The runner decodes an
instruction, supplies the selected family flags, and calls the generated fill;
it does not duplicate opcode arithmetic or memory semantics.

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
   `read_word name(clock, address_space, address)` and
   `write_word name(clock, address_space, address, limbs)` select register
   address space 0 or aligned-memory address space 1 in the felt function; the
   compiler constrains the selector to be boolean and preserves x0 semantics for
   dynamic register writes. Byte and half-word opcodes select and replace lanes
   in felt code before the aligned-word write. State transitions and
   opcode-specific range checks stay explicit relation statements.

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
   constrain every chain bit, and range-check an active result.
   `binary_u32(lhs, rhs, active, add, sub, and, or, xor)` instead commits one
   range-bound result word, constrains each selector boolean and their sum to
   `active`, derives the arithmetic carry/borrow chains, and uses one
   multiplicity-gated bitwise relation per limb with the selected operation ID.
   The base ALU families use this shared-output form. `divrem_u32` commits RV32
   signed or unsigned quotient, remainder, zero, overflow, and inverse
   witnesses; it adds no implicit soundness rule, so the felt body binds those
   columns through the wide product identity, absolute-remainder bound,
   special-case constraints, and explicit range relations. AUIPC and JAL use the
   split for their written word; JALR splits its canonical target and binds the
   cleared low bit through `bitand`. Comparisons use the terminal borrow from
   `sub_u32`; signed comparisons authenticate the standard sign-bit ordering
   transform through `bitxor`. Equality branches prove equality by checking that
   neither directional subtraction borrows.

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

The integration seam is also complete. `define_air!`'s `external:` section lists
every fn-DSL table folded into the `Tracer`; the list in
`crates/air/src/schema.rs` is authoritative. Each entry generates its tracer
field, initialization, row count, debug support, and column re-export. The
component router assigns Poseidon2 to the detached hash proof and every opcode
table to the VM proof.

### The `components!` boundary

`components!` is not an alternate AIR-authoring surface. It assembles generated
components into proof rosters and derives `Claim`, `Components`, and trace
orchestration using prover-side STWO types that the AIR crate does not depend
on. Opcode-specific `define_air!` tables and handwritten runner semantics are
gone. `runner/src/ops/` remains as the decode-to-generated-fill adapter layer;
deleting it would require moving instruction dispatch, not removing duplicate
AIR semantics.

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
