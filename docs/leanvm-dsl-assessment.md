# Can the stark-v AIR DSL express a LeanVM prover?

<!-- cspell:ignore leanvm xmss multilinear domainsep sumcheck -->

> Assessment of `define_air!` / `define_air_fns!` (crates/stwo-macros) against
> the LeanVM design at a sibling `leanVM` checkout. Read-only study: no source
> was modified and no build was run.

## Summary of the verdict

The DSL expresses LeanVM's _shape_ — a Cairo-style three-operand execution
table, bus-connected precompiles, a bytecode lookup, a multiplicity-addressed
memory table — in roughly six to ten files. It cannot express LeanVM's
_semantics_, because LeanVM is arithmetic over KoalaBear and the DSL is welded
to M31. Everything below is the detail behind that split.

## LeanVM overview

**Proving stack.** Multilinear WHIR + SuperSpartan + GKR-LogUp (`README.md`),
i.e. sumcheck over multilinear polynomials. Nothing about the commitment scheme
is shared with stwo's Circle-STARK/FRI stack.

**Field.** `crates/lean_vm/src/core/types.rs`:

```rust
pub type F = KoalaBear;                  // p = 2^31 - 2^24 + 1
pub type EF = QuinticExtensionFieldKB;   // DIMENSION = 5
```

**Machine state.** Cairo-derived and register-free: a program counter `pc`, a
frame pointer `fp`, and one flat write-once memory of field elements
(`crates/lean_vm/src/execution/memory.rs` — `Memory(ArenaVec<Option<F>>)`; `set`
on an already-written cell is `MemoryAlreadySet`). No timestamps, no clock, no
address spaces, no register file, no byte decomposition. A "word" is one
KoalaBear element.

**ISA.** Four instructions (`crates/lean_vm/src/isa/instruction.rs`):

| Instruction   | Semantics                                                                                                                                                        |
| ------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Computation` | `res = arg_a ⊕ arg_c` with `⊕ ∈ {+, ×}` in KoalaBear; any one of the three slots may be the unknown, so it doubles as SUB and DIV (`Operation::inverse_compute`) |
| `Deref`       | `res = m[m[fp + shift_0] + shift_1]`, or the symmetric store                                                                                                     |
| `Jump`        | `if cond != 0 { pc, fp = dest, updated_fp } else { pc += 1 }`; `cond` constrained boolean                                                                        |
| `Precompile`  | dispatch to `Poseidon16` or `ExtensionOp` with three operands                                                                                                    |

Operands are `MemOrConstant` / `MemOrFpOrConstant`
(`crates/lean_vm/src/isa/operands/`): immediate, `m[fp + off]`, or `fp + off`,
selected by decoded flag columns.

**Tables.** Exactly three (`crates/lean_vm/src/tables/table_enum.rs`):

| Table          | Columns                   | AIR degree                                        | Constraints     |
| -------------- | ------------------------- | ------------------------------------------------- | --------------- |
| `execution`    | 20 + 4 virtual            | 5                                                 | 14              |
| `extension_op` | 29 + 2 virtual            | 6                                                 | 35              |
| `poseidon16`   | Poseidon1-width-16 layout | 10 (with a degree-3 "low" part per partial round) | ~10 + 4·16 + 20 |

Sources: `tables/execution/air.rs`, `tables/extension_op/air.rs`,
`tables/poseidon/mod.rs:245`.

**Cross-table plumbing.** A `BusInteraction` system
(`crates/lean_vm/src/tables/table_trait.rs`): each bus has a direction
(push/pull), a multiplicity (constant `One` or a column), a domain separator,
and a data tuple of columns/columns-plus-constant/constants. Three buses in
practice: memory (`LOGUP_MEMORY_DOMAINSEP`), bytecode
(`LOGUP_BYTECODE_DOMAINSEP`), and precompile dispatch keyed by a runtime
`domainsep` column. Memory consistency is _not_ a permutation over timestamped
accesses: the memory vector itself is committed (`prove_execution.rs` commits
`memory` alongside a `memory_acc` access-count vector) and every access is a
lookup into it. Write-once semantics make that sound without clocks.

**Bytecode.** Committed as a multilinear (`isa/bytecode.rs`), hashed into the
Fiat-Shamir domain separator; the execution table pushes all 12 decoded
instruction columns plus `pc` onto the bytecode bus.

**Non-determinism.** A rich hint layer (`isa/hint.rs`): `Inverse`,
`RequestMemory`, `DerefHint` (deferred constraint resolution),
`ParallelBatchStart`, `HintWitness`. Hints are runner-side only and never appear
in verified bytecode.

**Cross-row structure.** `n_shift_columns()` is non-zero for `execution` (2:
`pc`, `fp`) and `extension_op` (13, including the 5-limb running accumulator).
LeanVM's AIR builder exposes `builder.shift()` — genuine next-row masks.

**Unusual bits worth flagging.** Degree-5 extension arithmetic as a first-class
precompile with a variable `len` chunked across consecutive rows;
`low_degree_air` as a per-AIR optimization hook; padding rows that are a real
self-jump at `ending_pc` rather than an inert zero row
(`tables/execution/mod.rs::padding_row`).

## stark-v DSL capability inventory

What `define_air!` provides (`crates/stwo-macros/src/define_air.rs`,
`trace_tables.rs`; used by `crates/air/src/schema.rs`):

- `relations:` — named LogUp relations of arbitrary declared arity.
- `preprocessed:` — declared constant lookup tables (`bitwise`,
  `range_check_*`), with generated multiplicity components.
- `trace:` — tables with `committed:` columns, `derived:` expressions
  (single-source across AIR and witness), `constraints:`, and `lookups:` whose
  numerator is an arbitrary in-row expression
  (`multiplicity * program_access(..)`, `-cur_mult * merkle(..)` in
  `schema.rs`).
- `clock_gap:` — generates the clock-gap component bound to a range relation.
- `external:` — folds `define_air_fns!` tables into the `Tracer`.

What `define_air_fns!` provides (`crates/stwo-macros/src/air_fns.rs`, header
docs lines 1–140):

- Single-assignment felt code; degree-budget materialization (`max_degree`
  **must be 2 or 3** — hard check at `air_fns.rs:225`).
- Static `for` with constant bounds, fixed-size arrays, `map`/`sum`/`update`,
  `inline fn` splicing, function-call activations as LogUp relations.
- `assert` (enabler-gated) and `constrain` (ungated) statements.
- `hint name = expr;` — prover-chosen committed column, unconstrained in the
  AIR.
- `relation r(arity);` with `emit`/`consume`, optionally with an explicit
  multiplicity expression `emit(expr) r(..)`.
- `embedded:` flag columns, `embedded_component:`, `embedded_preprocessed:`
  (trusted preprocessed columns replacing committed ones), `embedded_params:`
  (per-proof field constants, not columns), `embedded_relations:` (share one
  relation bundle across systems), `logup_batch: 1|2` with
  `logup_unbatched_tail`.
- `vm_access: { state, tracer }` plus `read_reg`/`write_reg`/`read_mem`/
  `write_mem`/`read_word`/`write_word` — witness-side architectural-state
  resolution with generated `memory_access` consume/emit pairs and
  `range_check_20` clock gaps.
- Word intrinsics: `split_m31`, `bitand`/`bitor`/`bitxor`, `add_u32`/`sub_u32`,
  `binary_u32`, `divrem_u32`.

What the DSL does **not** provide:

- **Any field other than M31.** `trace_tables.rs:609` hard-codes
  `M31_PRIME = (1 << 31) - 1`; constant folding, `inv(c)`, and every literal
  lower through `BaseField::from_u32_unchecked` (`trace_tables.rs:601`); witness
  generation is `PackedM31`/`PackedQM31`; codegen names `stwo::…` paths
  throughout. There is no field parameter anywhere in the macro crate.
- **Cross-row masks.** The only mask API emitted is `eval.next_trace_mask()`
  (`trace_tables.rs:1384`, `air_fns.rs:3627/3649`), which advances to the next
  _column_ at row offset 0. Row-shifted access is listed as unimplemented in
  `docs/felt-air-compiler.md` under "Open questions — Materialization vs masks".
  Row-to-row chaining is done with LogUp state relations instead
  (`registers_state(pc, clock)`).
- **Constraint degree above 3.**
- **Dynamic control flow.** No data-dependent branches or loop bounds; dispatch
  is one-hot flag columns (`docs/felt-air-compiler.md`, capability 5).

The DSL is proven at scale: 21 trace components + 1 detached + 6 lookup
components in `crates/prover/src/components/mod.rs`, 36 universal recursion
components pinned in `crates/recursion/tests/air_dsl_guard.rs`, zero handwritten
`FrameworkEval`.

## Requirement mapping

| LeanVM element                                                                | DSL coverage                  | Notes                                                                                                                                                                                                                                                                         |
| ----------------------------------------------------------------------------- | ----------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| KoalaBear base field                                                          | **Missing, structural**       | Macro crate is M31-only; see gap G1                                                                                                                                                                                                                                           |
| Quintic extension arithmetic (`extension_op`)                                 | **Missing, follows G1**       | An M31 build would use QM31, a _degree-4_ extension — LeanVM's `DIMENSION = 5` layout, the 5-limb accumulator, and every EF-typed memory layout change shape                                                                                                                  |
| Poseidon16 over KoalaBear                                                     | **Missing, follows G1**       | `crates/air/src/poseidon2.rs` is Poseidon2-over-M31; LeanVM uses Poseidon1-width-16-over-KoalaBear                                                                                                                                                                            |
| Fetch/decode (bytecode bus, 12 decoded columns + pc)                          | Covered                       | `define_air!` `trace:` table with `multiplicity * bytecode(...)`, exactly the `program` table pattern in `schema.rs`                                                                                                                                                          |
| `Computation` (ADD/MUL, any-slot-unknown)                                     | Covered structurally          | One `define_air_fns!` function with `opcode_add_flag`/`opcode_mul_flag`; the "unknown slot" resolution is runner-side, the AIR only checks `nu_b = nu_a + nu_c` / `nu_a · nu_c`                                                                                               |
| Operand selection (`flag_a/b/c`, `flag_ab_fp`, `flag_c_fp`)                   | Covered                       | In-row flag columns and `constrain` statements; the `nu_*` expressions are degree-2 derived cells                                                                                                                                                                             |
| `Deref`                                                                       | Covered                       | Address arithmetic plus one memory-bus emit                                                                                                                                                                                                                                   |
| `Jump` (pc/fp transition)                                                     | Covered, redesign needed      | LeanVM uses `shift[pc]`/`shift[fp]`; the DSL requires a `state(pc, fp)` consume/emit relation chain — this is the established stark-v idiom (`registers_state`), not a gap, but it is a rewrite of the transition constraints and adds two LogUp entries per row              |
| Write-once flat memory                                                        | Covered                       | `emit/consume memory(addr, value)` plus a `memory` table carrying one row per cell with a multiplicity column; `schema.rs`'s `memory` table already has this shape (minus the clock/limb/Merkle machinery)                                                                    |
| `vm_access` intrinsics                                                        | **Not applicable**            | Hard-wired to RV32: four byte limbs, address spaces 0/1, `x0` semantics, `clock_prev` + `range_check_20` gaps (`air_fns.rs:2086–2330`). LeanVM has none of these. Memory buses must be written as plain `emit`/`consume` statements — fully supported, just no intrinsic help |
| Word intrinsics (`split_m31`, `add_u32`, `binary_u32`, `divrem_u32`, bitwise) | **Not applicable**            | All assume u32-over-bytes RV32 values. LeanVM is field-native, so this entire specialized surface is dead weight for it                                                                                                                                                       |
| Range checks (LeanVM's 3-cycle `assert a < b`)                                | Covered                       | `preprocessed:` declaration plus `consume range_check_n(...)`                                                                                                                                                                                                                 |
| Hints (`Inverse`, `RequestMemory`, `DerefHint`)                               | Covered                       | `hint name = expr;` is exactly this; deferred resolution stays runner-side                                                                                                                                                                                                    |
| Variable-`len` extension op chunked across rows                               | Partially covered             | Needs a per-chunk accumulator relation chain instead of `shift[COL_ACC]`; expressible, costs LogUp columns                                                                                                                                                                    |
| Precompile dispatch bus with runtime `domainsep`                              | Covered                       | Relation tuple with a computed first argument; `emit(mult) rel(domainsep, a, b, c)`                                                                                                                                                                                           |
| Padding rows (self-jump at `ending_pc`)                                       | Covered                       | `enabler` gating plus an explicit padding constraint set                                                                                                                                                                                                                      |
| Public input / boundary                                                       | Covered                       | `crates/prover/src/public_data.rs` verifier-owned relation terms                                                                                                                                                                                                              |
| Continuations / recursion                                                     | Covered by a different design | stark-v's `recursion` crate is a Circle-STARK verifier-in-AIR; LeanVM's `rec_aggregation` verifies WHIR proofs. No reuse either way                                                                                                                                           |

## Gaps

**G1 — the DSL has no field abstraction (blocking, and not small).**
`crates/stwo-macros/src/trace_tables.rs` (`M31_PRIME`, `m31_pow`, `const_eval`,
literal lowering at lines 601–729), `air_fns.rs` (89 M31/QM31 references),
`components.rs` (39), `relations.rs` (10), `logup.rs` (5) all name M31, QM31,
`PackedM31`, `PackedQM31`, and `stwo::…` types directly. Making the macros
field-parametric is only the front half: the generated code targets stwo's
Circle-STARK prover, whose base field _is_ M31 by construction (circle-group FFT
over `p = 2^31 - 1`). KoalaBear is not a Circle-STARK field. So this is not a
macro refactor — it is a different proving backend.

Consequence: two honest options, neither of which is "a few files".

- _Re-instantiate_ LeanVM's design over M31/QM31. The AIR structure ports; the
  system stops being LeanVM (different `p`, different extension degree,
  different Poseidon, and every KoalaBear-specific guest — XMSS, the WHIR
  recursion — is invalidated).
- _Emulate_ KoalaBear inside M31. Every `Computation` MUL becomes a multi-limb
  62-bit product plus a quotient/remainder witness plus range checks — order
  10–30 extra columns and several lookups on the VM's hottest instruction, and
  the Poseidon16 precompile (the actual hot path for XMSS) becomes an
  emulated-field permutation. This is arithmetically expressible in the DSL
  today and economically indefensible.

Judgment: **genuinely reusable if solved, but out of scope for a DSL change.**

**G2 — no cross-row masks (non-blocking, genuinely reusable).** The workaround
(LogUp state relations) is the established stark-v pattern and is sound, but it
costs interaction columns where LeanVM pays a single mask, and it forces a
re-derivation of every transition constraint. Adding `prev(x)`/`next(x)` to the
felt language would touch `air_fns.rs` lowering (mask allocation and degree
accounting) and `trace_tables.rs` column-struct generation
(`eval.next_interaction_mask(ORIGINAL_TRACE_IDX, [0, 1])` instead of
`next_trace_mask()`), plus boundary-row handling. Already listed as future work
in `docs/felt-air-compiler.md`. Useful for stark-v independently of LeanVM.

**G3 — `max_degree` capped at 3 (non-blocking, narrow).** `air_fns.rs:225`.
LeanVM AIRs run at degree 5, 6, and 10. The compiler's materialization handles
this automatically — that is precisely what it is for — at the cost of extra
committed columns. Raising the cap would also require raising `logup_batch`'s
degree reasoning (`air_fns.rs:301`) and the stwo blowup factor. Reusable, but
the payoff is a column-count/blowup trade, not a capability.

**G4 — the intrinsic surface is RV32-shaped (non-blocking, LeanVM-specific).**
`vm_access` and the word intrinsics cover a large share of the DSL's specialized
code and none of it applies to a field-native, clock-free, write-once machine. A
LeanVM port would use only the generic core (`let`/`for`/`assert`/`constrain`/
`hint`/`emit`/`consume`/arrays/`inline fn`) plus `define_air!` tables. Nothing
needs to be added; the point is that the DSL's leverage on this VM is far
smaller than its leverage on RV32IM, which is where "just a few files" intuition
comes from.

## Verdict and scoped plan

**"Straightforward, a few files" is not accurate as stated.** It is accurate for
one narrow reading and wrong for the two readings that matter.

_If the goal is "prove LeanVM as it exists"_ — KoalaBear semantics, its
Poseidon16, its quintic extension, its XMSS guests — the DSL cannot do it at any
file count. G1 is a backend-level mismatch: stwo is Circle-STARK over
`p = 2^31 - 1`, LeanVM is multilinear/WHIR over `p = 2^31 - 2^24 + 1`. This is
not a gap to close in `crates/stwo-macros`.

_If the goal is "a LeanVM-shaped VM over M31, proven by stwo"_ — a Cairo-style
felt machine with `pc`/`fp`, write-once memory, four instructions, and two
precompiles — then the DSL is a good fit and the estimate is:

| Work                                                                                                                               | Files                                     | Effort                                                                                 |
| ---------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------- | -------------------------------------------------------------------------------------- |
| Schema: relations (`memory`, `bytecode`, `precompile_bus`, `state`), preprocessed range tables, `bytecode`/`memory`/padding tables | 1 (`schema.rs`-shaped)                    | ~1–2 days                                                                              |
| Execution component (`Computation` + `Deref` + `Jump` as one flag-dispatched `define_air_fns!` function, or two or three)          | 1–3                                       | ~3–5 days, most of it re-deriving the shift-based pc/fp transition as a state relation |
| Extension-op component over QM31 (degree 4, not 5) with the accumulator chain as a relation                                        | 1                                         | ~3–4 days                                                                              |
| Poseidon2 precompile wiring                                                                                                        | 0–1 (reuse `crates/air/src/poseidon2.rs`) | ~1 day                                                                                 |
| Runner/tracer: decode adapters, memory model, hint resolution                                                                      | 2–4                                       | ~1–2 weeks, and this is real work the DSL does not shrink                              |
| Prover roster, public data, boundary terms, tests                                                                                  | 2–3                                       | ~1 week                                                                                |

Call it **8–12 files and 4–6 weeks** for a working, tested prover — with the
AIR-authoring portion genuinely being "a few files", which is probably the
kernel of truth in the original expectation. The runner, the memory argument's
witness side, and the test/soundness work are where the time goes, and the DSL
does not compress those.

_The one reading where "a few files" holds outright_: writing the LeanVM **AIR
constraint definitions** only, over M31, ignoring witness generation, runner,
and proving integration. That is three `define_air_fns!` files plus a schema. It
is also not a prover.

Recommended next step if this is pursued: do not start with the execution table.
Start with a one-page spike that re-expresses LeanVM's `execution` AIR
(`tables/execution/air.rs`, 14 constraints) as a `define_air_fns!` function with
the pc/fp shift replaced by a `state(pc, fp)` relation, and count the resulting
columns and LogUp entries against LeanVM's 24 columns. That single number
decides whether the port is worth anything beyond an existence proof.
