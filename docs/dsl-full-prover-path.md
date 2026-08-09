# From AIR DSL to prover DSL

<!-- cspell:ignore leanvm -->

> **Status: design study, not implemented.** Read-only inventory of the stark-v
> rv32im prover as it exists on `chore/scratchpad-cleanups`, a classification of
> everything a prover author still writes by hand, and a staged path to "a
> prover = one schema file + N `define_air_fns!` files + one guest-semantics
> file". No source was modified and no build was run while producing it; every
> line count below is `wc -l` on checked-in files, split at the first
> `#[cfg(test)]` where one exists.
>
> Companion documents: `docs/felt-air-compiler.md` (what the felt compiler does
> today), `docs/airs.md` (the active AIR architecture),
> `docs/leanvm-dsl-assessment.md` (capability inventory measured against a
> second, non-RV32 VM). This document does not restate their contents.

## The answer up front

**The AIR is already a DSL. The prover is not.**

Every constraint system in the rv32im proof roster is generated. There is no
handwritten `FrameworkEval` anywhere in either recursion branch, and
`crates/recursion/tests/air_dsl_guard.rs` enforces that structurally. But the
machinery _around_ the AIR — the proving pipeline, the verifier, the public-data
boundary terms, the preprocessed column generators, the witness-side
finalization, the opcode dispatch adapters — is all ordinary Rust, and it is
roughly three and a half times the size of the DSL it wraps.

Counting production lines (tests excluded) for the rv32im surface:

| Kind                         | Lines     | Where                                                                                                                                                                                                           |
| ---------------------------- | --------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| DSL invocations              | **1,957** | `crates/air/src/schema.rs` (286), `crates/air/src/opcodes/*.rs` (1,331 across 16 files), `crates/air/src/poseidon2.rs` (297), `crates/prover/src/components/mod.rs` roster (43)                                 |
| Hand-written, `air` crate    | 1,427     | `clock.rs` 379, `instructions.rs` 254, `digest.rs` 196, `preprocessed/` 484, plus 114 lines of module shims                                                                                                     |
| Hand-written, `prover` crate | 2,852     | `precompile.rs` 794, `poseidon2_precompile.rs` 451, `prover.rs` 464, `public_data.rs` 357, `poseidon2_channel.rs` 288, `preprocessed.rs` 233, `verifier.rs` 137, `lib.rs` 101, `errors.rs` 22, `relations.rs` 5 |
| Hand-written, `runner` crate | 2,721     | `lib.rs` 629, `commitment.rs` 551, `ops/` 740, `elf.rs` 172, `memory.rs` 162, `program.rs` 107, `cpu.rs` 93, `execute.rs` 84, plus 183 lines of smaller modules                                                 |

About 680 of `precompile.rs`'s 794 lines are the two documented binding
exemplars (`prove_binding`, `prove_hash_binding`) rather than the production
path; the VM prover uses only `joint_interaction_channel`,
`prove_joint_interaction_in_channel`, `verify_joint_interaction_in_channel`, and
`bind_joint_interaction` (`crates/prover/src/precompile.rs:145–233`). Netting
those out leaves roughly **6,300 hand-written production lines wrapping 1,957
lines of DSL**.

So the goal is reachable, but not by adding syntax to `define_air_fns!`. It
needs three new declarative surfaces above the AIR — public boundary data,
preprocessed table bodies, and the proving pipeline itself — plus the removal of
a set of hard-coded module-path contracts that currently make a second prover in
this workspace impossible to write cleanly.

## What the DSL already produces

Worth stating precisely, because it bounds what is left to do.

`define_air!` (`crates/stwo-macros/src/define_air.rs`) takes `relations:`,
`preprocessed:`, `clock_gap:`, `external:`, and `trace:` and emits:

- the `relations` module: one `Relation` wrapper per declared relation, the
  `Relations` bundle with `draw`/`dummy`, the `PreProcessedTrace` registry, the
  `PreprocessedTable` trait, and the `Counters` multiplicity accumulators
  (`crates/stwo-macros/src/relations.rs:340–508`);
- the `trace` module: every table struct, the `Tracer` aggregate with its
  `total_traces`/`max_table_len`/`print_tables` helpers, the `prover_columns`
  structs with `SIZE`/`NAMES`/`at(i)`/`from_eval`/`constraints()`, the
  `trace_op!` macro, and the per-table `*_lookups` / `*_interaction` /
  `*_register_multiplicities` macros
  (`crates/stwo-macros/src/trace_tables.rs:1791–1966`);
- a synthesized `clock_update` table wired to the declared range relation
  (`define_air.rs:260–272`), including its `max_delta`, which the parser derives
  from the trailing digits of the relation name — `range_check_20` yields
  `(1 << 20) - 1` with no second declaration.

`define_air_fns!` compiles single-assignment felt code to columns, constraints,
witness fills, and LogUp entries under a degree budget. Every opcode file is
_only_ the macro invocation: `crates/air/src/opcodes/lui.rs` is 35 lines total
with zero items outside the macro, and the same holds for all sixteen families
(`div.rs` is the largest at 215).

`components!` (`crates/stwo-macros/src/components.rs`) takes the
`trace:`/`detached:`/`lookup:` roster and emits the component modules, `Traces`,
`Claim` with `mix_into`/`main_trace_log_sizes`, `ClaimedSum`, `COMPONENT_COUNT`,
`gen_trace`, `gen_trace_at_log_sizes` with `FixedTraceError`,
`gen_interaction_trace`, and `Components::new`/`provers`/`verifiers`. The roster
in `crates/prover/src/components/mod.rs:6–42` is 43 lines and produces all of
it.

That is a lot. The gap is not in the AIR layer.

## Inventory of everything written by hand

Classification is (**A**) mechanically derivable from declarations that already
exist, (**B**) derivable given a new declarative surface, (**C**) irreducibly
hand-written. The bias is against C: for each candidate the question asked is
"what would a declaration have to say for the macro to generate this?", and C is
only assigned when the honest answer is "the whole thing, verbatim".

### Module-path contracts (A)

Macro codegen resolves several paths textually rather than through parameters:

- `components!` names the AIR crate **literally `air`** — `air::relation_eval`,
  `air::trace::prover_columns::*`, `air::trace::Tracer`, `air::#lookups_macro!`
  (`components.rs:183, 189, 213, 643`). `crates/air/src/lib.rs:10` contains
  `extern crate self as air;` solely to satisfy this inside the owning crate.
- `components!` and `relations!` name `crate::relations::*` and
  `crate::preprocessed::*` in the _consuming_ crate
  (`components.rs:188, 414, 949`; `relations.rs:340–376`), which is why
  `crates/prover/src/relations.rs` exists as a five-line re-export and
  `crates/prover/src/preprocessed.rs:7` opens with
  `pub use air::preprocessed::*`.
- `define_air!` emits `crate::trace::ClockGapTable`, `crate::trace::Access`, and
  `crate::schema::trace::CLOCK_GAP_MAX_DELTA` (`define_air.rs:268, 290, 312`),
  which is why `crates/air/src/trace.rs` and `crates/runner/src/trace.rs` exist
  as shims and `crates/air/src/preprocessed/mod.rs:21` re-exports generated
  types back into the shape the macro expects.

Roughly 80 production lines across five files, and — more importantly — a hard
blocker on a second prover: two `components!` invocations in one workspace both
resolve `air::`, so a LeanVM-shaped port would need
`extern crate leanvm_air as air;` inside its prover crate. `define_air_fns!`
already has the fix in miniature: `embedded_relations:` overrides the default
`crate::relations::Relations` (`air_fns.rs:278–286`). Generalizing that pattern
is a parameter-plumbing change, not a design change.

### Preprocessed lookup tables (A)

`crates/air/src/preprocessed/` is 484 production lines across seven files. Each
table implements `PreprocessedTable` with `LOG_SIZE`, `gen_columns()`,
`column_ids()`, and `index()` — where `index()` must be the exact packed-lane
inverse of `gen_columns()`, checked today by a hand-written `index_roundtrip`
test per table. Four of the six tables are pure Cartesian enumerations of bit
widths already encoded in their names; `range_check_20.rs:30–40` is a
`for i in 0..size { col[i] = i as u32 }`. `bitwise` and `range_check_m31` each
need one expression. The macro already parses bit widths out of these names for
the clock-gap bound, so the declaration site exists.

### Public data and boundary terms (B — highest value)

`crates/prover/src/public_data.rs` is 357 production lines that say the same
thing three times:

- the `PublicData` struct and its `Serialize`/`Deserialize` (fields 44–74);
- `mix_into` (168–199), which must bind every field into the transcript in a
  fixed order;
- `logup_sum` (202–338), which opens and closes the relation chains the trace
  cannot close on its own: `registers_state` at entry and exit, the `journal`
  chain, each Merkle root, all 32 register `memory_access` pairs, input words,
  output words.

Every one of those `combine` calls is a public-side emission into a relation
declared in `schema.rs`. A `mix_into` that forgets a field, or a `logup_sum`
whose sign is wrong, is a soundness bug that no AIR test catches — hence tests
like `transcript_binds_the_last_program_root_word` and
`logup_binds_the_last_program_root_word` (`public_data.rs:484–507`), which exist
precisely because the two functions can silently disagree. That is the signature
of code that wants to be one declaration.

### The proving pipeline (B)

`crates/prover/src/prover.rs` is 464 lines whose production content is a
thirteen-step numbered sequence: generate traces → precompute twiddles → build
the commitment scheme → bind public data → inject cached preprocessing → commit
the main trace → mix the claim → commit the detached Poseidon2 trace → joint
grind and draw relations → generate and commit the interaction trace → construct
components → optionally report deficits → `prove`/`prove_ex`.
`crates/prover/src/verifier.rs` (137) replays the identical order.

The sequence is fully determined by things that are already declared or
declarable: the roster (`components!`), the preprocessing registry
(`relations!`), which components are detached (`detached: { poseidon2 }`), the
public-data binder, and the channel type. The strongest evidence is that it has
been written twice: `crates/recursion/src/recursive_proof.rs` (1,250 lines) runs
the same preprocessing-commit → main-commit → draw-relations →
interaction-commit → prove sequence for the universal roster, with its own
`CommitmentSchemeProver` construction (`recursive_proof.rs:214`), its own
`RecursionInteractionClaim`, and its own verifier mirror. Five non-macro sites
in the workspace construct a `CommitmentSchemeProver`.

`crates/prover/src/lib.rs` (101) is the shapes that follow: `InteractionClaim`,
`Proof<H>`, `SegmentProof<H>`. `crates/prover/src/preprocessed.rs` (233) is the
serializable commitment cache — already VM-agnostic and already reused by
recursion through `preprocess_trace_with_channel`; it is library code, not
per-prover code.

### Witness-side finalization and clock gaps (B, with a large declaration)

`crates/runner/src/commitment.rs` (551) builds the `program`, `memory`,
`merkle`, and `poseidon2` tables at segment close: enumerate the distinct
addresses touched, emit initial values at clock 0 with multiplicity `+1` and
final values at their last clock with multiplicity `-1`, build the binary Merkle
tree over the leaves, and record the roots that `public_data.rs` then publishes.
Those four tables _are_ declared in `schema.rs:153–283` — only the fill is hand
written.

`crates/air/src/clock.rs` (379) is the mirror asymmetry: `clock_gap:` generates
the AIR component, but `ClockGapTable` and the gap-filling `trace_reg_access` /
`trace_mem_access` / `trace_instr_access` methods (`clock.rs:297, 327, 358`) are
hand-written extensions of the generated `Tracer`.

This is the least certain category-B entry. The declaration required is long and
deeply VM-specific, and it may end up less readable than the code. Treat it as
conditional (see Stage 5).

### Opcode dispatch adapters (B)

`crates/runner/src/ops/` is 740 production lines and `execute.rs` is an 84-line
match. Every adapter has the same body: pack `(clock, pc, rd, rs1, rs2, flags…)`
into `BaseField`s, call the generated `*_fill`, assign the returned next PC.
`crates/runner/src/ops/alu.rs:20–66` does that ten times for the register ALU
families. The information content is one table: opcode identity → family
function → flag tuple.

### Irreducible (C)

- **Machine semantics.** `crates/runner/src/lib.rs` (629: the execution loop,
  segmentation policy, memory-fault guards, I/O anchoring), `memory.rs` (162),
  `cpu.rs` (93), `elf.rs` (172), `program.rs` (107), `io.rs` (30), `syscalls.rs`
  (46), `machine.rs` (38). This is what the machine _is_; the DSL proves it, it
  does not define it. ~1,280 lines.
- **The decoder.** `crates/air/src/instructions.rs` (254). A `decode:` DSL is
  conceivable, but the payoff is one file and the failure mode of a subtly wrong
  generated decoder is severe.
- **Protocol primitives.** `poseidon2_channel.rs` (288) is a Fiat-Shamir channel
  and Merkle hasher construction; `digest.rs` (196) is the digest/protocol-id
  encoding; the joint-interaction core in `precompile.rs` (~110) is a two-proof
  binding protocol. These are protocol choices, not tables.
- **`relation_eval.rs`** (23): two traits that let generated components hand
  relation tuples to a circuit evaluator. Small, and it is the seam recursion
  depends on.

## Is it achievable today?

For the AIR, yes and it already is. For a prover, no. Here is the concrete floor
for a _new_ simple VM prover on today's macros — a register machine with a
handful of opcodes, one range check, and no recursion:

| #   | File                                 | Contents                                                     | Can the macros produce it?                         |
| --- | ------------------------------------ | ------------------------------------------------------------ | -------------------------------------------------- |
| 1   | `air/src/lib.rs`                     | `extern crate self as air;`, module list, tree-height consts | No — the `air` crate-name contract is textual      |
| 2   | `air/src/schema.rs`                  | `define_air!`                                                | **Yes, DSL**                                       |
| 3   | `air/src/opcodes/*.rs`               | N × `define_air_fns!`                                        | **Yes, DSL**                                       |
| 4   | `air/src/vm.rs`                      | `MachineState` trait required by `vm_access:`                | No — 19 lines, but must exist                      |
| 5   | `air/src/trace.rs`                   | re-export shim for `crate::trace::{Access, ClockGapTable}`   | No — path contract                                 |
| 6   | `air/src/clock.rs`                   | `ClockGapTable` + gap-filling tracer methods                 | No — witness side of `clock_gap:` is not generated |
| 7   | `air/src/relation_eval.rs`           | two traits `components!` resolves as `air::relation_eval::*` | No — path contract                                 |
| 8   | `air/src/preprocessed/*.rs`          | one `PreprocessedTable` impl per lookup + `mod.rs` shim      | No                                                 |
| 9   | `prover/src/components/mod.rs`       | `components!`                                                | **Yes, DSL**                                       |
| 10  | `prover/src/relations.rs`            | `pub use air::relations::*;`                                 | No — path contract                                 |
| 11  | `prover/src/preprocessed.rs`         | re-export + `Preprocessing` cache                            | Partly — the cache is reusable library code        |
| 12  | `prover/src/public_data.rs`          | struct + `mix_into` + `logup_sum`                            | No                                                 |
| 13  | `prover/src/prover.rs`               | the thirteen-step pipeline                                   | No                                                 |
| 14  | `prover/src/verifier.rs`             | the mirror                                                   | No                                                 |
| 15  | `prover/src/lib.rs`                  | `Proof`, `InteractionClaim`, re-exports                      | No                                                 |
| 16  | `runner/src/lib.rs`                  | run loop, segmentation                                       | No, and correctly so (C)                           |
| 17  | `runner/src/{cpu,memory,elf}.rs`     | machine state                                                | No, and correctly so (C)                           |
| 18  | `runner/src/execute.rs` + `ops/*.rs` | dispatch adapters                                            | No                                                 |
| 19  | `runner/src/commitment.rs`           | finalization tables                                          | No                                                 |
| 20  | `runner/src/trace.rs`                | `trace_op!` forwarder                                        | No — path contract                                 |

Rust lets you merge modules, so the _file_ count can be squeezed below twenty.
That is the wrong metric and worth saying plainly: **the problem is not that
there are many files, it is that the non-DSL files hold the soundness-critical
content.** A new VM prover today is roughly six DSL invocations and 3,000–4,000
lines of hand-written pipeline, boundary, and finalization code — and the
boundary and pipeline code is exactly where a mistake is invisible to every AIR
test.

## The path

Six stages. Each is independently shippable and regression-testable against the
existing rv32im prover; none requires the next. Recommended order is 1 → 6 → 2 →
3 → 4 → (5, conditional): Stage 6 is cheap and gives an immediate visible win,
Stage 4 must follow Stage 3 because the transcript order includes public data,
and Stage 5 should only ship if its declaration proves shorter than the code for
two different VMs.

### Stage 1 — parameterize the module-path contracts

New surface, extending the precedent already set by `embedded_relations:`:

```text
components! {
    air: my_air,                       // default: `air`
    relations: crate::relations,       // default: `crate::relations`
    preprocessed: crate::preprocessed, // default: `crate::preprocessed`
    trace: { … }, detached: { … }, lookup: { … },
}

define_air! {
    paths: { trace: crate::trace, schema: crate::schema },
    relations: { … } …
}
```

Replaces: `crates/prover/src/relations.rs`, the shim halves of
`crates/prover/src/preprocessed.rs`, `crates/air/src/trace.rs`,
`crates/runner/src/trace.rs`, `crates/air/src/preprocessed/mod.rs`, and the
`extern crate self as air;` in `crates/air/src/lib.rs`: ~80 lines touched across
five files, three of which disappear entirely.

Guard: extend `crates/recursion/tests/air_dsl_guard.rs` with an owner-source
policy rejecting `pub use` re-export shims whose only purpose is to satisfy a
macro path — the same shape as its existing `framework_eval_impls` and
`wrapper_macro_count` checks.

Effort: 2–3 days. Unblocks: any second prover in this workspace.

### Stage 2 — preprocessed tables from their declaration

Give `preprocessed:` entries a body:

```text
preprocessed: {
    range_check_20:  value in 0..2^20;
    range_check_8_8: limb_0 in 0..2^8, limb_1 in 0..2^8;
    bitwise:         a in 0..2^8, b in 0..2^8, op_id in 0..4
                     -> result = select(op_id, a & b, a | b, a ^ b);
}
```

Generates `LOG_SIZE`, `gen_columns()`, `column_ids()`, and — from the same
enumeration order — `index()`, so the two can no longer drift.

Replaces: `crates/air/src/preprocessed/*.rs`, 484 lines, seven files.

Guard: a golden test asserting the generated columns equal today's
`gen_columns()` output element-for-element, plus a generated per-table
`index_roundtrip` replacing the seven hand-written copies.

Effort: ~1 week. Risk: `index()` is a performance-critical inner loop
(`relations.rs:503–509` runs it per packed lane); the generated form must lower
to the same arithmetic, which is worth checking with a micro-benchmark before
deleting the handwritten tables.

### Stage 3 — a `public:` section

The highest-value stage, and the one justified by soundness rather than file
count. A new section in `define_air!` declaring public fields and the boundary
terms they open and close:

```text
public: {
    fields: {
        initial_pc: u32, final_pc: u32, clock: u32,
        initial_regs: [u32; 32], final_regs: [u32; 32], reg_last_clock: [u32; 32],
        program_root: option<digest>, initial_rw_root: option<digest>, …
    }
    boundary: {
        +registers_state(initial_pc, 1),
        -registers_state(final_pc, clock + 1),
        for i in 0..32 {
            +memory_access(REG_AS, i, 0,            bytes(initial_regs[i])),
            -memory_access(REG_AS, i, reg_last_clock[i], bytes(final_regs[i])),
        },
        for root in [program_root, initial_rw_root, final_rw_root] {
            +merkle(0, 0, root, root),
        },
        …
    }
}
```

Generates the `PublicData` struct with its serde impls, `mix_into` in
declaration order, and `logup_sum` with the existing batch inversion. One
declaration, so `mix_into` and `logup_sum` cannot disagree.

Replaces: `crates/prover/src/public_data.rs`, 357 lines.

Guard: the existing `logup_sum_constrains_*` and
`*_binds_the_last_program_root_word` tests become generated per boundary term
(each field must change both the transcript digest and the LogUp sum); add an
`air_dsl_guard.rs` policy rejecting hand-written `Relation::combine` calls in
owner sources.

Effort: ~2 weeks. Risk: `option<digest>` and the input/output word vectors are
variable-length public data whose transcript encoding includes explicit presence
flags and lengths (`public_data.rs:177–198`); the declaration must express that,
not paper over it.

### Stage 4 — `define_prover!`

```text
define_prover! {
    air: air,
    roster: crate::components,
    public: crate::public_data::PublicData,
    channel: MC: MerkleChannel,
    transcript: [
        public_data,
        preprocessed_commitment,
        main_commitment,
        claim,
        detached(poseidon2) { join: grind(INTERACTION_POW_BITS) },
        relations,
        interaction_commitment,
        interaction_claim,
        stark,
    ],
    fixed_layout: yes,        // emits the *_at_log_sizes variants and FixedTraceError
    transcript_seam: yes,     // emits the VmClaimTranscript trait and NativeVmClaimTranscript
}
```

Generates `prove_*`/`verify_*` in both the dynamic and fixed-layout forms,
`Proof<H>`, `SegmentProof<H>`, `InteractionClaim`, and the caller-owned
transcript seam that recursion needs.

Replaces: `crates/prover/src/prover.rs` (464), `verifier.rs` (137), most of
`lib.rs` (~80). The larger prize is that
`crates/recursion/src/recursive_proof.rs` (1,250) becomes a second
`define_prover!` invocation with a different roster, channel, and transcript
list instead of a second hand-written pipeline.

Guard: byte-identical serialized proofs and identical channel digests against
the current pipeline under the pinned protocol identity — the pipeline's whole
contract is its transcript order, so a golden digest is the right pin. Add an
`air_dsl_guard.rs` policy rejecting `CommitmentSchemeProver` construction in
owner sources (five non-macro sites today).

Effort: 3–4 weeks. Must follow Stage 3.

### Stage 5 — `finalize:` and the clock-gap witness (conditional)

```text
clock_gap: { bound_by: range_check_20, relation: memory_access, witness: generate }

finalize: {
    program: enumerate(program_reads) with multiplicity,
             leaves: [value_0, value_1, value_2, value_3] at addr + 0..4,
             tree: merkle(hash: poseidon2_io, height: MAX_TREE_HEIGHT),
             root -> public.program_root,
    memory:  enumerate(mem_clock) in address_space 1,
             initial: +1 at clock 0, final: -1 at last_clock,
             tree: merkle(…), roots -> public.{initial_rw_root, final_rw_root},
}
```

Replaces: `crates/runner/src/commitment.rs` (551) and `crates/air/src/clock.rs`
(379).

Guard: byte-equal tracer tables for a fixed guest binary before and after, plus
the existing finalized-capacity checks.

Effort: 3–4 weeks, and the highest risk in the plan. **Ship it only if the
declaration is demonstrably shorter and clearer than the code for two different
memory models.** The generated `Tracer` is already RV32-shaped —
`reg_clock: [u32; 32]`, `mem_clock`, `mem_initial`, `program_reads`
(`trace_tables.rs:1793–1810`) — and a `finalize:` designed only around
clock-ordered, Merkle-committed RW memory would deepen that. If the declaration
cannot also express a write-once committed-vector memory, it is the wrong
declaration and `commitment.rs` should be accepted as category C.

### Stage 6 — `dispatch:`

```text
dispatch: {
    on: crate::instructions::Opcode,
    add => base_alu_reg(clock, pc, rd, rs1, rs2, flags = [1,0,0,0,0]),
    sub => base_alu_reg(clock, pc, rd, rs1, rs2, flags = [0,1,0,0,0]),
    …
}
```

Generates `execute()` and every adapter in `runner/src/ops/`.

Replaces: `crates/runner/src/ops/` (740) and `crates/runner/src/execute.rs`
(84).

Guard: the generated match must be exhaustive over the opcode enum — a compile
error, which is a stronger guard than any test. Keep the existing per-opcode
`test_bin_e2e!` roster unchanged as the behavioral pin.

Effort: ~1 week. Independent of every other stage.

## Risks

**Compile time.** `crates/stwo-macros/src/air_fns.rs` is already 5,429 lines of
proc-macro and `define_air!` on `schema.rs` expands to the whole `Tracer`,
relations registry, and five table components in one unit. Stages 3 and 4 put
the public data and the entire pipeline into that same expansion. Measure
`cargo build --timings` before and after each stage; if `define_prover!`
dominates, split it into a types macro and a functions macro so editing the
pipeline does not re-expand the roster. No numbers are claimed here — none were
measured.

**Error messages.** A typo inside `public:`'s boundary block would today be a
type error pointing at a line of `public_data.rs`. `define_air.rs:82–89` already
shows the standard to hold: named-key errors with real spans. Every new section
needs the same treatment, and generated items should carry `#[doc]` attributes
naming their declaration site.

**Debuggability.** `prover.rs` carries the `tracing` spans and the
`track-relations` deficit reporting that make a failing proof diagnosable. A
generated pipeline must emit the same spans and keep the
`#[cfg(feature = "track-relations")]` clauses, and `cargo expand` output must
stay readable — that is the debugger of last resort for a generated pipeline.

**Review surface.** Auditors today read `prover.rs`'s numbered steps to check
the transcript order. After Stage 4 the reviewable artifact is the
`transcript: [...]` list, which is arguably better — but only if the macro's
lowering of that list is itself pinned by the golden channel-digest test. Make
that test a Stage 4 gate, not a follow-up.

**Bounds this path does not move.** `max_degree` is capped at 2 or 3
(`air_fns.rs:225`), there are no cross-row masks, and the whole macro crate is
M31-only. Those are `docs/leanvm-dsl-assessment.md`'s G1–G3 and they are
untouched by everything above. "A prover in a few files" means a few files of
_this_ DSL, over M31, at degree ≤ 3.

## Sanity check against both targets

**Does stark-v itself shrink to a few DSL files?** Half of it does, and that is
the correct half. After Stages 1–4 and 6, the proving stack is:

- `crates/air/src/schema.rs` — `define_air!` with relations, preprocessed
  bodies, `clock_gap:`, `public:`, `external:`, `trace:`
- `crates/air/src/opcodes/*.rs` and `poseidon2.rs` — `define_air_fns!`
- `crates/prover/src/components/mod.rs` — `components!` + `define_prover!`

Four DSL files, and the entire "how a STARK is assembled" layer disappears from
the visible surface. What remains hand-written is the machine: the execution
loop and segmentation policy, memory, CPU, ELF loading, the decoder, the syscall
ABI, and the channel/digest primitives — about 1,800 production lines across six
or seven files, plus `commitment.rs` if Stage 5 is skipped. That is ordinary
software with ordinary tests, and it is the part the DSL has no leverage on. The
honest formulation of the end state is **"a prover = one schema file + N
`define_air_fns!` files + one roster file + a small machine crate"**, not "a
prover = a few macro files".

**Does the LeanVM-shaped port become a few files for real?**
`docs/leanvm-dsl-assessment.md` estimates 8–12 files and 4–6 weeks for a
LeanVM-shaped VM over M31, with the time going to the runner, the memory
argument's witness side, and the prover/public-data/test work. Under this path:

- Stage 1 removes a genuine blocker, not an annoyance: two `components!`
  invocations in one workspace both resolve `air::` today.
- Stage 2 removes its range-table files.
- Stage 3 collapses "public data, boundary terms" into the `public:` block: −1
  file, roughly −1 week.
- Stage 4 collapses "prover roster" into one `define_prover!`: −1 file, several
  days.
- Stage 6 helps marginally — LeanVM has four instructions, so its dispatch is
  small either way.
- **Stage 5 does not help it at all.** LeanVM's memory is a committed write-once
  vector with an access-count column, not a clock-ordered Merkle finalization;
  its `finalize:` would be a different declaration entirely. This is the
  strongest independent argument for keeping Stage 5 conditional.
- The 3–5 days of re-deriving the `shift[pc]`/`shift[fp]` transition as a state
  relation is untouched — that is gap G2, outside this path.

Revised estimate: **5–7 files and 3–4 weeks**, with the residue being exactly
what the assessment already identified as irreducible — the runner and the
memory-argument witness side. The path meaningfully improves the second-VM case;
it does not turn a VM port into a weekend.

## Summary

| Stage                           | New macro surface                                                           | Files eliminated                                                                                                                 | Prod lines | Effort |
| ------------------------------- | --------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------- | ---------- | ------ |
| 1. Path contracts               | `components! { air:, relations:, preprocessed: }`, `define_air! { paths: }` | `prover/relations.rs`, `air/trace.rs`, `runner/trace.rs` (3) — plus the shim halves of `prover/preprocessed.rs` and `air/lib.rs` | ~80        | 2–3 d  |
| 6. Dispatch                     | `dispatch: { opcode => family(args, flags) }` in `define_air_fns!`          | `runner/ops/*.rs` (10), `runner/execute.rs` (11)                                                                                 | 824        | ~1 w   |
| 2. Preprocessed bodies          | `preprocessed: { name: col in 0..2^k … -> expr }`                           | `air/preprocessed/*.rs` incl. `mod.rs` (7)                                                                                       | 484        | ~1 w   |
| 3. Public data                  | `public: { fields: …, boundary: … }` in `define_air!`                       | `prover/public_data.rs` (1)                                                                                                      | 357        | ~2 w   |
| 4. Pipeline                     | `define_prover! { roster, channel, transcript: [...] }`                     | `prover/prover.rs`, `prover/verifier.rs` (2), most of `prover/lib.rs`; re-expresses `recursion/recursive_proof.rs` (1,250)       | 681        | 3–4 w  |
| 5. Finalization _(conditional)_ | `finalize: { … }`, `clock_gap: { witness: generate }`                       | `runner/commitment.rs`, `air/clock.rs` (2)                                                                                       | 930        | 3–4 w  |

Stages 1–4 and 6: ~2,430 production lines and 24 files removed, ~7–9 weeks. With
Stage 5: ~3,360 lines and 26 files, ~11–13 weeks. Against a hand-written surface
of ~6,300 production lines, that leaves the machine — the execution loop,
memory, CPU, ELF loading, decoder, syscall ABI, and channel primitives — and
nothing else.
