# Syscalls and an output journal (proposal — not implemented)

> **Status: design only.** Nothing in this document is implemented. The VM
> currently has no `ecall`/syscall support; a guest containing an `ecall`
> instruction fails to decode (`RunError::InvalidInstruction`). This file
> records a proposed design and the debugging findings from a prototype so a
> future implementation can resume cleanly. It deliberately claims no working
> feature: an unproven capability that looks like a committed output would be
> worse than no capability at all.

## Motivation

The fixed output region (`__output_data`) forces two constraints: the output is
size-bounded, and every output word must be written in the _final_ continuation
segment (the runner enforces this by cutting a segment boundary just before the
first output store — see `run_segments_impl`). A streamed, digest-anchored
output would remove both: the guest commits an unbounded sequence of words, the
VM folds them into a running hash, and only the final digest is public. This is
the RISC Zero "journal" pattern, and stark-v is well-suited to it because the
Poseidon2 sponge is already an in-AIR primitive.

The same ISA hook — decode `ecall`, dispatch on a syscall id — is also what
guest-callable precompiles need (`docs/precompiles.md`), so the two would share
a front end.

## Soundness requirement (why the execution layer alone is not enough)

A journal digest is only meaningful if the segment STARK _proves_ three things,
so no prover can fake `final`:

1. Each step is one Poseidon2 permutation of the previous state with the
   committed word absorbed.
2. The absorbed words are exactly the register values the execution produced
   (bound to the register file).
3. The steps form one unbroken, ordered chain from the public `initial` to the
   public `final` — no insertions, drops, or reorderings.

Because all three must hold in-AIR before the digest can be exposed, the journal
must be built proof-first: the digest may only appear on `PublicData` /
`Boundary` once the AIR enforces it. A runner-level journal with no AIR backing
must not exist, because its `final` value would look like a commitment while
being forgeable.

## Proposed in-AIR construction

- **`ecall` trace table** (`define_air!` schema): one row per COMMIT — `clock`,
  `pc`, the `a0` register read, a per-segment `step` index, the 16-lane `prev`
  and `next` states. Derived: the permutation input `in = prev + a0-in-rate`
  (degree 1). Lookups: `program_access`, the `pc`/`clock` `registers_state`
  transition, the `a0` `memory_access` read, `range_check_20` on the clock gap,
  an atomic `poseidon2_io(in, next)` binding discharged by the Poseidon2
  component's `io` rows, and a `journal` chain (consume `journal(step, prev)`,
  emit `journal(step+1, next)`).
- **`journal` relation** (arity 17: `step` + 16 lanes): the per-row consume/emit
  telescopes across the segment; endpoints are anchored by public
  `journal(0, initial)` and `journal(n_commits, final)` terms.
- **Witness**: record the `ecall` row and a Poseidon2 `io` row so the
  permutation is proven by the existing component; `finalize_commitments` must
  append to the Poseidon2 table rather than reset it, so the execution-recorded
  `io` rows survive the Merkle-tree build.
- **Public data / boundary**: `PublicData` and `Boundary` gain `initial`/`final`
  journal fields chained across segments alongside pc / regs / memory roots, so
  the recursion tree root exposes the whole run's digest.

## Prototype findings

A prototype of the above was built and reverted. Two results are worth keeping:

- The novel parts are sound in isolation: the `journal` chain and its public
  anchors balance exactly (removing both leaves the global LogUp sum unchanged),
  and the `poseidon2_io` emit/consume counts match.
- The blocker is a codegen issue, not the design: wiring a _newly added_
  `define_air!` trace table left a LogUp imbalance in the standard relations.
  Isolation pinned the first culprit to `range_check_20` multiplicity
  registration for the new table (removing that lookup changed the global sum,
  which means the consume was not matched by a registered preprocessed emit),
  with a second standard-chain residual behind it. The place to start is how
  `components!` / `define_air!` generate `register_multiplicities` and the
  interaction trace for a freshly added trace table — not any journal-specific
  logic.
