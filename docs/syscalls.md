# Syscalls and an output journal

> **Status: syscall front end implemented; proof-bound calls remain planned.**
> The decoder accepts only canonical `ecall` (`0x00000073`), program commitment
> rows encode it canonically, and the runner routes `a7`/`a0` through an
> internal dispatcher. Every syscall ID currently fails with
> `RunError::UnsupportedSyscall` before the PC advances. No runner journal,
> public digest, COMMIT handler, or guest SDK call exists yet.

## Motivation

The fixed output region (`__output_data`) forces two constraints: the output is
size-bounded, and every output word must be written in the final execution
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
must be built proof-first: the digest may only appear on VM `PublicData` and the
recursive `MachineState::public_io_state` once the AIR enforces it. A
runner-level journal with no AIR backing must not exist, because its `final`
value would look like a commitment while being forgeable.

## Proposed in-AIR construction

- **`ecall` trace table** (`define_air!` or `define_air_fns!`): one row per
  COMMIT — `clock`, `pc`, the `a0` register read, a per-segment `step` index,
  the 16-lane `prev` and `next` states. Derived: the permutation input
  `in = prev + a0-in-rate` (degree 1). Lookups: `program_access`, the
  `pc`/`clock` `registers_state` transition, the `a0` `memory_access` read,
  `range_check_20` on the clock gap, an atomic `poseidon2_io(in, next)` binding
  discharged by the Poseidon2 component's `io` rows, and a `journal` chain
  (consume `journal(step, prev)`, emit `journal(step+1, next)`).
- **`journal` relation** (arity 17: `step` + 16 lanes): the per-row consume/emit
  telescopes across the segment; endpoints are anchored by public
  `journal(0, initial)` and `journal(n_commits, final)` terms.
- **Witness**: record the `ecall` row and a Poseidon2 `io` row so the
  permutation is proven by the existing component; `finalize_commitments` must
  append to the Poseidon2 table rather than reset it, so the execution-recorded
  `io` rows survive the Merkle-tree build.
- **Public data / recursive statement**: VM `PublicData` gains the initial and
  final journal states. The leaf adapter maps them into
  `MachineState::public_io_state`, which is already part of every recursive
  `SpanStatement`, so binary folding proves journal continuity to the root.

## Implementation order

1. `[done]` Add `ecall` decoding and a runner dispatch interface without
   exposing any unauthenticated journal value.
2. `[in progress]` Define the COMMIT component through `define_air!` or
   `define_air_fns!`; no manual `FrameworkEval` component is allowed because the
   recursion leaf verifier will consume this AIR.
3. `[pending]` Prove, in a focused release test, that a minimal new table's
   standard relation multiplicities and interaction trace close before adding
   journal logic.
4. `[pending]` Add the Poseidon2 transition and journal-chain relation, with one
   negative test for a changed word, broken state, dropped step, inserted step,
   and reordered step.
5. `[pending]` Bind per-segment journal endpoints into VM `PublicData` and the
   Fiat-Shamir transcript.
6. `[pending]` Extend the recursion leaf adapter and statement semantics to map
   the proven endpoints into `MachineState::public_io_state`.
7. `[pending]` Expose a guest SDK COMMIT call only after VM proof, continuation,
   and recursive-root tests all reject forged journal data.
