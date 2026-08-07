# Syscalls and the output journal

> **Status: implemented and validated through a recursive root.** Canonical
> `ecall` dispatches on `a7`. Syscall ID 1 authenticates the `a0` word, advances
> a Poseidon2 journal, and exposes only proof-bound segment endpoints. Every
> other ID fails with `RunError::UnsupportedSyscall` before the PC advances.

## Current capability

The active implementation proves COMMIT calls from instruction execution to the
recursive statement boundary:

- `crates/air/src/schema.rs` defines `commit` directly through the existing
  `define_air!` DSL. There is no manual component or syscall-specific macro.
- `guest_lib::commit(u32)` is the guest API. It places selector 1 in `a7`, the
  committed word in `a0`, and executes the canonical `ecall`.
- The row authenticates canonical `ecall`, `a7 == 1`, the `a0` register read,
  the PC/clock transition, and the register access clocks.
- The runner records the journal Poseidon2 call before commitment finalization.
  Merkle construction appends its Poseidon2 rows, so it cannot erase journal
  calls already present in the trace.
- VM `PublicData` and its Fiat-Shamir transcript contain the initial digest,
  final digest, COMMIT count, and last COMMIT clock.
- Host continuation requires each segment's final digest to equal the next
  segment's initial digest.
- The recursion leaf claim binds all four journal fields. Its statement maps the
  initial and final digests to `MachineState::public_io_state`, so ordinary
  binary statement folding carries journal continuity toward the root.

The one- and two-COMMIT guest fixtures use the SDK. A real SDK COMMIT execution
produces and verifies a constant-size recursive root, while application and VM
claim mutation tests reject forged journal boundaries.

## Journal transition

The persistent journal state is an eight-word canonical M31 digest. A COMMIT of
one arbitrary `u32` register value constructs this 16-word Poseidon2 input:

```text
input[0..8]   = previous digest
input[8..12]  = a0 as four little-endian byte limbs
input[12]     = 0x434f4d4d (COMMIT domain)
input[13..16] = 0
```

The existing `poseidon2_io` relation binds every input and output lane to one
full permutation. The next journal digest is `output[0..8]`. Byte limbs are used
because every `u32` is valid guest data while one M31 limb cannot represent all
`u32` values canonically.

## Ordered chain invariant

The `journal` relation has arity 10:

```text
(step, last_commit_clock, digest[0..8])
```

Each active COMMIT row consumes `(step, previous_commit_clock, previous_digest)`
and emits `(step + 1, execution_clock, next_digest)`. The row range-checks
`step`, both clocks, and `execution_clock - previous_commit_clock - 1`.
Therefore every link uses a strictly later authenticated execution clock; a
prover cannot reorder valid COMMIT rows by assigning different step witnesses.

VM public terms emit `(0, 0, initial_digest)` and consume
`(commit_count, last_commit_clock, final_digest)`. Together with the atomic
Poseidon2 relation and authenticated `a0` read, this rules out changed words,
broken states, dropped rows, inserted endpoints, and reordered clock links.

The step and clock restart at each segment boundary. The digest itself persists
in the CPU and is the value chained by continuation and recursive statements.
This gives each segment an independently provable local chain while preserving
one application journal across the complete execution.

## Motivation and scope

The fixed output region requires every public output word to fit in memory and
to be written in the final segment. A digest-anchored journal lets an
application authenticate a sequence across segments without carrying all words
in the root proof. Per-segment trace capacity still applies; constant root proof
size does not mean unlimited work in one segment.

The same canonical `ecall` front end will also dispatch guest-callable
precompiles described in `docs/precompiles.md`. Those features remain planned
and must reuse the existing AIR DSL.

## Implementation checklist

1. `[done]` Decode canonical `ecall` and reject unsupported syscall IDs before
   state mutation.
2. `[done]` Define COMMIT through `define_air!` and authenticate `a7`, `a0`, and
   the execution/register relations.
3. `[done]` Prove the minimal COMMIT row closes its standard VM relations.
4. `[done]` Add the Poseidon2 transition, strictly execution-ordered journal
   relation, and adversarial VM tests.
5. `[done]` Bind digest endpoints, count, and last clock into VM public data and
   its transcript.
6. `[done]` Validate the continuation boundary and recursive leaf/root mapping
   with a real COMMIT proof, including forged recursive claims.
7. `[done]` Add the guest SDK COMMIT call and its unit, segmented, and
   application-root tests.

The complete path verifies an SDK COMMIT-derived digest from one constant-size
root without accepting any runner-only journal value.
