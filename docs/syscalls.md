# Syscalls and the output journal (ECALL)

> **Status.** The ECALL instruction and the output journal are implemented at
> the **execution level** and covered by runner tests. Decoding, the COMMIT
> syscall, the running Poseidon2 journal sponge, cross-segment chaining, and the
> guest API all work and are proven correct against a host recomputation. The
> **in-AIR proof** of the journal (so `final_journal` becomes a sound
> public/boundary claim) is designed below and partially built; a LogUp-balance
> issue in the new `define_air!` trace table's multiplicity/interaction codegen
> is the one open item — see "Open item" at the end.

## Motivation

The fixed output region (`__output_data`) forces two awkward constraints: the
output is size-bounded, and every output word must be written in the _final_
continuation segment (the runner enforces this by cutting a segment boundary
just before the first output store — see `run_segments_impl`). A streamed,
digest-anchored output removes both: the guest commits an unbounded sequence of
words, the VM folds them into a running hash, and only the final digest is
public. This is the RISC Zero "journal" pattern, and stark-v is well-suited to
it because the Poseidon2 sponge is already an in-AIR primitive.

The same ISA hook — decode ECALL, dispatch on a syscall id — is what
guest-callable precompiles need, so this and `docs/precompiles.md` share a front
end.

## Execution model (implemented)

- **ISA.** `Opcode::Ecall` decodes the SYSTEM encoding (`0x00000073`,
  `funct3 == 0`, `imm12 == 0`). The one syscall is COMMIT; additional syscalls
  will dispatch on `a7`.
- **Journal.** A 16-lane Poseidon2 sponge (`runner::ops::system::Journal`),
  genesis all-zero. `absorb(state, word)` adds the word's two 16-bit halves into
  rate lanes 0 and 1 (each half is a valid M31 element, so the absorption is
  injective) and applies one permutation. The state is cumulative across the
  whole run and chains from one segment to the next.
- **RunResult.** Each segment carries `initial_journal` / `final_journal`; the
  final segment's `final_journal` is the run's committed output digest.
- **Guest API.** `guest_lib::io::commit_word(u32)` (an `ecall` with the word in
  `a0`) and `commit_bytes(&[u8])`.
- **Tests.** `crates/runner/tests/journal.rs`: the journal matches a host
  recomputation, chains across segments, and starts at genesis.

## In-AIR proof (design)

To make `final_journal` a sound claim rather than an execution-level value, the
journal hashing must be proven in the segment STARK and the digest carried on
`PublicData` → `Boundary` → the recursion tree, exactly as the memory roots are.

The design, mirroring the recursion crate's proven `channel_replay` sponge:

- **`ecall` trace table** (`define_air!` schema). One row per COMMIT: `clock`,
  `pc`, the `a0` register read (`src` access), a per-segment `step` index, the
  16-lane `prev` state and 16-lane `next` state. Derived: the permutation input
  `in = prev + a0-in-rate` (degree-1). Lookups: `program_access(pc, ECALL, …)`,
  the `pc`/`clock` `registers_state` transition, the `a0` `memory_access` read,
  `range_check_20` on the clock gap, an atomic `poseidon2_io(in, next)` binding
  (discharged by the reused Poseidon2 component's `io` rows), and a `journal`
  chain: consume `journal(step, prev)`, emit `journal(step+1, next)`.
- **`journal` relation** (arity 17: `step` + 16 lanes). The per-row consume/emit
  telescopes across the segment; the endpoints are anchored by public
  `journal(0, initial_journal)` (emit) and `journal(n_commits, final_journal)`
  (consume) terms in `PublicData::logup_sum`.
- **Witness.** `system::ecall` records the `ecall` row and a Poseidon2 `io` row
  (`poseidon2_traced_state(.., io = true)`), so the permutation is proven by the
  existing component. `finalize_commitments` must NOT reset the Poseidon2 table
  (execution already recorded the journal `io` rows; the Merkle-tree build
  appends to them).
- **Public data / boundary.** `PublicData` gains `initial_journal`,
  `final_journal`, `n_commits`; `Boundary` gains the journal endpoints and
  chains them (`left.final_journal == right.initial_journal`) alongside pc /
  regs / memory roots, so the tree root exposes the whole run's digest.

This construction was verified in isolation to be sound: the `journal` chain and
its public anchors balance exactly (removing them leaves the global LogUp sum
unchanged), and the `poseidon2_io` emit/consume counts match (8 ecall rows ⇄ 8
Poseidon2 `io` rows in the reference guest).

## Open item

Wiring the `ecall` table through the core `define_air!` codegen leaves a
residual LogUp imbalance in the _standard_ relations (not the journal or
Poseidon2 parts, which balance). Isolation pinned the first culprit to
`range_check_20` multiplicity registration for the newly-added table: removing
that lookup changes the global sum, which means the consume is not matched by a
registered preprocessed emit. A second standard-chain residual remains after
that. The next step is to audit how `components!` / `define_air!` generate
`register_multiplicities` and the interaction trace for a freshly-added trace
table, starting from `range_check_20`, rather than any journal-specific logic.
