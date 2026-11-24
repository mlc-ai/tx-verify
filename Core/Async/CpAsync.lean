-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tma

@[expose] public section

/-!
# Thread semantics: non-bulk asynchronous copies

The events of `cp.async`, its group commit and wait, and `cp.async.mbarrier.arrive`. When the copies
complete and what a wait observes are decided by the execution rules (OBJ-BULK-GROUP-TRACE,
DEP-BULK-WAIT, OBJ-MBAR-OBSERVE).
-/

namespace PTX

noncomputable section

/-! ## THREAD-CP-ASYNC — cp.async, its groups and cp.async.mbarrier.arrive
Statement: A `cp.async` produces one issue event: a copy of `cp-size` bytes from global memory to
  the executing CTA's shared memory, of which the first `src-size` bytes, or none when `ignore-src`
  is true, are read and the rest are zeros. `cp.async.commit_group`, `cp.async.wait_group` and
  `cp.async.mbarrier.arrive` each produce one event, and `cp.async.wait_all` produces a commit event
  followed by a wait event for no remaining group. A misaligned address or a `src-size` larger than
  `cp-size` produces an undefined-behaviour event.

Defs: cpAsyncSourceSize, cpAsyncTmpl

Source:
- §9.7.10.28.3.1: "Operand src specifies a location in the global state space and dst specifies a
    location in the shared state space."
- §9.7.10.28.3.1: "cp-size can only be 4, 8 and 16."
- §9.7.10.28.3.1: "Operand src-size represents the size of the data in bytes to be copied from src
    to dst and must be less than or equal to cp-size . In such case, remaining bytes in destination
    dst are filled with zeros. Specifying src-size larger than cp-size results in undefined
    behavior."
- §9.7.10.28.3.1: "If the source data is ignored then zeros will be copied to destination dst ."
- §9.7.10.28.3.1: "cp.async is treated as a weak memory operation performed in the generic proxy in
    the Memory Consistency Model ."
- §9.7.10.28.3.1: "Cache operator are treated as performance hints only."
- §9.7.10.28.3.1: "The .level::prefetch_size qualifier is treated as a performance hint only."
- §6.4.1: "The address must be naturally aligned to a multiple of the access size. If an address is
    not properly aligned, the resulting behavior is undefined."
- §9.7.10.28.3.2 (cp.async.commit_group)
- §9.7.10.28.3.3: "cp.async.wait_all is equivalent to : cp.async.commit_group; cp.async.wait_group
    0;"
- §9.7.15.16.18: "Causes an arrive-on operation to be triggered by the system on the mbarrier object
    upon the completion of all prior cp.async operations initiated by the executing thread."
- §9.7.15.16.18: "If no state space is specified then Generic Addressing is used."
- §9.7.15.16.18: "If the address specified by addr does not fall within the address window of
    .shared::cta state space then the behavior is undefined."

Direction: stricter

Applies: `cp.async.{ca,cg}.shared{::cta}.global` with every `cp-size`, with or without `src-size`
  or `ignore-src`, `.L2::cache_hint` and `.L2::{64B,128B,256B}`; `cp.async.commit_group`,
  `cp.async.wait_group`, `cp.async.wait_all`; `cp.async.mbarrier.arrive{.noinc}` with
  `.shared{::cta}` written or with a generic address

Premises: The addresses are aligned to `cp-size`, `src-size` is at most `cp-size`, the
  `ignore-src` operand is a predicate and the cache policy, when present, a defined 64-bit value.

Effect: Thread event construction. Grouping, waits, visibility and completion are execution rules.
  The event of a `cp.async` is a linear copy (`Kind.copy`) whose source is the first `src-size`
  bytes (all `cp-size` bytes without `src-size`, none when `ignore-src` is true) and whose
  destination is the `cp-size` bytes at `dst`; its completion mechanism is the non-bulk async-group
  (`Completion.asyncGroup`), which a later `cp.async.mbarrier.arrive` of the thread may also track,
  and it is performed in the generic proxy (`generic`). The bytes beyond the source are zeros
  (DEP-LINEAR-COPY-EFFECTS). Its accesses are weak and use the generic proxy (MEM-MODEL-CAUSALITY).
  The cache operator `.ca`/`.cg`, the prefetch size and the cache policy have no effect. The
  alignment rule of §6.4.1 is applied with the access size `cp-size` to both addresses.
  `cp.async.wait_all` is two events of the same instruction, a commit then a wait leaving no group,
  through sub-steps, as its stated equivalence says. A `cp.async.mbarrier.arrive` produces one event
  naming the 8-byte aligned `.shared::cta` mbarrier and whether `.noinc` is written; a generic
  address must be a generic shared pointer of the executing CTA (`genericSharedLoc`), and any other
  generic address has no rule; without `.noinc` the event increments the pending count, and its
  arrive-on is an asynchronous stage (OBJ-MBAR-ORIGIN).
-/

/-- The number of source bytes a `cp.async` of `size` bytes reads: all of them, its `src-size`
(at most `size`, otherwise undefined), or none when its `ignore-src` predicate is true. -/
def cpAsyncSourceSize (L : Launch) (g : Nat) (t : TState) (size : Nat) :
    CpAsyncSource → Exec Nat
  | .full => pure size
  | .size n => do
    let v ← readBits L g t 32 n
    unless v.toNat ≤ size do throw .badValue
    pure v.toNat
  | .ignore p => do
    let ignored ← readPred L g t p
    pure (if ignored then 0 else size)

/-- The event of `cp.async`, `cp.async.commit_group`, `cp.async.wait_group`, `cp.async.wait_all`
(a commit at sub-step 0, a wait at sub-step 1) or `cp.async.mbarrier.arrive`. -/
def cpAsyncTmpl (L : Launch) (g : Nat) (t : TState) : Op → Tmpl
  | .cpAsync db doff sb soff size source policy => ofExec do
    let d ← effAddr L g t .shared db doff
    let s ← effAddr L g t .global sb soff
    unless 0 < size ∧ d.addr % size = 0 ∧ s.addr % size = 0 do throw .misaligned
    let n ← cpAsyncSourceSize L g t size source
    bulkPolicy L g t policy
    pure (.copy (AsyncCopy.Spec.mk { loc := s, size := n } { loc := d, size := size } .asyncGroup
      .whole none true none) (next t))
  | .cpAsyncCommit => .asyncCommit (next t)
  | .cpAsyncWait false n => .asyncWait n (next t)
  | .cpAsyncWait true _ =>
    if t.sub = 0 then .asyncCommit { t with sub := 1 } else .asyncWait 0 { next t with sub := 0 }
  | .cpAsyncArrive noinc base off generic => ofExec do
    let m ← if generic then do
        let m ← genericSharedLoc L g t false base off
        unless m.addr % 8 = 0 do throw .misaligned
        pure m
      else mbarLoc L g t base off
    pure (.asyncArrive m noinc (next t))
  | _ => .ub .noRule

end

end PTX
