-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX

/-! ## OBJ-CTA-BARRIER-SYNC — named-resource histories refer to source arrivals

Statement: A CTA barrier instance is a barrier number together with a generation of its resource. An
  arrival of either form (`bar.sync` or `bar.arrive`) in an instance orders the arriving thread's
  earlier accesses before the later accesses of every thread that has passed a `bar.sync` of the
  same instance. A `bar.sync` returns only after its generation has completed, and a `bar.arrive`
  returns once its warp's arrival is recorded. An arrival that the resource cannot perform is
  ERR-CTA-BARRIER.

Defs: CtaBarSources, CtaBarHistoryOk, CtaBarArrivalK, CtaBarK, CtaBarDone, CtaBarSync

Source:
- §9.7.15.1: "barrier{.cta} instruction causes executing thread to wait for all non-exited threads
    from its warp and marks warps’ arrival at barrier."
- §9.7.15.1: "barrier{.cta}.arrive does not cause executing thread to wait for threads of other
    participating warps."
- §9.7.15.1: "The barrier{.cta}.sync or barrier{.cta}.red or barrier{.cta}.arrive instruction
    guarantees that when the barrier completes, prior memory accesses requested by this thread are
    performed relative to all threads participating in the barrier. The barrier{.cta}.sync and
    barrier{.cta}.red instruction further guarantees that no new memory access is requested by this
    thread before the barrier completes."
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- §8.9.4: "A bar{.cta}.sync or bar{.cta}.red or bar{.cta}.arrive operation synchronizes with a
    bar{.cta}.sync or bar{.cta}.red operation executed on the same barrier."

Direction: reading

Applies: CTA barrier arrival events of both forms (`bar.sync`, `bar.arrive`) with omitted or
  explicit participant counts

Premises: Resource histories contain unique source-event references and complete collective
  arrivals; source threads and operands match the recorded CTA-local operations.

Effect: Named barrier synchronization used by MEM-BASE-CAUSALITY (`CtaBarSync`), the history used by
  the needs of both forms (`KindNeeds`, DEP-ORDER), and the history that ERR-CTA-BARRIER checks for
  an arrival the resource cannot perform. The needs are: for each lane of the warp, its arrival in
  the warp's record or its exit recorded before it (both forms, the warp wait of the first quoted
  sentence); for `bar.sync`, also the release of its generation (`CtaBarDone`) and the records that
  the release counted. The direction is `reading` because the model takes a `bar.arrive` to be
  performed, with its warp's arrival recorded, when its warp's lanes have executed it.

Review: The warp wait of a `bar.arrive` is a need like that of a `bar.sync`: a lane passes its
  `bar.arrive` only after every non-exited lane of its warp has executed it, so its warp's record
  exists, and the warp's lanes are witnesses of its return. A history contains the arrivals the
  resource performed. `bar.arrive` (`BarMode.arrive`) gives no synchronizes-with edge as target:
  §8.9.4 lists only `bar{.cta}.sync` and `bar{.cta}.red` as the operation synchronized with, and
  §9.7.15.1 gives no guarantee about the arriving thread's later accesses. Accesses of a thread
  after its `bar.arrive` are therefore unordered with the other participants. The arrival does not
  wait for the other warps; a later arrival of the same warp can never take its place in a
  generation.
-/

/-- Each record of the history of CTA `cta` is backed by actual source events: the lanes of an
arrival and the thread of an exit belong to that CTA and execute the matching instruction with
the recorded operands. -/
def CtaBarSources (L : Launch) (X : Execution) (cta : Nat) :
    CtaBarrier.Record EvId → Prop
  | .exit g e => g < L.block ∧ e.1 = cta * L.block + g ∧
      ∃ pc, X.get e = some ⟨pc, .exit⟩
  | .arrival id _ count lanes => ∀ p ∈ lanes,
      p.1 < L.block ∧ p.2.1 = cta * L.block + p.1 ∧
      ∃ pc, X.IsBarArrival p.2 id count pc

/-- The recorded histories of all CTAs of the launch are valid: no source event is counted twice,
every record is backed by source events, and the barrier resources accept the records in order.
Incomplete lane arrivals may remain outside the history until the warp arrives collectively. -/
def CtaBarHistoryOk (L : Launch) (X : Execution) : Prop :=
  (∀ c, L.grid ≤ c → X.barriers c = []) ∧
  ∀ c < L.grid,
    ((X.barriers c).flatMap CtaBarrier.Record.refs).Nodup ∧
    (∀ r ∈ X.barriers c, CtaBarSources L X c r) ∧
    ∃ s, CtaBarrier.run L.block {} (X.barriers c) = .ok s

/-- `e` is an arrival of either form at instance `key`: `key % 16` is the barrier ID and
`key / 16` its actual resource generation. -/
def CtaBarArrivalK (L : Launch) (X : Execution) (e : EvId) (key : Nat) : Prop :=
  e.1 < L.threads ∧
  (∃ count pc, X.IsBarArrival e (key % 16) count pc) ∧
  CtaBarrier.GenerationOf L.block (X.barriers (e.1 / L.block))
    e (key % 16) (key / 16)

/-- `e` is a `bar.sync` arrival at instance `key`: `key % 16` is the barrier ID; `key / 16` is its
actual resource generation. -/
def CtaBarK (L : Launch) (X : Execution) (e : EvId) (key : Nat) : Prop :=
  e.1 < L.threads ∧
  (∃ count pc, X.IsBarrier e (key % 16) count pc) ∧
  CtaBarrier.GenerationOf L.block (X.barriers (e.1 / L.block))
    e (key % 16) (key / 16)

/-- The generation of instance `key` of the barrier resources of CTA `cta` has completed. -/
def CtaBarDone (L : Launch) (X : Execution) (cta key : Nat) : Prop :=
  CtaBarrier.Released L.block (X.barriers cta) (key % 16) (key / 16)

/-- Generic memory synchronization through two actual arrivals in one named phase: an
arrival of either form after `e`, and a `bar.sync` arrival before `f`. -/
def CtaBarSync (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  SameCta L e.1 f.1 ∧ ∃ key i j,
    CtaBarArrivalK L X (e.1, i) key ∧ CtaBarK L X (f.1, j) key ∧
    e.2 < i ∧ j < f.2 ∧ f.2 < (X.tr f.1).length

/-! ## ERR-CTA-BARRIER — an arrival the CTA barrier resource cannot perform

Statement: An execution is unsafe when a warp arrives at a CTA barrier with a count that differs
  from the open generation's, or arrives twice in one generation.

Defs: CtaBarFault

Source:
- §9.7.15.1: "Different warps may execute different forms of the barrier{.cta} instruction using the
    same barrier name and thread count."
- §9.7.15.1: "Care must be taken to keep a warp from executing more barrier{.cta} instructions than
    intended ( barrier{.cta}.arrive followed by any other barrier{.cta} instruction to the same
    barrier) prior to the reset of the barrier."
- OBJ-CTA-BARRIER-SYNC

Direction: stricter

Applies: CTA barrier arrival events of both forms (`bar.sync`, `bar.arrive`) that are not in the
  history of their CTA

Premises: The recorded history of the CTA is accepted by its barrier resources, and the arrival's
  lanes execute the matching instruction with the recorded operands (`CtaBarSources`).

Effect: Safety rejection (part of Unsafe). An issued collective arrival that the resource cannot
  perform (`CtaBarrier.Error.isFault`) is not removed from the possible executions: its lanes stay
  at the barrier, unrecorded, and `CtaBarFault` rejects the execution. The faulting arrival is
  outside the history, which records every operation the resource performed before it. This
  covers an arrival whose count differs from the open generation's, whatever the forms (`bar.arrive
  1, 64` meeting `bar.sync 1, 128`), and a warp that arrives twice in one generation (`bar.arrive`
  followed by another `barrier{.cta}` instruction on the same barrier before it completes, the case
  §9.7.15.1 warns about).
-/

/-- Some warp has issued an arrival that is not in the history and that the resource cannot
perform after the recorded history, because of a count mismatch or a second arrival in one
generation. -/
def CtaBarFault (L : Launch) (X : Execution) : Prop :=
  ∃ c < L.grid, ∃ s, CtaBarrier.run L.block {} (X.barriers c) = .ok s ∧
    ∃ id warp count lanes err,
      CtaBarSources L X c (.arrival id warp count lanes) ∧
      (∀ p ∈ lanes, p.2 ∉ (X.barriers c).flatMap CtaBarrier.Record.refs) ∧
      CtaBarrier.Record.perform L.block s (.arrival id warp count lanes) = .error err ∧
      err.isFault

end PTX
