-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX
noncomputable section

/-! ## OBJ-BULK-GROUP-TRACE — bulk groups of actual thread instruction instances
Statement: The groups that a wait covers are computed from the waiting thread's own trace before
  the wait: its operations of the wait's kind, its commits of that kind, and the wait's own mode and
  operand. A bulk wait covers the tensor stores and `.bulk_group` linear copies of the groups it
  observes, and a `cp.async` wait covers the `cp.async` operations of the groups it observes; each
  operation keeps the position of its issue in the trace.

Defs: bulkAction, bulkActions, bulkStateBefore, BulkWaitsFor, asyncAction, asyncActions,
  asyncStateBefore, AsyncGroupWaitsFor, issue_mem_actions, issue_of_waitsFor,
  not_bulkWaitsFor_of_copy, not_asyncGroupWaitsFor_of_copy

Source:
- §9.7.10.28.6.1–2 (per-thread grouping and waits)
- §9.7.10.28.3.2–3 (cp.async-groups)
- §9.7.10.28.1.1: "The thread issuing the asynchronous operation must create separate async-groups
    for bulk and non-bulk asynchronous operations."

Direction: reading

Applies: Tensor stores and linear copies with bulk-group completion, bulk commit/wait events,
  `cp.async` copies and `cp.async` commit/wait events

Premises: The actual source-thread prefix contains the issues and commits. Wait mode and
  remaining-group operand come from its event.

Effect: The execution adapter for group membership. A `cp.async.wait_all` is a commit event
  followed by a wait event leaving no group (THREAD-CP-ASYNC), so it covers every `cp.async` of the
  thread before it.
-/
/-- The bulk-group action of the instruction of kind `k` at trace position `index` of thread `g`: a
tensor store is an issue named by its event identity, `commit_group` and `wait_group` are their
actions, and other instructions have no action. -/
def bulkAction (g index : Nat) : Kind → Option (BulkGroup.Action EvId)
  | .tensorStore .. => some (.issue (g, index))
  | .copy s => if s.completion = .bulkGroup then some (.issue (g, index)) else none
  | .bulkCommit => some .commit
  | .bulkWait mode n => some (.wait mode n)
  | _ => none

/-- The bulk-group actions of a thread's trace, in order. -/
def bulkActions (g : Nat) (trace : List Event) : List (BulkGroup.Action EvId) :=
  trace.zipIdx.filterMap fun (event, index) => bulkAction g index event.kind

/-- The grouping state of the waiter's thread just before the wait: the run of the actions of the
trace prefix that precedes it. -/
def bulkStateBefore (X : Execution) (waiter : EvId) : BulkGroup.State EvId :=
  BulkGroup.run (bulkActions waiter.1 ((X.tr waiter.1).take waiter.2))

/-- The bulk operation `operation` is covered by the wait event `waiter` of mode `mode`: it belongs
to a group that the wait observes in the state before it. -/
def BulkWaitsFor (X : Execution) (mode : BulkGroup.WaitMode) (operation waiter : EvId) : Prop :=
  ∃ pc remaining, X.get waiter = some ⟨pc, .bulkWait mode remaining⟩ ∧
    BulkGroup.Observes (bulkStateBefore X waiter) remaining operation

/-- The `cp.async`-group action of the instruction of kind `k` at trace position `index` of thread
`g`: a `cp.async` is an issue, `cp.async.commit_group` and `cp.async.wait_group` are their actions
(a full wait), and other instructions have no action. -/
def asyncAction (g index : Nat) : Kind → Option (BulkGroup.Action EvId)
  | .copy s => if s.completion = .asyncGroup then some (.issue (g, index)) else none
  | .asyncCommit => some .commit
  | .asyncWait n => some (.wait .full n)
  | _ => none

/-- The `cp.async`-group actions of a thread's trace, in order. -/
def asyncActions (g : Nat) (trace : List Event) : List (BulkGroup.Action EvId) :=
  trace.zipIdx.filterMap fun (event, index) => asyncAction g index event.kind

/-- The `cp.async`-group state of the waiter's thread just before the wait. -/
def asyncStateBefore (X : Execution) (waiter : EvId) : BulkGroup.State EvId :=
  BulkGroup.run (asyncActions waiter.1 ((X.tr waiter.1).take waiter.2))

/-- The `cp.async` operation `operation` is covered by the `cp.async.wait_group` event `waiter`: it
belongs to a group that the wait observes in the state before it. -/
def AsyncGroupWaitsFor (X : Execution) (operation waiter : EvId) : Prop :=
  ∃ pc remaining, X.get waiter = some ⟨pc, .asyncWait remaining⟩ ∧
    BulkGroup.Observes (asyncStateBefore X waiter) remaining operation

/-- An issue action of the per-thread action list names the event at its position, when every
issue the action function produces names its own position. -/
theorem issue_mem_actions {act : Nat → Nat → Kind → Option (BulkGroup.Action EvId)}
    (hact : ∀ g index k i, act g index k = some (.issue i) → i = (g, index))
    {g : Nat} {tr : List Event} {i : EvId}
    (h : BulkGroup.Action.issue i ∈
      tr.zipIdx.filterMap fun (event, index) => act g index event.kind) :
    i.1 = g ∧ ∃ ev, tr[i.2]? = some ev ∧ act g i.2 ev.kind = some (.issue i) := by
  obtain ⟨⟨ev, idx⟩, hm, hk⟩ := List.mem_filterMap.mp h
  have hi := hact _ _ _ _ hk
  subst hi
  refine ⟨rfl, ev, ?_, hk⟩
  rw [List.mem_zipIdx_iff_getElem?] at hm
  simpa using hm

/-- An operation that a group wait observes is an event of the execution whose group action is its
issue. -/
theorem issue_of_waitsFor {act : Nat → Nat → Kind → Option (BulkGroup.Action EvId)}
    (hact : ∀ g index k i, act g index k = some (.issue i) → i = (g, index))
    {X : Execution} {w i : EvId} {remaining : Nat}
    (h : BulkGroup.Observes (BulkGroup.run ((((X.tr w.1).take w.2).zipIdx).filterMap
      fun (event, index) => act w.1 index event.kind)) remaining i) :
    ∃ ev, X.get i = some ev ∧ act i.1 i.2 ev.kind = some (.issue i) := by
  obtain ⟨h1, ev, hev, hk⟩ := issue_mem_actions hact (BulkGroup.issue_of_observes h)
  refine ⟨ev, ?_, h1 ▸ hk⟩
  rw [List.getElem?_take] at hev
  split at hev
  · simpa [Execution.get, h1] using hev
  · cases hev

/-- A linear copy that is not completed through a bulk group is covered by no bulk wait. -/
theorem not_bulkWaitsFor_of_copy {X : Execution} {i w : EvId} {s : AsyncCopy.Spec}
    {mode : BulkGroup.WaitMode} (hc : X.Copy i s) (hs : s.completion ≠ .bulkGroup) :
    ¬ BulkWaitsFor X mode i w := by
  rintro ⟨pc, remaining, -, hobs⟩
  obtain ⟨ev, hev, hk⟩ := issue_of_waitsFor (act := bulkAction) (fun g index k i h => by
    unfold bulkAction at h
    split at h <;> grind) hobs
  obtain ⟨pc', hc'⟩ := hc
  rw [hc'] at hev
  cases hev
  simp [bulkAction, hs] at hk

/-- A linear copy that is not a `cp.async` is covered by no `cp.async` wait. -/
theorem not_asyncGroupWaitsFor_of_copy {X : Execution} {i w : EvId} {s : AsyncCopy.Spec}
    (hc : X.Copy i s) (hs : s.completion ≠ .asyncGroup) : ¬ AsyncGroupWaitsFor X i w := by
  rintro ⟨pc, remaining, -, hobs⟩
  obtain ⟨ev, hev, hk⟩ := issue_of_waitsFor (act := asyncAction) (fun g index k i h => by
    unfold asyncAction at h
    split at h <;> grind) hobs
  obtain ⟨pc', hc'⟩ := hc
  rw [hc'] at hev
  cases hev
  simp [asyncAction, hs] at hk

/-! ## ERR-CP-ASYNC-OVERLAP — overlapping cp.async destinations in one group
Statement: An execution is unsafe when two `cp.async` operations of one thread that belong to the
  same cp.async-group (no commit of the thread lies between them) have overlapping destinations,
  whatever bytes they write.

Defs: SameAsyncGroup, CpAsyncOverlap, not_cpAsyncOverlap_of_none

Source:
- §9.7.10.28.3.2: "There is no memory ordering guarantee provided between any two cp.async
    operations within the same cp.async-group . So two or more cp.async operations within a
    cp.async-group copying data to the same location results in undefined behavior."

Direction: equal

Applies: Every pair of distinct `cp.async` issues of one thread with no `cp.async.commit_group` (or
  the commit of a `cp.async.wait_all`) between them

Premises: Their destination footprints overlap at a byte.

Effect: Safety rejection (ERR-OBJECT-LIFETIME, `TmaUnsafe`), with no exemption for writes of the
  same value (unlike ERR-DATA-RACE's `SameValueWrites`). Two `cp.async` operations of one thread
  before and after a commit are in different groups; their destinations may overlap, and the race
  check (ERR-DATA-RACE) orders them only through a wait.
-/
/-- The `cp.async` operations issued by `i` and `j` belong to the same cp.async-group: one thread
issues both, `i` first, and no commit event of the thread lies between them. -/
def SameAsyncGroup (X : Execution) (i j : EvId) : Prop :=
  (∃ s, X.Copy i s ∧ s.completion = .asyncGroup) ∧
  (∃ s, X.Copy j s ∧ s.completion = .asyncGroup) ∧ i.1 = j.1 ∧ i.2 < j.2 ∧
  ∀ k pc, i.2 < k → k < j.2 → X.get (i.1, k) ≠ some ⟨pc, .asyncCommit⟩

/-- Two `cp.async` operations of one cp.async-group copy to an overlapping location. -/
def CpAsyncOverlap (X : Execution) : Prop :=
  ∃ i j s s', SameAsyncGroup X i j ∧ X.Copy i s ∧ X.Copy j s' ∧ s.dst.Overlap s'.dst

/-- An execution without `cp.async` has no overlapping `cp.async` group. -/
theorem not_cpAsyncOverlap_of_none {X : Execution}
    (h : ∀ i s, X.Copy i s → s.completion ≠ .asyncGroup) : ¬ CpAsyncOverlap X :=
  fun ⟨i, _, _, _, ⟨⟨s, hc, hs⟩, _⟩, _⟩ => h i s hc hs

/-! ## ERR-BULK-MASK-RANGE — the destination range of a masked bulk copy

Statement: An execution is unsafe when the destination range of a `.cp_mask` bulk copy covers a
  byte that is not allocated at launch, whichever bytes its mask selects.

Defs: MaskedRangeUnalloc, not_maskedRangeUnalloc_of_none

Source:
- §9.7.10.28.4.1: "The memory range [dstMem, dstMem + size - 1] must not overflow the destination
  memory space and the memory range [srcMem, srcMem + size - 1] must not overflow the source
  memory space. Otherwise, the behavior is undefined."
- §9.7.10.28.4.1: "The i-th bit in the 16-bit wide byteMask operand specifies whether the i-th
  byte of each 16-byte wide chunk of source data is copied to the destination."

Direction: stricter

Applies: Every linear copy whose writes are `WriteMode.masked` (THREAD-TMA), at issue, pending or
  completed.

Premises: A byte of the copy's whole destination range `[dstMem, dstMem + size - 1]` is
  unallocated in the launch memory.

Effect: Safety rejection (ERR-OBJECT-LIFETIME, `TmaUnsafe`). The footprint of a masked copy's write
  covers only the bytes its mask selects, so ERR-UNALLOCATED-ACCESS sees no other byte of the range;
  this check covers the rest. Its source range is a read footprint, which ERR-UNALLOCATED-ACCESS
  checks. THREAD-TMA bounds both ranges by the address range of their spaces (`bulkRangeOk`); this
  check rejects a destination range that reaches past the bytes allocated at launch. A range over an
  unallocated gap inside the space is rejected as well, which is stricter than the text.
-/
/-- The whole destination range of a `.cp_mask` copy covers a byte that is unallocated in `mem0`. -/
def MaskedRangeUnalloc (mem0 : Mem0) (X : Execution) : Prop :=
  ∃ i s m l, X.Copy i s ∧ s.writes = .masked m ∧ s.dst.Covers l ∧ mem0 l = none

/-- An execution without `.cp_mask` copies has no masked range to check. -/
theorem not_maskedRangeUnalloc_of_none {mem0 : Mem0} {X : Execution}
    (h : ∀ i s m, X.Copy i s → s.writes ≠ .masked m) : ¬ MaskedRangeUnalloc mem0 X :=
  fun ⟨i, s, m, _, hc, hw, _⟩ => h i s m hc hw

/-! ## DEP-BULK-WAIT — actual output effects and what a group wait covers
Statement: Every recorded tensor store belongs to an actual issue with a valid specification and
  obeys the store's effect rules. A group wait covers the operations of the groups it waits for,
  and one table gives, for each covered operation, the stages the wait waits for and the stages
  whose memory effects it makes visible to the waiting thread.

Defs: TensorStoreOk, GroupWait, GroupWaitsFor, GroupWaitStages, GroupWaitVisible

Source:
- §9.7.10.28.5.3 (tensor output effects)
- §9.7.10.28.6.2: "The optional .read modifier indicates that the waiting has to be done until all
    the bulk async operations in the specified bulk async-group have completed: reading from the
    tensormap the reading from their source locations."
- §9.7.10.28.6.2 (wait completion; writes being made visible to the executing thread)
- §9.7.10.28.3.3 (cp.async.wait_group): "all the prior cp.async-group s committed by the executing
    threads are complete"

Direction: reading

Applies: Output tensor observation records, bulk-group wait events and `cp.async` wait events

Premises: Each output record names its actual issue and immutable specification; each wait covers
  the groups from its thread prefix.

Effect: `Consistent.store`. The table gives the needs of the group waits (`KindNeeds`,
  DEP-ORDER: a wait returns only after the stages it waits for), the generic visibility of
  `AsyncFinished` and `AsyncOnlyFinished` (MEM-OBSERVED-COMPLETION) and the observations of
  `SyncObserved` (MEM-OBJECT-ORDER-CAUSALITY). By wait and covered operation:
  - `.read` wait, tensor store: waits for `.readsDone`; makes the source reads visible
  - `.read` wait, linear copy: waits for `.read .copy`; makes the source read visible
  - `.full` wait, tensor store: waits for `.readsDone` and `.fullDone`; makes the reads, writes and
    old-value reads visible
  - `.full` wait, linear copy: waits for `.read .copy` and `.write .copy`; makes the read, the write
    and the element writes and old-value reads visible
  - `.asyncProxy` wait: waits as a `.full` wait; makes nothing visible to generic accesses
  - `cp.async.wait_group`, `cp.async`: waits for `.read .copy` and `.write .copy`; makes the read
    and the write visible
  A linear copy has one read stage and one write stage (DEP-LINEAR-COPY-EFFECTS), so its reads are
  finished when its read is present and it is complete when its write is present.
-/
/-- Every recorded tensor store observation of `X` is the effect of an actual store issue, has a
valid specification and obeys the effect rules of a tensor store. -/
def TensorStoreOk (L : Launch) (X : Execution) : Prop :=
  ∀ i observation, X.tensorStores i = some observation →
    (∃ address, X.TensorStoreIssue i address observation.spec) ∧
    TensorStore.Valid (i.1 / L.block) observation.spec ∧
    TensorStore.CopyOk observation.spec observation.effects

/-- A group wait: `cp.async.bulk.wait_group` with its mode, or `cp.async.wait_group`. -/
inductive GroupWait where
  | bulk (mode : BulkGroup.WaitMode)
  | cpAsync
  deriving DecidableEq, Repr

/-- The group wait `w` of kind `k` covers the operation issued by `i`: `i` belongs to a group the
wait waits for. -/
def GroupWaitsFor (X : Execution) : GroupWait → EvId → EvId → Prop
  | .bulk mode, i, w => BulkWaitsFor X mode i w
  | .cpAsync, i, w => AsyncGroupWaitsFor X i w

/-- The stages of the operation issued by `i` that a group wait of kind `k` covering it waits for:
the read completion of a tensor store or the read of a linear copy for a `.read` wait, and both
completions otherwise. -/
def GroupWaitStages (X : Execution) (i : EvId) (k : GroupWait) : List AsyncCopy.Part :=
  match (X.get i).map Event.kind, k with
  | some (.tensorStore ..), .bulk .read => [.readsDone]
  | some (.tensorStore ..), _ => [.readsDone, .fullDone]
  | _, .bulk .read => [.read .copy]
  | _, _ => [.read .copy, .write .copy]

/-- The parts of a covered operation whose memory effects a group wait of kind `k` makes visible
to generic accesses of the waiting thread and its causal successors. -/
def GroupWaitVisible : GroupWait → AsyncCopy.Part → Bool
  | .bulk .read, .read (.store ..) | .bulk .read, .read .copy => true
  | .bulk .full, .read (.store ..) | .bulk .full, .write (.store ..)
  | .bulk .full, .old (.store ..) | .bulk .full, .read .copy | .bulk .full, .write .copy
  | .bulk .full, .write (.elem _) | .bulk .full, .old (.elem _) => true
  | .cpAsync, .read .copy | .cpAsync, .write .copy | .cpAsync, .write (.elem _)
  | .cpAsync, .old (.elem _) => true
  | _, _ => false

end
end PTX
