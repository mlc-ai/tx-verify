-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairHistory
public import Core.Sync.Barrier
public import Core.Sync.Shuffle
public import Core.Sync.Elect
public import Core.Sync.WarpBarrier
public import Core.Thread.SetMaxNReg
public import Core.MBarrier.AsyncMBarrier

@[expose] public section

/-!
# Stage order and group-wait coverage

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## DEP-ASYNC-STAGE-ORDER — the stages of an asynchronous operation
Statement: The stages of one asynchronous operation follow its issue and each other as listed under
  Effect, and one table lists the stages that complete each operation.

Defs: StageEdge, StageOrder, IssueStage, AsyncCopy.FinalStage

Source:
- §9.7.10.28 (copy stages)
- §9.7.15.16.18 (cp.async.mbarrier.arrive triggers its arrive-on upon completion of the prior
    cp.async operations)
- §9.7.18.12.1 (tcgen05.commit arrives on completion)
- §9.7.15.18
- §9.7.10.28.1: "Asynchronous operations may be tracked by either of the completion mechanisms or
    both mechanisms. The tracking mechanism is instruction/instruction-variant specific."
- EXT-STAGE-ORDER

Direction: reading

Applies: The stages of asynchronous copies, stores, MMAs, commits and CLC requests

Premises: Every edge relates stages that are present.

Effect: `StageOrder` is shared by both layers: it is part of `stageCausality`
  (MEM-OBJECT-ORDER-CAUSALITY) and of the dependency order (`DepStep`, DEP-ORDER). `IssueStage`
  belongs to the dependency order only. The issue precedes every stage except a notification, a bulk
  store's full completion, an MMA's completion and the arrive-on of a `cp.async.mbarrier.arrive`,
  which follow other stages of their operation (`IssueStage`). The read of a slot precedes its
  write, and the write of a slot precedes the notification that signals it (`Part.target`). CLC
  resolution precedes each response write. A store's reads precede its read completion, its writes
  and old-value reads precede its full completion, and its read completion precedes its full
  completion. MMA operand reads precede the MMA completion, and a tracked MMA completion precedes
  its commit notification. The write of a tracked `cp.async` precedes the arrive-on of
  `cp.async.mbarrier.arrive`. The source read of an element-wise linear operation precedes each
  element write, and each element write and old-value read precedes its `.write .copy` stage, which
  marks its completion. `FinalStage` is the one table of the stages that complete an operation, by
  its completion mechanism (§9.7.10.28.1): the notification of a linear copy completed through an
  mbarrier, the write of any other linear copy, the arrive-on of `cp.async.mbarrier.arrive`, the
  completion of `tcgen05.mma` and `tcgen05.cp`, the notification at each target of a CLC request,
  the notification of a tensor load, the full completion of a tensor store, and the arrive-on at
  each target of `tcgen05.commit`. `AsyncDrained` (CORRECT-COMPLETE) and `SharedUse`
  (ERR-SHARED-LIFETIME) read it.

Review: Thread returns and independent asynchronous stages are distinct nodes. A bulk issue may
  return before its copy reads, writes or notifies; no edge forces those effects to precede the
  issuing thread's next event. Output copies track per-byte reads and writes plus separate read and
  full completion points; a reduction's read of an old destination byte follows its issue and
  precedes full completion, as its writes do. A write may follow the issue directly (a tensor load's
  out-of-bounds fill needs no source read). Tensor dependencies match the exact issue and byte
  slot; distinct slots are not ordered. MMA notifications follow the actual tracked MMAs. The group
  waits are not stage edges: what a wait returns after is its need (DEP-ORDER), stated once
  in `GroupWaitStages` (DEP-BULK-WAIT).
-/

/-- The order of the stages inside one asynchronous operation, from the completion of a stage to
the start of the next: every edge relates two present stages. -/
def StageEdge (X : Execution) : AsyncCopy.Ref → AsyncCopy.Ref → Prop
  | .async i (.read .copy), .async j (.write (.elem k)) =>
    i = j ∧ X.AsyncPresent i (.read .copy) ∧ X.AsyncPresent j (.write (.elem k))
  | .async i (.write (.elem k)), .async j (.write .copy) =>
    i = j ∧ X.AsyncPresent i (.write (.elem k)) ∧ X.AsyncPresent j (.write .copy)
  | .async i (.old (.elem k)), .async j (.write .copy) =>
    i = j ∧ X.AsyncPresent i (.old (.elem k)) ∧ X.AsyncPresent j (.write .copy)
  | .async i (.read s), .async j (.write s') =>
    i = j ∧ s = s' ∧ X.AsyncPresent i (.read s) ∧ X.AsyncPresent j (.write s')
  | .async i (.write s), .async j (.notify t) =>
    i = j ∧ (AsyncCopy.Part.write s).target = some t ∧ X.AsyncPresent i (.write s) ∧
      X.AsyncPresent j (.notify t)
  | .async i .resolve, .async j (.write (.cta c)) =>
    i = j ∧ X.AsyncPresent i .resolve ∧ X.AsyncPresent j (.write (.cta c))
  | .async i (.read (.store x y k)), .async j .readsDone =>
    i = j ∧ X.AsyncPresent i (.read (.store x y k)) ∧ X.AsyncPresent j .readsDone
  | .async i (.write (.store x y k)), .async j .fullDone =>
    i = j ∧ X.AsyncPresent i (.write (.store x y k)) ∧ X.AsyncPresent j .fullDone
  | .async i (.old s), .async j .fullDone =>
    i = j ∧ X.AsyncPresent i (.old s) ∧ X.AsyncPresent j .fullDone
  | .async i .readsDone, .async j .fullDone =>
    i = j ∧ X.AsyncPresent i .readsDone ∧ X.AsyncPresent j .fullDone
  | .async i (.mmaRead b k), .async j .mmaDone =>
    i = j ∧ X.AsyncPresent i (.mmaRead b k) ∧ X.AsyncPresent j .mmaDone
  | .async i .mmaDone, .async j (.tcNotify rank) =>
    AsyncCopy.TracksMma X i j ∧ X.AsyncPresent i .mmaDone ∧ X.AsyncPresent j (.tcNotify rank)
  | .async i (.write .copy), .async j .arriveOn =>
    AsyncCopy.TracksCpAsync X i j ∧ X.AsyncPresent i (.write .copy) ∧ X.AsyncPresent j .arriveOn
  | _, _ => False

/-- The stage order on nodes, shared by both layers: the two points (issue, completion) of one
present node, and the completion of a stage before the start of the next stage of its
operation. It never starts at a thread instruction's completion or ends at a thread
instruction's issue. -/
def StageOrder (X : Execution) : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | (e, b), (f, b') =>
    (e = f ∧ b = false ∧ b' = true ∧ X.RefPresent e) ∨
    (b = true ∧ b' = false ∧ StageEdge X e f)

/-- The issue of a thread instruction before a stage of its own asynchronous operation (execution
layer only): every stage except a notification, a bulk store's full completion, an MMA's
completion and an arrive-on, which follow other stages of their operation. -/
def IssueStage (X : Execution) : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop
  | (e, b), (f, b') =>
    b = false ∧ b' = false ∧ ∃ i p, e = .thread i ∧ f = .async i p ∧ X.RefPresent e ∧
      X.AsyncPresent i p ∧
      match p with
      | .notify _ | .fullDone | .mmaDone | .arriveOn => False
      | _ => True

/-- `p` is a stage that completes the asynchronous operation issued by `i`, by its completion
mechanism (the table of DEP-ASYNC-STAGE-ORDER). -/
def AsyncCopy.FinalStage (X : Execution) (i : EvId) (p : AsyncCopy.Part) : Prop :=
  (∃ s m, X.Copy i s ∧ s.completion = .mbarrier m ∧ p = .notify .copy) ∨
  (∃ s, X.Copy i s ∧ (∀ m, s.completion ≠ .mbarrier m) ∧ p = .write .copy) ∨
  (∃ m noinc, X.AsyncArrive i m noinc ∧ p = .arriveOn) ∨
  (X.TcAsync i ∧ p = .mmaDone) ∨
  (∃ s targets c, X.ClcIssue i s targets ∧ c ∈ targets ∧ p = .notify (.cta c)) ∨
  (∃ a s, X.TensorIssue i a s ∧ p = .notify .load) ∨
  (∃ a s, X.TensorStoreIssue i a s ∧ p = .fullDone) ∨
  ∃ s rank m, X.Commit i s ∧ TcCommit.target s rank = some m ∧ p = .tcNotify rank

end

end PTX
