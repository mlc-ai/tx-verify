-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncChain
public import Lemmas.Order.OrderBaseCausality
public import Lemmas.Order.OrderWaits
public import Lemmas.Order.GuardOrder
public import Lemmas.Async.AsyncCopy
public import Lemmas.Execution.MemoryPresence
public import Lemmas.Execution.EffectValidity
public import Lemmas.Order.WaitOrderWaits

@[expose] public section

namespace PTX
noncomputable section
open AsyncCopy

section
variable {L : Launch} {X : Execution}

/-- The completion of a stage of an asynchronous operation precedes the start of the next stage:
`StageEdge`, the stage-order disjunct of `Waits`. A stage is reached from its issue point only
through `StageOrder` and `IssueStage`; no `Waits` edge leaves a thread instruction's return for one
of its own stages. -/
theorem waits_async {e f : Ref} (h : StageEdge X e f) :
    Waits L X (e, true) (f, false) :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl, h⟩⟩)))))

/-- Two records of one mbarrier: the earlier record's return precedes the later one's return. -/
theorem waits_object {e f : Ref} {m : Loc} (h : MBarrier.Before (X.objects m) e f) :
    Waits L X (e, true) (f, true) :=
  Waits.before h

-- moved to WaitsStageLegacy: `copy_write_waits`, `async_step`, `scalarIssuePart`,
-- `async_issue_waits` and `async_memory_issue_waits` start at `(.thread i, true)`, but an
-- instruction's issue point is the `false` component: `IssueStage` enters a stage at
-- `false → false`, so no `Waits` edge leaves a thread return for a stage of its own operation.
-- moved to WaitsStageLegacy: `bulk_wait_present`, `tensor_write_waits`, `async_finished_waits` and
-- `async_only_finished_waits` conclude at `(.async i p, true)` from a stage or from a group wait
-- whose stages are reached at `false`; the `true → true` chain they need has no `Waits` path.

/-- MMA completion reaches a successful wait via the actual commit notification. -/
theorem mma_done_waits (hc : CommitOk X) {i w : EvId} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved X i .mmaDone w acq ws) : X.async.mmaDone i = true ∧
      Relation.TransGen (Waits L X) (.async i .mmaDone, true) (.thread w, true) := by
  obtain ⟨n, m, ⟨c, s, rank, hn, htrack, -, -, hrank⟩, hwo⟩ := h
  subst hn
  have hd := (hc c rank hrank).2 i htrack
  have hn' : X.AsyncPresent c (.tcNotify rank) := hrank
  exact ⟨hd, ((Relation.TransGen.single (waits_async (e := .async i .mmaDone)
      (f := .async c (.tcNotify rank)) ⟨htrack, hd, hn'⟩)).tail
    (Waits.node (e := .async c (.tcNotify rank)) hn')).tail
    (Waits.before (before_of_update hwo.2))⟩

-- moved to WaitsStageLegacy: `AsyncBefore.waits`, `AsyncChain.waits`, `modelCausality.waits`,
-- `modelCausality_asymm` and `writes_vis_asymm` are the `true → true` composition forms and the
-- asymmetry they support; asymmetry rests on `modelCausality_asymm_guarded`, which lives in
-- `Lemmas.Order.GuardObserver`; that module still names the deleted `Observed`, `AsyncWaits`,
-- `Rendezvous` and `Enables.observed`, so the statement has no proof in the tree today.

end
end
end PTX
