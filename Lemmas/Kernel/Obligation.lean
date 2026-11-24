-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The obligations of an incomplete execution

An execution that is not complete has an obligation (`cover`): a thread that has neither exited
nor been canceled, an issued asynchronous operation not finished (a linear copy, a
`cp.async.mbarrier.arrive`'s arrive-on, a Tensor Core operation, a CLC request's notification, a
tensor copy or store, a commit's notification), a paired Tensor Memory request not drained: the
conjuncts of `asyncDrained_iff`. A kernel's progress argument discharges each by extending a
maximal execution or by passing to an obligation of smaller rank (`Descent.Steps`,
`Descent.progress_of_steps`). -/

namespace PTX.Descent

open PTX

/-- An obligation of an incomplete execution. -/
inductive Obligation where
  | thread (g : Nat)
  | bulk | arriveOn | mma | clc | tensor | store | commit
  | tmem

/-- Whether an obligation is open in an execution. -/
def Obl (L : Launch) (X : Execution) : Obligation → Prop
  | .thread g => Frame.Pending L X g
  | .bulk => ¬ ∀ i s, X.Copy i s → match s.completion with
      | .mbarrier _ => (X.async.copies i).notified = true
      | _ => (X.async.copies i).writeBytes.isSome
  | .arriveOn => ¬ ∀ i m noinc, X.AsyncArrive i m noinc → X.async.arrived i = true
  | .mma => ¬ ∀ i, X.TcAsync i → X.async.mmaDone i = true
  | .clc => ¬ ∀ i s targets, X.ClcIssue i s targets → ∀ c ∈ targets, c ∈ (X.clc i).notified
  | .tensor => ¬ ∀ i mapAddress s, X.TensorIssue i mapAddress s →
      ∃ observation, X.tensor i = some observation ∧ observation.effects.notified = true
  | .store => ¬ ∀ i mapAddress s, X.TensorStoreIssue i mapAddress s →
      ∃ observation, X.tensorStores i = some observation ∧ observation.effects.fullDone = true
  | .commit => ¬ ∀ i s rank m, X.Commit i s → TcCommit.target s rank = some m →
      rank ∈ X.tcNotified i
  | .tmem => ¬ Tmem.Pair.Drained L X

/-- An execution that is not complete has an open obligation. -/
theorem cover {L : Launch} {X : Execution} (h : ¬ Complete L X) : ∃ o, Obl L X o := by
  classical
  by_contra hno
  push Not at hno
  apply h
  refine ⟨fun g hg => ?_, (asyncDrained_iff X).mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := hno (.thread g)
    simp only [Obl, Frame.Pending, not_and, not_forall, not_not] at this
    by_cases hc : ClcCanceled L X g
    · exact .inl hc
    · obtain ⟨pc, hpc⟩ := this hg hc
      exact .inr ⟨pc, hpc⟩
  all_goals first
    | (have := hno .bulk; simp only [Obl, not_not] at this; exact this)
    | (have := hno .arriveOn; simp only [Obl, not_not] at this; exact this)
    | (have := hno .mma; simp only [Obl, not_not] at this; exact this)
    | (have := hno .clc; simp only [Obl, not_not] at this; exact this)
    | (have := hno .tensor; simp only [Obl, not_not] at this; exact this)
    | (have := hno .store; simp only [Obl, not_not] at this; exact this)
    | (have := hno .commit; simp only [Obl, not_not] at this; exact this)
    | (have := hno .tmem; simp only [Obl, not_not] at this; exact this)

end PTX.Descent
