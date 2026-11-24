-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedRescaleInputs
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof

/-- The saved successful Bias wait is reached from launch along its exact recorded prefix. -/
theorem ObservedBiasedRescaleInputs.beforePrefix {p : Params} {l : Launch} {X : Execution}
    {g pos : Nat} (entry : ObservedBiasedRescaleInputs p l X g pos) :
    TraceReach kernel Assumptions.all l g {} ((X.tr g).take entry.biasWait) entry.before := by
  have hSplit : (X.tr g).take entry.biasWait = (X.tr g).take entry.roleEntry ++
      ((X.tr g).drop entry.roleEntry).take (entry.biasWait-entry.roleEntry) := by
    conv_lhs => rw [← List.take_append_drop entry.roleEntry ((X.tr g).take entry.biasWait)]
    rw [List.take_take,Nat.min_eq_left entry.roleBefore,List.drop_take]
  rw [hSplit]
  exact entry.rolePrefix.append entry.beforePath

/-- The recorded Bias wait is the head of the continuation from its observed state. -/
theorem ObservedBiasedRescaleInputs.beforeRun {p : Params} {l : Launch} {X : Execution}
    {g pos : Nat} (entry : ObservedBiasedRescaleInputs p l X g pos) :
    Run kernel Assumptions.all l g entry.before ((X.tr g).drop entry.biasWait) entry.ending := by
  obtain ⟨s,hPrefix,hLocal⟩ := entry.beforePath.returnedPrefix
  let events := (X.tr g).drop entry.roleEntry
  let offset := entry.biasWait-entry.roleEntry
  have hSuffix : events.drop offset = (X.tr g).drop entry.biasWait := by
    rw [List.drop_drop,Nat.add_sub_of_le entry.roleBefore]
  have hWhole : events = events.take offset ++ (X.tr g).drop entry.biasWait := by
    rw [← hSuffix,List.take_append_drop]
  have hOrigin : Run kernel Assumptions.all l g entry.roleSeed events entry.ending := entry.roleRun
  rw [hWhole] at hOrigin
  have hRun := hPrefix.after_returned_prefix hOrigin
  obtain ⟨_,hWait⟩ := entry.waitEvent
  have hMore : (X.tr g).drop entry.biasWait ≠ [] := by
    intro h
    exact (Nat.not_le_of_lt (len_of_get hWait)) (List.drop_eq_nil_iff.mp h)
  exact hRun.after_local_nonempty hLocal hMore


/-- The saved point is the source of the successful Bias wait at this visit. -/
theorem ObservedBiasedRescaleInputs.beforeEvent {p : Params} {l : Launch} {X : Execution}
    {g pos : Nat} (entry : ObservedBiasedRescaleInputs p l X g pos) :
    ∃ phase o, EStep kernel Assumptions.all l g entry.before
      ⟨5181,.wait (Softmax.waitLoc l g (Softmax.stageOf entry.warp) 5) phase true true .cta⟩ o ∧
      X.get (g,entry.biasWait) =
        some ⟨5181,
          .wait (Softmax.waitLoc l g (Softmax.stageOf entry.warp) 5) phase true true .cta⟩ := by
  obtain ⟨phase,hEvent⟩ := entry.waitEvent
  let e : Event :=
    ⟨5181,.wait (Softmax.waitLoc l g (Softmax.stageOf entry.warp) 5) phase true true .cta⟩
  have hHead : ((X.tr g).drop entry.biasWait)[0]? = some e := by
    rwa [List.getElem?_drop,Nat.add_zero]
  have reached {t : TState} (h : Relation.ReflTransGen
      (Tau kernel Assumptions.all l g) entry.before t) : t = entry.before := by
    rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_,hTau,_⟩
    · rfl
    · exact (not_tau_of_stops entry.beforeStops hTau).elim
  have hRun := entry.beforeRun
  generalize (X.tr g).drop entry.biasWait = events at hRun hHead
  generalize entry.ending = ending at hRun
  refine ⟨phase,?_⟩
  cases hRun with
  | nil => cases hHead
  | step hLocal hStep _ =>
    obtain rfl := reached hLocal
    obtain rfl := Option.some.inj hHead
    exact ⟨_,hStep,hEvent⟩
  | last hLocal hStep =>
    obtain rfl := reached hLocal
    obtain rfl := Option.some.inj hHead
    exact ⟨none,hStep,hEvent⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
