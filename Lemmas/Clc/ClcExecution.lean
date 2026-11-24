-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Lemmas.Clc.ClcEffects
public import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX
noncomputable section

/-- Observing a CLC notification entails the matching replica's actual response write. -/
theorem AsyncCopy.AsyncObserved.clc_completed {L : Launch} {X : Execution} (hc : ClcOk L X)
    {i w : EvId} {c : Nat} {acq : Bool} {ws : MbarScope}
    (ho : AsyncCopy.AsyncObserved X i (.notify (.cta c)) w acq ws) :
    ∃ a bs, X.MemWrites (.async i (.write (.cta c))) a bs ∧ a.size = 16 ∧
      ∃ r, (X.clc i).resolved = some r ∧ Clc.Result L i X.clcState r ∧
        bs = (Value.clc r).toBytes := by
  obtain ⟨s, ts, hi, hct, hn, _⟩ := ho.clc
  have he := (hc.2.2.2.1 i s ts hi).1
  obtain ⟨a, bs, hw, hsize, _⟩ := Clc.completion_has_write he
    (show Clc.Completion s (X.clc i) c { s.mbar with cta := c } 16 from ⟨hn, rfl, rfl⟩)
  have hmem : X.MemWrites (.async i (.write (.cta c))) a bs := ⟨s, ts, hi, hct, hw⟩
  obtain ⟨_, r, hr, _, hb⟩ := hw
  exact ⟨a, bs, hmem, hsize, r, hr, he.result r hr, hb⟩

/-- A task with any running thread cannot simultaneously be canceled. -/
theorem ClcOk.running_not_canceled {L : Launch} {X : Execution} (hc : ClcOk L X)
    (has : ∃ i s targets, X.ClcIssue i s targets) {g request : Nat}
    (hg : g < L.threads) (ht : X.tr g ≠ []) :
    X.clcState.owner (L.clusterOfCta (g / L.block)) ≠ some (.canceled request) := by
  rw [hc.2.2.2.2 has g hg ht]
  simp

/-- A canceled cluster is assigned to an actual issuing event, not a ghost owner. -/
theorem ClcOk.canceled_has_issue {L : Launch} {X : Execution} (hc : ClcOk L X)
    {task request : Nat} (ho : X.clcState.owner task = some (.canceled request)) :
    ∃ i s targets, request = Clc.requestId i ∧ X.ClcIssue i s targets ∧
      X.clcState.response (Clc.requestId i) = some (some task) := by
  have hr := Clc.canceled_has_response hc.1 task request ho
  obtain ⟨i, s, targets, hi, he⟩ := hc.2.1 request (some task) hr
  exact ⟨i, s, targets, hi, he, hi ▸ hr⟩

/-- The data write must exist before its completion notification, not merely its issue. -/
theorem ClcOk.notification_has_write {L : Launch} {X : Execution} (hc : ClcOk L X)
    {i : EvId} {c : Nat} (hn : c ∈ (X.clc i).notified) :
    ∃ a bs, X.MemWrites (.async i (.write (.cta c))) a bs := by
  obtain ⟨s, ts, hi⟩ := hc.2.2.1 i (.inr (.inr ⟨c, hn⟩))
  have he := (hc.2.2.2.1 i s ts hi).1
  have hw := he.notified c hn
  have ht := (hc.2.2.2.1 i s ts hi).2.2 c
  obtain ⟨a, bs, hb, _, _⟩ := Clc.completion_has_write he
    (show Clc.Completion s (X.clc i) c { s.mbar with cta := c } 16 from ⟨hn, rfl, rfl⟩)
  exact ⟨a, bs, s, ts, hi, ht.mpr (he.writes c hw).1, hb⟩

end
end PTX
