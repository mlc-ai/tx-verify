-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorReadSources
public import Lemmas.Async.AsyncChain

@[expose] public section

/-! # A tensor load whose write is ordered before an access has written its byte

The completion of a tensor load's write is the load's notification on its mbarrier, observed
by a wait (`AsyncFinished`, `Notifies`, `NotifyOn .load`): the load's observation exists and
is notified (`tensor_notified_of_finished`). Byte-specific asynchronous order from a load's
write starts with such a completion (`AsyncChain.first`; a load has no bulk-group wait), so a
load write visible to another asynchronous access has a notified observation
(`tensor_notified_of_modelCausality`). A notified load has written every slot (`CopyOk.complete`),
and a slot with a global source holds a copied byte (`writeByte_of_notified`). -/

namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A finished tensor-load write is of a notified load.** -/
theorem tensor_notified_of_finished {i w : EvId} {x y z : Nat}
    (h : AsyncFinished L X i (.write (.load x y z)) w) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  rcases h with ⟨k, hv, -, -⟩ | ⟨ws, ⟨n, m, hn, -⟩, -⟩
  · simp [GroupWaitVisible] at hv
  · obtain ⟨-, o, a, ho, -, -, hnot⟩ := hn
    exact ⟨o, ho, hnot⟩

/-- **A tensor-load write visible to an asynchronous access is of a notified load.** -/
theorem tensor_notified_of_modelCausality {l : Loc} {i j : EvId} {x y z : Nat} {q : AsyncCopy.Part}
    (h : modelCausality L X l (.async i (.write (.load x y z))) (.async j q)) :
    ∃ o, X.tensor i = some o ∧ o.effects.notified = true := by
  obtain ⟨-, hc⟩ := h
  obtain ⟨c, -, -, hw | hw⟩ := hc.first
  · obtain ⟨w, hw, -⟩ := hw
    exact tensor_notified_of_finished hw
  · obtain ⟨w, hv, -⟩ := hw
    obtain ⟨hg, -, -⟩ := hv
    simp only [GroupWaitVisible] at hg
    exact absurd hg (by simp)

/-- **A notified tensor load wrote a byte at every slot with a global source.** -/
theorem writeByte_of_notified (hX : Consistent L K A mem0 X) {i : EvId}
    {o : TensorCopy.Observation} {x y z : Nat} {l : Loc} (ho : X.tensor i = some o)
    (hn : o.effects.notified = true) (hl : TensorCopy.readLoc o.spec x y z = some l) :
    ∃ v, TensorCopy.writeByte o x y z = some v := by
  have hok := (hX.tensor i o ho).2.1
  rw [TensorCopy.readLoc_source] at hl
  obtain ⟨slot, hs, hsrc⟩ := Option.bind_eq_some_iff.mp hl
  obtain ⟨value, hv⟩ := hok.complete hn slot
  have hw := hok.writes slot value hv
  cases hso : TensorCopy.source o.spec slot with
  | global a =>
    rw [hso] at hw
    obtain ⟨byte, -, rfl⟩ := hw
    exact ⟨byte, by simp [TensorCopy.writeByte, hs, hv, TensorCopy.Content.byte]⟩
  | fill mode format byte =>
    rw [hso] at hsrc
    cases hsrc

end
end PTX
