-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorExecution
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Async.AsyncMBarrier

@[expose] public section

namespace PTX
noncomputable section

theorem AsyncObserved.all_writes {L : Launch} {X : Execution} {i waiter : EvId} {acq : Bool}
    {ws : MbarScope} (hc : TensorOk L X)
    (h : AsyncCopy.AsyncObserved X i (.notify .load) waiter acq ws) :
    ∃ observation, X.tensor i = some observation ∧
      ∀ slot, ∃ value, observation.effects.write slot = some value := by
  obtain ⟨observation, mapAddress, ho, _, hn, _⟩ := h.tensor
  exact ⟨observation, ho, (hc i observation ho).2.1.complete hn⟩

end
end PTX
