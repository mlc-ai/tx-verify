-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorGrowth

namespace PTX.Tests.TensorStoreSize
noncomputable section

-- Completion flags count even when no byte effect exists (e.g. an all-OOB tile).
example (s : TensorStore.Spec) :
    ({ readsDone := true } : TensorStore.Effects s).size = 1 := by
  simp [TensorStore.Effects.size, TensorStore.Effects.readSlots, TensorStore.Effects.writeSlots]

example (s : TensorStore.Spec) :
    ({ readsDone := true, fullDone := true } : TensorStore.Effects s).size = 2 := by
  simp [TensorStore.Effects.size, TensorStore.Effects.readSlots, TensorStore.Effects.writeSlots]

-- Marking source-read completion is progress, without requiring destination writes.
example (X : Execution) (L : Launch) (i : EvId) (s : TensorStore.Spec)
    (e : TensorStore.Effects s) (he : e.readsDone = false)
    (hx : X.tensorStores i = some ⟨s, e⟩)
    (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length) :
    X.size L < ({ X with tensorStores := fun j => if j = i then (some (⟨s, { e with readsDone :=
                                                                                    true }⟩ :
      TensorStore.Observation)) else X.tensorStores j }).size L := by
  apply Execution.tensorStore_update_size hx hg hi
  apply TensorStore.Extends.size_lt_of_readsDone (a := e) (b := { e with readsDone := true })
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intros; assumption
    · intros; assumption
    · intro _; rfl
    · intros; assumption
    · intro _; rfl
    · intros; assumption
  · exact he
  · rfl

-- Full completion is another strict increase after source reads have completed.
example (s : TensorStore.Spec) (e : TensorStore.Effects s) (he : e.fullDone = false) :
    e.size < ({ e with fullDone := true } : TensorStore.Effects s).size := by
  apply TensorStore.Extends.size_lt_of_fullDone (a := e) (b := { e with fullDone := true })
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intros; assumption
    · intros; assumption
    · intros; assumption
    · intro _; rfl
    · intro _; rfl
    · intros; assumption
  · exact he
  · rfl

end
end PTX.Tests.TensorStoreSize
