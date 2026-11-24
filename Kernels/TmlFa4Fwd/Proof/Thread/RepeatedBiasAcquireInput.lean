-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasAcquireGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction Thread

private theorem repeatedBiasFmaCarryWrites {p : Params} {l : Launch} {g : Nat} {warp : Fin 8}
    {x : Nat × Value} (hx : x ∈ Scores.repeatedBiasFencePack p l g warp) :
    x.1 ∉ [4166,4167,4168,4169,4170] ∧ (∀ i, biasVectorKeeps true i x.1) ∧
      x.1 ≠ biasBarReg true ∧ x.1 ∉ biasReleaseWritten true := by
  simp only [Scores.repeatedBiasFencePack,biasFenceFacts,biasStageReg,biasKeep,ite_true,
    List.mem_cons,List.not_mem_nil,or_false] at hx
  have hCode : ∀ r ∈ [7896,631,632,1062,2535],
      r ∉ [4166,4167,4168,4169,4170] ∧ (∀ i, biasVectorKeeps true i r) ∧
        r ≠ biasBarReg true ∧ r ∉ biasReleaseWritten true := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> unfold biasVectorKeeps <;> decide +kernel
  apply hCode
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp

/-- An actual returned acquire supplies its row, vector, fence and inverse-scale
operands even when no vector read has yet been recorded. -/
theorem repeatedBiasAcquireLaneOfActual {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j phase : Nat} (warp : Fin 8) (hWarp : warp.val = Prologue.warpIndex l g)
    {F : List (Nat × Value)} (cursor : OpeningTripCursor l X g 5184 F)
    {object : Loc} {acq : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨5181,.wait object phase true acq scope⟩)
    (hPos : cursor.pos = j+1)
    (hLive : ∀ x ∈ F, x.1 ∉ [4166,4167,4168,4169,4170] ∧
      (∀ i, biasVectorKeeps true i x.1) ∧ x.1 ≠ biasBarReg true ∧
      x.1 ∉ biasReleaseWritten true) :
    ∃ lane : RepeatedBiasAcquireLane l X g (stageOf warp)
        (observedBarrierOrdinal X (g,cursor.pos) (11+(stageOf warp).val))
        (Scores.repeatedBiasFencePack p l g warp ++ F),
      lane.warp = warp ∧ lane.cursor.ready = cursor.ready ∧ lane.cursor.pos = cursor.pos ∧
      lane.cursor.ending = cursor.ending := by
  obtain ⟨hFence,hScale,hRow,hStage,hVectors⟩ :=
    Scores.repeatedBiasGeometryOfAcquire hp hX warp hWarp cursor he hPos
  let c : OpeningTripCursor l X g 5184 (Scores.repeatedBiasFencePack p l g warp ++ F) :=
    ⟨cursor.pos,cursor.before,cursor.ready,cursor.ending,cursor.positive,cursor.bounded,
      cursor.released,cursor.checkpoint.mono ((holds_append ..).mpr
        ⟨⟨hScale,hFence⟩,cursor.checkpoint.2.2.2.2⟩),cursor.recorded,cursor.remaining,
      cursor.localSteps⟩
  have hStable (x : Nat × Value) (hx : x ∈ Scores.repeatedBiasFencePack p l g warp ++ F) :
      x.1 ∉ [4166,4167,4168,4169,4170] ∧ (∀ i, biasVectorKeeps true i x.1) ∧
        x.1 ≠ biasBarReg true ∧ x.1 ∉ biasReleaseWritten true := by
    exact (List.mem_append.mp hx).elim repeatedBiasFmaCarryWrites (hLive x)
  exact ⟨⟨warp,rfl,c,rfl,hRow,hStage,hVectors,fun x hx => (hStable x hx).1,
    fun x hx => (hStable x hx).2.1,fun x hx => (hStable x hx).2.2.1,
    fun x hx => List.mem_append_left _ (.tail _ hx),fun x hx => (hStable x hx).2.2.2⟩,
    rfl,rfl,rfl,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
