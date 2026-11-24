-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasObservation
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof Prologue PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- An actual repeated Bias read always returns a canonical BF16 pair, including
padding. The preceding opening rendezvous excludes generation zero. -/
theorem repeatedBiasWordShapeInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g read : Nat} {i : Fin 16}
    {access : Acc} {bytes : List (Option Byte)}
    (hRead : BiasVectorRead X (g,read) true i access bytes) :
    ∃ lo hi : Option ℝ, rebuild 3 bytes = .ok (biasLoadWord lo hi) := by
  obtain ⟨warp,word,hWarp,hAccess,hWords⟩ :=
    observedLaterBiasWordInRange hp hX hFrame (hFrame.metadataProtected hp).1 hRead
  let stage := stageOf warp
  have hStage : warpIndex l g/4 = stage.val := by rw [← hWarp]; rfl
  have hRange : 4847 < biasReadPc true i ∧ biasReadPc true i < 7605 := by
    fin_cases i <;> decide
  have he : X.get (g,read) = some ⟨biasReadPc true i,.rd access bytes⟩ := hRead
  have hPositive := firstBiasBarrierBeforeRepeatedEvent hp hX stage hStage he hRange.1 hRange.2
  obtain ⟨_,_,_,_,_,_,hValue⟩ := hWords hPositive
  exact ⟨_,_,hValue⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
