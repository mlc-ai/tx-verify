-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasStageProgress
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Thread

/-- The actual repeated Bias input vectors and proxy fence leave the stage's
named barrier ordinal at the value it had when the acquire returned. -/
theorem repeatedBiasArrivalOrdinal {l : Launch} {X : Execution}
    {g pos : Nat} (warp : Fin 8) (words : Fin 16 → Nat → Value)
    (reads : ∀ i, BiasWordReads l X true i g (pos+4*i.val)
      (biasVectorBase l g (stageOf warp) true i) (words i))
    (fence : X.get (g,pos+64) = some
      ⟨biasFencePc true,.fenceProxy (.async (some (.shared .cta))) none⟩) :
    observedBarrierOrdinal X (g,pos+65) (11+(stageOf warp).val) =
      observedBarrierOrdinal X (g,pos) (11+(stageOf warp).val) := by
  let id := 11+(stageOf warp).val
  let mark := Execution.isBarId id
  have hVectors (k : Nat) (hBound : k ≤ 64) :
      ((X.tr g).take (pos+k)).countP mark = ((X.tr g).take pos).countP mark := by
    induction k with
    | zero => rfl
    | succ k ih =>
      let i : Fin 16 := ⟨k/4,by omega⟩
      obtain ⟨bytes,hGet,_⟩ := reads i (k%4) (by omega)
      have hIndex : pos+4*i.val+k%4 = pos+k := by dsimp [i]; omega
      rw [hIndex] at hGet
      rw [show pos+(k+1) = pos+k+1 by omega,countP_take_succ_false (p := mark) hGet rfl]
      exact ih (by omega)
  exact (countP_take_succ_false (p := mark) fence rfl).trans (hVectors 64 (by decide))

end PTX.Kernels.TmlFa4Fwd.Softmax
