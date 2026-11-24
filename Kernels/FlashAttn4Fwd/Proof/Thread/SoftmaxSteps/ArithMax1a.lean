-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1Facts

@[expose] public section

/-! # A loop tile's row maximum: pieces from `2780` -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The packs of the last load's words. -/
theorem segMax1_packs {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 16 2780
      (factsFrom (Flow.live 2779 ++ ldRegs true 3)
        (valueEx (valueOf L g { d with site := .ldW true 3 }) [])) 2796
      (factsFrom (Flow.live 2796) (valueEx (valueOf L g { d with site := .ldW true 3 })
        (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ [])))
      (packsOk (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
        (ldPacks true 3) = true) :=
  SegD.packs (liveT := Flow.live 2796) noPack_asms (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (segFree_asms (by decide +kernel))
    (by decide +kernel)

/-- The unpacks and the `max.f32` chain of the row maximum, with the reference maximum. -/
theorem segMax1_2796 {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 130 2796
      (factsFrom (Flow.live 2796) (valueEx (valueOf L g { d with site := .ldW true 3 })
        (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ []))) 2926
      (factsFrom (Flow.live 2926) (valueEx (valueOf L g { d with site := .ldW true 3 })
        (exMax1_2926 L d ++ (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ []))))
      (rCond (valueEx (valueOf L g { d with site := .ldW true 3 })
        (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ [])) readsMax1_2796) := by
  refine SegD.reads (pc := 2796) (keys := [2386]) (by decide +kernel) (by decide +kernel)
    (by kernel_rfl) (by decide +kernel) (noItemRule_asms _) (segFree_asms (by decide +kernel))
    (ideal_max_range (by decide +kernel)) (decline_max_range (by decide +kernel))
    (by kernel_rfl) rfl (by decide +kernel) (by decide +kernel)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
