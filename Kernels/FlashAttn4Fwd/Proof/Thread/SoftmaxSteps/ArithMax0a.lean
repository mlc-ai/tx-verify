-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0Facts

@[expose] public section

/-! # The first tile's row maximum: the packs and the column mask -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The packs of the last load's words. -/
theorem segMax0_packs {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 16 1318
      (factsFrom (Flow.live 1317 ++ ldRegs false 3)
        (valueEx (valueOf L g { d with site := .ldW false 3 }) [])) 1334
      (factsFrom (Flow.live 1334)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1334 L d)))
      (packsOk (valueEx (valueOf L g { d with site := .ldW false 3 }) [])
        (ldPacks false 3) = true) := by
  have hpv : packVals (valueEx (valueOf L g { d with site := .ldW false 3 }) [])
      (ldPacks false 3) ++ [] = exMax0_1334 L d := by kernel_rfl
  refine (SegD.packs (liveT := Flow.live 1334) noPack_asms (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel) (segFree_asms (by decide +kernel)) (by decide +kernel)).weaken_end
    fun R h => ?_
  rwa [hpv] at h

theorem segMax0_1334 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (d : D) :
    Seg kernel asms L g 3 1334
      (factsFrom (Flow.live 1334)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1334 L d))) 1337
      (factsFrom (Flow.live 1337)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1337 L d))) := by
  intro t h
  have hx : skOf L < 2 ^ 31 := skOf_eq hpre ▸ hpre.skRange
  have hy : skOf L = 128 * (trips L - 1 + 1) := by
    have := skOf_eq hpre; have := hpre.skDiv128; have := hpre.skPos
    simp only [trips, Work.n, Work.sk]; omega
  ar_seg h

theorem segMax0_1337 {L : Launch} {g : Nat} (d : D) :
    Seg kernel asms L g 4 1337
      (factsFrom (Flow.live 1337)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1337 L d))) 1341
      (factsFrom (Flow.live 1341)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1341 L d))) := by
  intro t h
  ar_seg h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
