-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax1Facts

@[expose] public section

/-! # A loop tile's row maximum: the lazy rescale

The test of the maximum `mx` against `-∞`, the gap `sc · (m - mx)`, its exponential, the
comparison `gap ≥ -8` and the selections of the new reference maximum (`mNV`), the exponent
maximum (`mExpV`) and the rescale factor (`alphaV`), as an outcome run (`max1T`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem segMax1_2926 {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 9 2926 (factsFrom (Flow.live 2926)
      (valueEx (valueOf L g { d with site := .ldW true 3 }) (exMax1_2926 L d ++
        (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ [])))) 2935
      (factsAt L g 2935 { d with site := .alphaSt })
      (oCond (valueEx (valueOf L g { d with site := .ldW true 3 }) (exMax1_2926 L d ++
        (packVals (valueEx (valueOf L g { d with site := .ldW true 3 }) [])
          (ldPacks true 3) ++ []))) max1T) :=
  (SegD.outs (pc := 2926) (liveT := Flow.live 2935) (by decide +kernel) (by decide +kernel)
    (by kernel_rfl) (by decide +kernel) (orules_asms _ _ (by decide +kernel))
    (by decide +kernel)).weaken_end fun _ h => holds_live_congr (by kernel_rfl) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
