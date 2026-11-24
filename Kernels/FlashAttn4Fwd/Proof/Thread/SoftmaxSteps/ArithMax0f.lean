-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithMax0Facts

@[expose] public section

/-! # The first tile's row maximum: its test against `-∞`

The `setp.neu.f32` and `selp.f32` of `%r1682` (`mSel`), as an outcome run (`max0T`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem segMax0_1860 {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 2 1860
      (factsFrom (Flow.live 1860)
      (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1860 L d ++ exMax0_1683 L d))) 1862
      (factsAt L g 1862 ⟨.gen 0, d.i, d.t, half d.w, rmax0V d.w, d.l⟩)
      (oCond (valueEx (valueOf L g { d with site := .ldW false 3 })
        (exMax0_1860 L d ++ exMax0_1683 L d)) max0T) :=
  (SegD.outs (pc := 1860) (liveT := Flow.live 1862) (by decide +kernel) (by decide +kernel)
    (by kernel_rfl) (by decide +kernel) (orules_asms _ _ (by decide +kernel))
    (by decide +kernel)).weaken_end fun _ h => holds_live_congr (by kernel_rfl) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
