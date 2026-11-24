-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The first tile's row sum, part 2

The `add.rn.f32x2` tree over the packed probabilities `p0V`, the unpack of the two partial sums
and their `add.f32`, as an outcome run (`sum0Items`): the row sum `lsum0V`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem sum0_b {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 129 2577 (factsAt L g 2577 d) 2706
      (factsAt L g 2706 { d with l := lsum0V L d }) (SumOk0 L g d) :=
  (SegD.outs (pc := 2577) (liveT := Flow.live 2706) (items := sum0Items) (by decide +kernel)
    (by decide +kernel) (by kernel_rfl) (by decide +kernel) (orules_asms _ _ (by decide +kernel))
    (by decide +kernel)).weaken_end fun _ h => holds_live_congr (by kernel_rfl) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
