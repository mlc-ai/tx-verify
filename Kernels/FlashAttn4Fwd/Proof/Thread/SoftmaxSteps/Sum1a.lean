-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # A loop tile's row sum, part 1

The product `l · α` (`mul.f32`), the `add.rn.f32x2` tree over it and the packed probabilities
`p1V`, the unpack of the two partial sums and their `add.f32`, as an outcome run (`sum1Items`):
the row sum `lsum1V`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem sum1_b {L : Launch} {g : Nat} (d : D) :
    SegD kernel asms L g 133 3590 (factsAt L g 3590 d) 3723
      (factsAt L g 3723 { d with l := lsum1V L d }) (oCond (valueOf L g d) sum1Items) :=
  (SegD.outs (pc := 3590) (liveT := Flow.live 3723) (items := sum1Items) (by decide +kernel)
    (by decide +kernel) (by kernel_rfl) (by decide +kernel) (orules_asms _ _ (by decide +kernel))
    (by decide +kernel)).weaken_end fun _ h => holds_live_congr (by kernel_rfl) h

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
