-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The softmax warps' shape table at the control sites: the store waits -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl7 (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : ∃ r k, d.site = .pwst r k) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  soft_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
