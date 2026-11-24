-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # The softmax warps' shape table at the control sites: the closing polls and the final stores -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl5 (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r, d.site = .pwend r) ∨ ∃ k, d.site = .fin k) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  soft_shape except [.fin _ => (by soft_st)]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
