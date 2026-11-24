-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Shape

@[expose] public section

/-! # The softmax warps' shape table at the control sites: the statistics stores -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl3 (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : ∃ b, d.site = .stat b) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  soft_shape except [.stat _ => (by soft_st)]

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
