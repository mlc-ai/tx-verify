-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeTcProof

@[expose] public section

/-! # Event shapes at probability-store instructions -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc0_st (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : ∃ r q, d.site = .pst r q) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨r, q, hs⟩ := hs
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  cases hs
  cases r <;> fin_cases q <;> soft_tc

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
