-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Shape

@[expose] public section

/-! # Event shapes for scan `.first` -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_scanFirst (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site = .word .first ∨ d.site = .down .first ∨
      (∃ j, d.site = .up .first j) ∨ d.site = .total .first) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k', acc⟩ := d
  cases hk
  soft_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
