-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeTcLd
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeTcSt

@[expose] public section

/-! # Event shapes at Tensor Memory sub-step zero -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc0 (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r c, d.site = .sld r c) ∨ (∃ c, d.site = .sldw c) ∨ ∃ r q, d.site = .pst r q) :
    (code p L g).ShapeAt (Ev p L g) d := by
  rcases hs with h | h | h
  · exact @shapeAt_tc0_ld p L m g hp d hk (.inl h)
  · exact @shapeAt_tc0_ld p L m g hp d hk (.inr h)
  · exact @shapeAt_tc0_st p L m g hp d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
