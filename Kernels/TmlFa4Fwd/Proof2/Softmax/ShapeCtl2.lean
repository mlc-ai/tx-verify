-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeBiasPoll
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeBiasBar

@[expose] public section

/-! # Event shapes at score and bias polls, fences and barriers -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl2 (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r, d.site = .ws r) ∨ (∃ b, d.site = .wb b) ∨ (∃ b, d.site = .fence b) ∨
      (∃ b, d.site = .bsync b) ∨ (∃ b, d.site = .barr b)) :
    (code p L g).ShapeAt (Ev p L g) d := by
  rcases hs with h | h | h
  · exact @shapeAt_biasPoll p L m g hp d hk (.inl h)
  · exact @shapeAt_biasPoll p L m g hp d hk (.inr h)
  · exact @shapeAt_biasBar p L m g hp d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
