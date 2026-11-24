-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeTcWaitLd
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeTcWaitSt

@[expose] public section

/-! # Event shapes at Tensor Memory sub-step one -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc1 (hp : Pre p L m) (d : D) (hk : d.k = 1)
    (hs : (∃ c, d.site = .sldw c) ∨ d.site = .pst .first 0 ∨ d.site = .pst .bias 0) :
    (code p L g).ShapeAt (Ev p L g) d := by
  rcases hs with h | h
  · exact @shapeAt_tc1_ld p L m g hp d hk h
  · exact @shapeAt_tc1_st p L m g hp d hk h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
