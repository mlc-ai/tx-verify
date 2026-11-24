-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapePArrive
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapePElect

@[expose] public section

/-! # Event shapes at probability arrivals, barriers and elections -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl4 (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r, d.site = .parr r) ∨ (∃ r, d.site = .pws r) ∨ (∃ r, d.site = .pel r) ∨
      (∃ r, d.site = .parr2 r)) :
    (code p L g).ShapeAt (Ev p L g) d := by
  rcases hs with h | h | h | h
  · exact @shapeAt_pArrive p L m g hp d hk (.inl h)
  · exact @shapeAt_pElect p L m g hp d hk (.inl h)
  · exact @shapeAt_pElect p L m g hp d hk (.inr h)
  · exact @shapeAt_pArrive p L m g hp d hk (.inr h)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
