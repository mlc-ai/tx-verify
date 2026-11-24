-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Event shapes for scan `.loop` -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_scanLoop (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site = .word .loop ∨ d.site = .down .loop ∨
      (∃ j, d.site = .up .loop j) ∨ d.site = .total .loop) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k', acc⟩ := d
  cases hk
  soft_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
