-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_scan (hp : Pre p L m) (d : D) (hk : d.k = 0) (k : Epilogue.Scan)
    (hs : d.site = .word k ∨ d.site = .down k ∨ (∃ j, d.site = .up k j) ∨ d.site = .total k) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k'⟩ := d
  cases hk
  cases k <;> corr_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
