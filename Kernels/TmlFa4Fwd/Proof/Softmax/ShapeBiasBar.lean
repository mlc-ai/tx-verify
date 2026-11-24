-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code

@[expose] public section

/-! # Event shapes at bias fences and barriers -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_biasBar (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ b, d.site = .fence b) ∨ (∃ b, d.site = .bsync b) ∨ ∃ b, d.site = .barr b) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k', acc⟩ := d
  cases hk
  soft_shape

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
