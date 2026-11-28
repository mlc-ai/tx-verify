-- SPDX-License-Identifier: Apache-2.0
-- iface: RescaleWords producer=W status=stated domain=consistent
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-! # The words of the softmax's rescale store

Values the value chain proves (exact values of the rescaled accumulator): an infinite or NaN
operand does not fault a floating instruction, so the store's words are numbers only through
the finiteness of the whole chain from the loaded scores. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- **The rescale store (pc 2328) writes f32 numbers**: every word reads as a real number. -/
def RescaleWords (X : Execution) : Prop :=
  ∀ {t sk a vals sh}, X.get (t, sk) = some ⟨2328, .tc (.st a vals sh)⟩ →
    ∀ v ∈ vals, ∃ r : ℝ, valFloat .f32 v = .ok r

end PTX.Kernels.InklingRelDecode.Proof.Iface
