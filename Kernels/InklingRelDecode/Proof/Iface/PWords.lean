-- SPDX-License-Identifier: Apache-2.0
-- iface: PWords producer=W status=stated domain=consistent
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

/-! # The words of the softmax's probability store

Values the value chain proves (exact values of the probabilities): an infinite or NaN
operand does not fault a floating instruction, so the store's words are numbers only through
the finiteness of the whole chain from the loaded scores. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- **The probability store (pc 1009) writes pairs of bf16 numbers.** -/
def PWords (X : Execution) : Prop :=
  ∀ {t sk a vals sh}, X.get (t, sk) = some ⟨1009, .tc (.st a vals sh)⟩ →
    ∀ v ∈ vals, ∃ x y : ℝ, v = .pair (.float .bf16 x) (.float .bf16 y)

end PTX.Kernels.InklingRelDecode.Proof.Iface
