-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.W0Reads

@[expose] public section

/-! # Words that are the exact value of an extended real

`Ev v x`: the word `v` is `erealValue .f32 x` (`.float .f32 r` for a real, the `-inf` pattern for
`⊥`) and `x` is no `+inf`. `Rd v x`: the word reads as `x`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- The word is the `f32` word of the extended real `x`, which is no `+inf`. -/
def Ev (v : Value) (x : EReal) : Prop := v = erealValue .f32 x ∧ x ≠ ⊤

theorem Ev.read {v : Value} {x : EReal} (h : Ev v x) : readEReal .f32 v = some (.ok x) := by
  rw [h.1]; exact readEReal_erealValue h.2

/-- The word reads as `x`. -/
def Rd (v : Value) (x : EReal) : Prop := readEReal .f32 v = some (.ok x)

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
