-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedFloatJ

@[expose] public section

/-! # The pack of two bf16 numbers is a datum of four bytes

`cvt.rn.bf16x2.f32` read as exact (`bf16Exact`) writes `.pair (erealValue .bf16 y)
(erealValue .bf16 x)` of its operands as extended reals. Each half has two bytes and a bit
pattern, so the pair is read as an `.f32` datum of four bytes (`Dat32`): the float tag of the typed
engine serves it, and `tcgen05.st` reads it as a 32-bit value. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Assumption
noncomputable section

theorem decode_f32_some (n : Nat) : ∃ c, FloatFmt.f32.layout.decode n = some c := by
  simp only [FloatFmt.layout, Layout.decode, Layout.width, ite_true, Nat.reduceAdd, Nat.reducePow]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem erealValue_bf16 (x : EReal) :
    (erealValue .bf16 x).bytes = 2 ∧ ∃ n, (erealValue .bf16 x).bitPattern = some n := by
  unfold erealValue
  split_ifs <;> exact ⟨rfl, _, rfl⟩

/-- **A pack of two bf16 numbers is a datum of four bytes** (`bf16Exact` on operands that are
extended reals). -/
theorem dat32_pairBf16 (x y : EReal) :
    Dat32 (.pair (erealValue .bf16 y) (erealValue .bf16 x)) := by
  obtain ⟨hb1, n1, hn1⟩ := erealValue_bf16 y
  obtain ⟨hb2, n2, hn2⟩ := erealValue_bf16 x
  have hby : (Value.pair (erealValue .bf16 y) (erealValue .bf16 x)).bytes = 4 := by
    simp [Value.bytes, hb1, hb2]
  obtain ⟨c, hc⟩ := decode_f32_some (n1 % 2 ^ (8 * (erealValue .bf16 y).bytes) +
    2 ^ (8 * (erealValue .bf16 y).bytes) * n2)
  refine ⟨⟨c, ?_⟩, hby, nofun⟩
  simp [classify, Value.bitPattern, hn1, hn2, hby, hc, FloatFmt.bytes, pure, Except.pure]
end
end PTX.Flow.TyG
