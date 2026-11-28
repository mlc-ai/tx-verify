-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumRd
public import Lemmas.Flow.OutKinds

@[expose] public section

/-! # Lemmas of the strict conditions of the generated runs

The conditions `Gen.X_cond` of the value windows (each item's outcome is no fault) are proved in
`Wg0/Gen/Cond*.lean` from the value equalities the numeric chain proves: an outcome that is no
fault because its value is not the sentinel (`cond_of_okVal`), and the width conditions of the
moves (`pair_bytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- An outcome whose value is not the sentinel is no fault. -/
theorem cond_of_okVal {d v : Value} {E : Exec Value} (h : okVal d E = v) (hne : v ≠ d) :
    ∃ x, E = .ok x := by
  cases E with
  | ok x => exact ⟨x, rfl⟩
  | error f => exact absurd h.symm (by simpa [okVal] using hne)

theorem erealValue_bytes (x : EReal) : (erealValue .f32 x).bytes = 4 := by
  unfold erealValue
  split_ifs <;> rfl

/-- The widths of a pair of two four-byte values and of its halves. -/
theorem pair_bytes {a b : Value} (ha : a.bytes = 4) (hb : b.bytes = 4) :
    (Value.pair a b).bytes = 8 ∧ (splitValue 64 (.pair a b)).1.bytes = 4 ∧
      (splitValue 64 (.pair a b)).2.bytes = 4 :=
  ⟨by simp [Value.bytes, ha, hb], ha, hb⟩

theorem fl_bytes {T : Value} {x : ℝ} (h : T = .float .f32 x) : T.bytes = 4 := by
  subst h; rfl

/-- The widths of a value that is a pair of two four-byte values, and of its halves. -/
theorem upk_cond {T a b : Value} (h : T = .pair a b) (ha : a.bytes = 4) (hb : b.bytes = 4) :
    T.bytes = 8 ∧ (splitValue 64 T).1.bytes = 4 ∧ (splitValue 64 T).2.bytes = 4 := by
  subst h; exact pair_bytes ha hb

/-- `cvt.rn.bf16x2.f32` of two finite words is no fault. -/
theorem bf_cond {a b : Value} {x y : ℝ} (ha : a = .float .f32 x) (hb : b = .float .f32 y) :
    ∃ v, Wg0.bfE [a, b] = .ok v := by
  subst ha hb
  exact ⟨Assumptions.bf16Pair y x, by simp [Wg0.bfE, valFloat, pure, Except.pure, Except.toOption]⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
