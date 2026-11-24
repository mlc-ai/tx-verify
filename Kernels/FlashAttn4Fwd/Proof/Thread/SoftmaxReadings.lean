-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxRealsSums
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.ArithBase

@[expose] public section

/-! # The real readings of the computed values

On words that are single-precision payloads and a reference maximum (and row sum) that is one,
the values the code computes (`SoftmaxReals`: `p0V`, `p1V`, `mNV`, `alphaV`, `lsum0V`, `lsum1V`)
are the real terms of the ideal arithmetic (`p0`, `p1`, `mN`, `alpha`, `lsum0`, `lsum1`): no
operation declines, so each outcome is the ideal one. The hypotheses are the finiteness facts
the loaded words have in a consistent execution (`Safety.LoadFloats`, `StatsFloats`); the
scale word reads as `sc L` (`scale_ok`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The scale word reads as `sc L` (`scale_ok`). -/
abbrev ScaleOk (L : Launch) : Prop := valFloat .f32 (scaleV L) = .ok (sc L)

/-- The words of a state are single-precision payloads. -/
def WordsF32 (w : Nat → Value) : Prop := ∀ k < 128, ∃ y, w k = .float .f32 y

theorem rd32_float (x : ℝ) : rd32 (.float .f32 x) = x := by
  rw [rd32, valFloat_float]
  rfl

/-- The pair of two scale words splits into them. -/
theorem scale_split (L : Launch) :
    splitValue 64 (joinValue (scaleV L) (scaleV L)) = (scaleV L, scaleV L) := by
  have hb : (truncBits 32 ((L.params (param "8")).getD 0)).toNat < 2 ^ 32 := by
    simp only [truncBits, BitVec.toNat_ofNat]; omega
  simp only [scaleV]
  generalize truncBits 32 ((L.params (param "8")).getD 0) = b at hb
  simp only [joinValue, splitValue, truncBits, and_self, show 2 * 32 ≤ 64 by norm_num,
    ↓reduceIte, Prod.mk.injEq, Value.bits.injEq, true_and]
  have key : b ||| b <<< 32 = BitVec.ofNat 64 (b.toNat * 2 ^ 32 + b.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.or_comm, lor_eq_add (k := 32) (by omega) hb]
    omega
  have hX : b.toNat * 4294967296 + b.toNat < 18446744073709551616 := by omega
  have h1 : (b.toNat * 4294967296 + b.toNat) % 4294967296 = b.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hb
  have h2 : (b.toNat * 4294967296 + b.toNat) / 4294967296 = b.toNat := by
    rw [Nat.mul_comm, Nat.mul_add_div (by norm_num)]; omega
  have h3 : b.toNat % 18446744073709551616 = b.toNat := Nat.mod_eq_of_lt (by omega)
  have h4 : b.toNat % 4294967296 = b.toNat := Nat.mod_eq_of_lt (by omega)
  rw [key]
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow, Nat.mod_eq_of_lt hX, h1, h2,
      h3, h4]

theorem half_eq {w : Nat → Value} (hw : WordsF32 w) {j : Nat} (hj : j < 128) :
    half w j = w j := by
  unfold half
  split
  · obtain ⟨a, ha⟩ := hw j hj
    obtain ⟨b, hb⟩ := hw (j + 1) (by omega)
    rw [ha, hb]; rfl
  · obtain ⟨a, ha⟩ := hw (j - 1) (by omega)
    obtain ⟨b, hb⟩ := hw j hj
    rw [ha, hb]; rfl

theorem half_read' {w : Nat → Value} (hw : WordsF32 w) :
    ∀ j < 128, ∃ x, valFloat .f32 (half w j) = .ok x := by
  intro j hj
  obtain ⟨y, hy⟩ := hw j hj
  exact ⟨y, by rw [half_eq hw hj, hy]; exact valFloat_float⟩

variable {L : Launch}

/-- The negated scaled maximum of a number. -/
theorem negMV_read (hsc : ScaleOk L) (x : ℝ) :
    negMV L (.float .f32 x) = .float .f32 (negM L x) := by
  unfold negMV negM
  rw [mulE_fin (hsc) valFloat_float, okVal, subE_fin valFloat_zero valFloat_float]
  rfl

/-- The exponent argument of a column of payload words, with a maximum that is a number. -/
theorem argV_read (hsc : ScaleOk L) (x : ℝ) {w : Nat → Value} (hw : WordsF32 w)
    {j : Nat} (hj : j < 128) :
    argV L (.float .f32 x) w j = .float .f32 (rd32 (w j) * sc L + negM L x) := by
  have hs := scale_split L
  unfold argV argPairV
  rw [negMV_read hsc]
  split
  · obtain ⟨a, ha⟩ := hw j hj
    obtain ⟨b, hb⟩ := hw (j + 1) (by omega)
    rw [ha, hb, fma2E_fin (x0 := a) (x1 := b) valFloat_float valFloat_float
      (by rw [hs]; exact hsc) (by rw [hs]; exact hsc) valFloat_float
      valFloat_float, okVal, rd32_float]
    rfl
  · obtain ⟨a, ha⟩ := hw (j - 1) (by omega)
    obtain ⟨b, hb⟩ := hw j hj
    rw [ha, hb, fma2E_fin (x0 := a) (x1 := b) valFloat_float valFloat_float
      (by rw [hs]; exact hsc) (by rw [hs]; exact hsc) valFloat_float
      valFloat_float, okVal, rd32_float]
    rfl

/-- The probability of a column of payload words, with a maximum that is a number. -/
theorem pV_read (hsc : ScaleOk L) (x : ℝ) {w : Nat → Value} (hw : WordsF32 w)
    {j : Nat} (hj : j < 128) :
    pV L (.float .f32 x) w j =
      .float .f32 (Real.rpow 2 (rd32 (w j) * sc L + negM L x)) := by
  unfold pV
  rw [argV_read hsc x hw hj]
  split
  · rw [rd32_float]; rfl
  · rw [ex2E_fin valFloat_float]; rfl

/-- **A first tile's probability** is `p0` on payload words and a maximum that is a number. -/
theorem p0V_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) {j : Nat} (hj : j < 128) : p0V L d j = .float .f32 (p0 L d j) := by
  have hsel : mSel d.m = .float .f32 x := by rw [hm]; exact mSel_read valFloat_float
  rw [p0V, hsel, pV_read hsc x hw hj, p0, D.s, half_eq hw hj, D.mR, hm, rd32_float]

theorem split_pair (a b : Value) : splitValue 64 (.pair a b) = (a, b) := rfl

/-- The pair of two numbers. -/
theorem join_float (a b : ℝ) :
    joinValue (.float .f32 a) (.float .f32 b) = .pair (.float .f32 a) (.float .f32 b) := rfl

/-- A packed sum of pairs of numbers. -/
theorem add2V_float (x0 x1 y0 y1 : ℝ) :
    add2V (.pair (.float .f32 x0) (.float .f32 x1)) (.pair (.float .f32 y0) (.float .f32 y1)) =
      .pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1)) := by
  rw [add2V, add2E_fin valFloat_float valFloat_float valFloat_float valFloat_float]
  rfl

/-- **The first tile's row sum** is `lsum0` on payload words and a maximum that is a number. -/
theorem lsum0V_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : lsum0V L d = .float .f32 (lsum0 L d) := by
  have hp : ∀ j < 128, p0V L d j = .float .f32 (p0 L d j) := fun j hj => p0V_read hsc hm hw hj
  unfold lsum0V sum0PairV
  simp (disch := decide) only [hp, join_float, add2V_float, split_pair]
  rw [floatE_add_fin valFloat_float valFloat_float]
  rfl


/-- The first packed sum of a loop tile's row sum, from the pair `{l · α, 0}`. -/
theorem add2V_float0 (x0 y0 y1 : ℝ) :
    add2V (.pair (.float .f32 x0) (.bits 32 (BitVec.ofNat 64 0)))
      (.pair (.float .f32 y0) (.float .f32 y1)) =
      .pair (.float .f32 (x0 + y0)) (.float .f32 (0 + y1)) := by
  rw [add2V, add2E_fin (va := .pair (.float .f32 x0) (.bits 32 (BitVec.ofNat 64 0)))
    (vb := .pair (.float .f32 y0) (.float .f32 y1)) valFloat_float valFloat_zero valFloat_float
    valFloat_float]
  rfl

/-- The scaled distance of a reference maximum that is a number from a loop tile's maximum. -/
theorem gapV_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : gapV L d.m d.w = .float .f32 (gap L d) := by
  have hmx := mxV_read (m := d.m) (x := x) (by rw [hm]; exact valFloat_float) (half_read' hw)
  unfold gapV gap
  rw [hmx, mSel_read valFloat_float, hm, subE_fin valFloat_float valFloat_float, okVal,
    mulE_fin (hsc) valFloat_float, okVal, D.mR, hm, rd32_float]

theorem keepV_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : keepV L d.m d.w = decide (gap L d ≥ -8) := by
  unfold keepV
  rw [gapV_read hsc hm hw, setpE_fin (cmp := .ge) (.inl rfl) valFloat_float neg8]
  simp only [okPred, Assumption.erealCompare, ge_iff_le, EReal.coe_le_coe_iff]

/-- **A loop tile's new reference maximum** is `mN`. -/
theorem mNV_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : mNV L d = .float .f32 (mN L d) := by
  have hmx := mxV_read (m := d.m) (x := x) (by rw [hm]; exact valFloat_float) (half_read' hw)
  unfold mNV mN
  rw [keepV_read hsc hm hw]
  by_cases hg : gap L d ≥ -8
  · simp only [hg, decide_true, ↓reduceIte, D.mR, hm, rd32_float]
  · have hmx' : mxV (.float .f32 x) d.w = .float .f32 (mx x d.s) := by rw [← hm]; exact hmx
    simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte, D.mR, hm, rd32_float, hmx']

/-- **A loop tile's exponent maximum** is `mN`. -/
theorem mExpV_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : mExpV L d = .float .f32 (mN L d) := by
  have hmx := mxV_read (m := d.m) (x := x) (by rw [hm]; exact valFloat_float) (half_read' hw)
  unfold mExpV mN
  rw [keepV_read hsc hm hw]
  by_cases hg : gap L d ≥ -8
  · simp only [hg, decide_true, ↓reduceIte, D.mR, hm, rd32_float]
  · have hmx' : mxV (.float .f32 x) d.w = .float .f32 (mx x d.s) := by rw [← hm]; exact hmx
    simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte, D.mR, hm, rd32_float, hmx']
    exact mSel_read valFloat_float

/-- **A loop tile's rescale factor** reads as `alpha`. -/
theorem alphaV_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) : valFloat .f32 (alphaV L d) = .ok (alpha L d) := by
  unfold alphaV alpha
  rw [keepV_read hsc hm hw]
  by_cases hg : gap L d ≥ -8
  · simp only [hg, decide_true, ↓reduceIte]
    exact valFloat_one
  · simp only [hg, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [gapV_read hsc hm hw, ex2E_fin valFloat_float]
    exact valFloat_float

/-- **A loop tile's probability** is `p1`. -/
theorem p1V_read (hsc : ScaleOk L) {d : D} {x : ℝ} (hm : d.m = .float .f32 x)
    (hw : WordsF32 d.w) {j : Nat} (hj : j < 128) : p1V L d j = .float .f32 (p1 L d j) := by
  rw [p1V, mExpV_read hsc hm hw, pV_read hsc _ hw hj, p1, D.s, half_eq hw hj]

/-- **A loop tile's row sum** is `lsum1` on payload words, a reference maximum and a row sum
that are numbers. -/
theorem lsum1V_read (hsc : ScaleOk L) {d : D} {x y : ℝ} (hm : d.m = .float .f32 x)
    (hl : d.l = .float .f32 y) (hw : WordsF32 d.w) : lsum1V L d = .float .f32 (lsum1 L d) := by
  have hp : ∀ j < 128, p1V L d j = .float .f32 (p1 L d j) := fun j hj => p1V_read hsc hm hw hj
  have hla : okVal (.bits 32 0) (mulE false d.l (alphaV L d)) = .float .f32 (y * alpha L d) := by
    rw [hl, mulE_fin valFloat_float (alphaV_read hsc hm hw)]; rfl
  have hj0 : joinValue (.float .f32 (y * alpha L d)) (.bits 32 (BitVec.ofNat 64 0)) =
      .pair (.float .f32 (y * alpha L d)) (.bits 32 (BitVec.ofNat 64 0)) := rfl
  unfold lsum1V sum1PairV
  rw [hla, hj0]
  simp (disch := decide) only [hp, join_float, add2V_float0, add2V_float, split_pair]
  rw [floatE_add_fin valFloat_float valFloat_float, lsum1, D.lR, hl, rd32_float]
  rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
