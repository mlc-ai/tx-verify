-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.OperandRound
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The PTX 9.2 relative-error contract for rsqrt.approx.ftz.f32 on positive normal
operands. The format always has a normal output word meeting the published bound. -/
@[expose] public section
namespace FlashKda.RootContract
open PTX
noncomputable section
abbrev format := FloatFmt.f32.layout
abbrev magnitude := Layout.magnitude 8 23
def tolerance : ℝ := (2:ℝ) ^ (-229/10 : ℝ)
def normal (x : ℚ) := format.minNormal ≤ x ∧ x ≤ format.maxNorm
def allowed (x : ℚ) (field : Nat) : Prop :=
  8388608 ≤ field ∧ field ≤ format.topField ∧
    |(magnitude field : ℝ) * √(x:ℝ) - 1| ≤ tolerance

theorem tolerance_power : tolerance ^ 10 = (1:ℝ)/2^229 := by
  unfold tolerance
  rw [← Real.rpow_mul_natCast (by norm_num)]
  norm_num

theorem tolerance_bounds : (120:ℝ)/1000000000 ≤ tolerance ∧ tolerance ≤ 130/1000000000 := by
  have ten := tolerance_power
  have pos : 0 ≤ tolerance := by unfold tolerance; positivity
  constructor
  · by_contra! h
    have p := pow_le_pow_left₀ pos h.le 10
    rw [ten] at p
    norm_num at p
  · by_contra! h
    have p := pow_le_pow_left₀ (by norm_num) h.le 10
    rw [ten] at p
    norm_num at p

theorem decode {x : ℚ} {field : Nat} (ok : allowed x field) :
    format.decode field = some (.fin (magnitude field)) := by
  have spec := FloatFmt.decode_field .f32 false ok.2.1
  have nz : field ≠ 0 := by have := ok.1; omega
  simpa [Layout.fieldVal,nz,FloatFmt.expBits,FloatFmt.mantBits,FloatFmt.layout] using spec

/-- Squaring lets rational arithmetic check an enclosure for the relative error. -/
theorem error_iff {x y e : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h1 : e ≤ 1) :
    |y * √x - 1| ≤ e ↔ (1-e)^2 ≤ y^2*x ∧ y^2*x ≤ (1+e)^2 := by
  have hp := mul_nonneg hy (Real.sqrt_nonneg x)
  have eq : (y*√x)^2 = y^2*x := by rw [mul_pow,Real.sq_sqrt hx]
  rw [← eq,sq_le_sq₀ (sub_nonneg.mpr h1) hp,sq_le_sq₀ hp (by linarith),abs_le]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

theorem root_range {x : ℚ} (hx : normal x) :
    (1:ℝ)/2^63 ≤ √(x:ℝ) ∧ √(x:ℝ) ≤ 2^64 := by
  have lowQ : (1:ℚ)/2^126 ≤ x := by
    rw [show (1:ℚ)/2^126 = format.minNormal by decide +kernel]; exact hx.1
  have low : (1:ℝ)/2^126 ≤ x := by
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).2 lowQ
  have high : (x:ℝ) ≤ 2^128 :=
    (Rat.cast_le (K := ℝ)).2 hx.2 |>.trans (by norm_num [Layout.maxNorm, Layout.topField,
      FloatFmt.layout, Layout.magnitude, Layout.bias])
  have rootLo : (1:ℝ)/2^63 ≤ √(x:ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num at low ⊢; exact low)
  have rootHi : √(x:ℝ) ≤ 2^64 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num, by norm_num at high ⊢; exact high⟩
  exact ⟨rootLo,rootHi⟩

/-- A result within the published error is positive and normal. Flushing the result to
zero cannot arise on this input domain. -/
theorem normal_result {x y : ℚ} (hx : normal x) (error : |(y:ℝ)*√(x:ℝ)-1| ≤ tolerance) :
    normal y := by
  obtain ⟨lo,hi⟩ := root_range hx
  have hr : 0 < √(x:ℝ) := lt_of_lt_of_le (by norm_num) lo
  obtain ⟨a,b⟩ := abs_le.mp error
  have e := tolerance_bounds.2
  have bot : (format.minNormal : ℝ) * 2^64 < 1/2 := by
    norm_num [Layout.minNormal,FloatFmt.layout,Layout.bias]
  have cap : (3:ℝ)/2 < (format.maxNorm : ℝ) * (1/2^63) := by
    norm_num [Layout.maxNorm,FloatFmt.layout,Layout.topField,Layout.magnitude,Layout.bias]
  have m0 : 0 ≤ (format.minNormal : ℝ) := by norm_num [Layout.minNormal,FloatFmt.layout,Layout.bias]
  have m1 : 0 ≤ (format.maxNorm : ℝ) := by
    exact_mod_cast Layout.magnitude_nonneg 8 23 format.topField
  constructor
  · apply (Rat.cast_le (K := ℝ)).1
    by_contra! h
    have tiny := (mul_lt_mul_of_pos_right h hr).trans_le (mul_le_mul_of_nonneg_left hi m0)
    linarith
  · apply (Rat.cast_le (K := ℝ)).1
    by_contra! h
    have big := (mul_le_mul_of_nonneg_left lo m1).trans_lt (mul_lt_mul_of_pos_right h hr)
    linarith

/-- Rounding a normal exact result down is already sufficient for the PTX error bound.
The proof constructs a permitted finite word for every positive normal input, independently
of which approximation an actual chip chooses. -/
theorem exists_allowed (x : ℚ) (hx : normal x) : ∃ field, allowed x field := by
  classical
  obtain ⟨rootLo,rootHi⟩ := root_range hx
  have hr : 0 < √(x:ℝ) := lt_of_lt_of_le (by norm_num) rootLo
  let y := 1/√(x:ℝ)
  have bottom : (magnitude 8388608 : ℝ) ≤ y := by
    apply (le_div_iff₀ hr).2
    norm_num [Layout.magnitude,Layout.bias]
    linarith
  have topValue : y ≤ (magnitude format.topField : ℝ) := by
    have bound : y ≤ 2^63 := (div_le_iff₀ hr).2 (by linarith)
    exact bound.trans (by norm_num [FloatFmt.layout,Layout.topField,Layout.magnitude,Layout.bias])
  let p := fun f => (magnitude f : ℝ) ≤ y
  let field := Nat.findGreatest p format.topField
  have facts := Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest p format.topField = field)
  have first : 8388608 ≤ field := by
    by_contra! lt
    exact facts.2.2 lt (by decide) bottom
  have here : (magnitude field : ℝ) ≤ y := facts.2.1 (by omega)
  have relative : y - (magnitude field : ℝ) ≤ y/8388608 := by
    by_cases last : field = format.topField
    · rw [last]
      linarith [show 0 ≤ y by dsimp [y]; positivity]
    · have next := facts.2.2 (Nat.lt_succ_self field)
        (Nat.succ_le_of_lt (lt_of_le_of_ne facts.1 last))
      change ¬ (magnitude (field+1) : ℝ) ≤ y at next
      have gap : (magnitude (field+1) : ℝ) - (magnitude field : ℝ) ≤
          (magnitude field : ℝ)/8388608 :=
        by exact_mod_cast OperandRound.normal_spacing 8 23 field first
      linarith
  have scaled := mul_le_mul_of_nonneg_right relative hr.le
  have under := mul_le_mul_of_nonneg_right here hr.le
  have exactValue : y * √(x:ℝ) = 1 := by dsimp [y]; field_simp
  rw [exactValue] at under
  rw [sub_mul, exactValue, div_mul_eq_mul_div, exactValue] at scaled
  refine ⟨field, first, facts.1, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr under)]
  linarith [tolerance_bounds.1]

end
end FlashKda.RootContract
