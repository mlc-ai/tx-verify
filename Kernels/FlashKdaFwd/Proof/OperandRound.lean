-- SPDX-License-Identifier: Apache-2.0
module
public import Core.Float.Round
import Mathlib.Tactic

/-! Relative error of the bfloat16 nearest-even conversion in the finite normal range. -/
@[expose] public section
namespace FlashKda.OperandRound
open PTX
noncomputable section
abbrev layout := Layout.binary 8 7 true .ieee
abbrev mag := Layout.magnitude 8 7

/-- For a binary format with m significand fraction bits, the gap above a normal
magnitude is at most 2⁻ᵐ times that magnitude, including exponent boundaries. -/
theorem normal_spacing (eb mb f : Nat) (hf : 2^mb ≤ f) :
    Layout.magnitude eb mb (f+1) - Layout.magnitude eb mb f ≤
      Layout.magnitude eb mb f / ((2^mb : Nat) : ℚ) := by
  let m := 2^mb
  have hm : 0 < m := Nat.two_pow_pos _
  let q := f/m
  let r := f%m
  have hq : q ≠ 0 := (Nat.div_pos hf hm).ne'
  have hr : r < m := Nat.mod_lt _ hm
  have decomp : r + m*q = f := Nat.mod_add_div _ _
  let u := (2:ℚ)^((q:ℤ)-Layout.bias eb-mb)
  have hu : 0 < u := zpow_pos (by norm_num) _
  have base : Layout.magnitude eb mb f = ((m:ℚ) + (r:ℚ))*u := by
    simp [Layout.magnitude, ← show m=2^mb by rfl, ← show q=f/m by rfl, hq, r, u]
  rw [base, le_div_iff₀ (by exact_mod_cast hm)]
  have extra := mul_nonneg (Nat.cast_nonneg (α:=ℚ) r) hu.le
  by_cases hc : r+1 < m
  · have up : (f+1)/m=q ∧ (f+1)%m=r+1 :=
      (Nat.div_mod_unique hm).mpr ⟨by rw [← decomp]; ring, hc⟩
    simp only [Layout.magnitude, ← show m=2^mb by rfl, up.1,up.2,hq,ite_false]
    push_cast
    change (((m:ℚ) + (r+1))*u - ((m:ℚ)+r)*u)*m ≤ _
    linarith
  · have carry : r+1=m := by omega
    have up : (f+1)/m=q+1 ∧ (f+1)%m=0 :=
      (Nat.div_mod_unique hm).mpr ⟨by rw [← decomp]; nlinarith, hm⟩
    have twice : (2:ℚ)^(((q+1:Nat):ℤ)-Layout.bias eb-mb) = 2*u := by
      rw [show ((q+1:Nat):ℤ)-Layout.bias eb-mb = ((q:ℤ)-Layout.bias eb-mb)+1 by
        push_cast; ring, zpow_add_one₀ (by norm_num)]
      dsimp [u]
      ring
    simp only [Layout.magnitude, ← show m=2^mb by rfl, up.1,up.2,Nat.succ_ne_zero,
      ite_false,Nat.add_zero,twice]
    have carryQ : (r:ℚ)+1=m := by exact_mod_cast carry
    rw [← carryQ] at *
    linarith

theorem spacing (f : Nat) (hf : 128 ≤ f) : mag (f+1) - mag f ≤ mag f / 128 := by
  simpa only [show (2^7 : Nat)=128 by decide, Nat.cast_ofNat] using normal_spacing 8 7 f hf

theorem nearest (a l u : ℝ) (neg even : Bool) (hl : l ≤ a) (hu : a ≤ u) :
    ∃ up : Bool, RoundMode.rn.away neg a l u (some even) = some up ∧
      |(if up then u else l)-a| ≤ (u-l)/2 := by
  unfold RoundMode.away
  split_ifs with left right
  · exact ⟨false,rfl,by simp [abs_of_nonpos (sub_nonpos.mpr hl)]; linarith⟩
  · exact ⟨true,rfl,by simp [abs_of_nonneg (sub_nonneg.mpr hu)]; linarith⟩
  · cases even
    · exact ⟨true,rfl,by simp [abs_of_nonneg (sub_nonneg.mpr hu)]; linarith⟩
    · exact ⟨false,rfl,by simp [abs_of_nonpos (sub_nonpos.mpr hl)]; linarith⟩

def signed (x : ℝ) (m : ℚ) : ℚ := if x < 0 then -m else m
theorem signed_error (x : ℝ) (m : ℚ) : |(signed x m : ℝ)-x| = |(m:ℝ)-(|x|)| := by
  by_cases h : x < 0
  · simp only [signed, ite_eq_left h, Rat.cast_neg, abs_of_neg h]
    rw [← abs_neg ((m:ℝ)- -x)]
    congr 1
    ring
  · simp [signed,h,abs_of_nonneg (not_lt.mp h)]

/-- Every input whose magnitude lies between the smallest normal and the largest finite
bfloat16 magnitude has a specified finite rounded result with relative error at most 1/256. -/
theorem relative (x : ℝ) (lo : (mag 128 : ℝ) ≤ |x|) (hi : |x| ≤ (mag layout.topField : ℝ)) :
    ∃ y : ℚ, layout.round .rn .inf x false = some (.fin y) ∧ |(y:ℝ)-x| ≤ |x|/256 := by
  classical
  let p := fun g => (mag g : ℝ) ≤ |x|
  let f := Nat.findGreatest p layout.topField
  have facts := Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest p layout.topField = f)
  have lower : 128 ≤ f := by
    by_contra! h
    exact facts.2.2 (n := 128) h (by decide) lo
  have nonzero : f ≠ 0 := by omega
  have l : (mag f : ℝ) ≤ |x| := facts.2.1 nonzero
  by_cases eq : (mag f : ℝ) = |x|
  · refine ⟨signed x (mag f), ?_, ?_⟩
    rw [Layout.round_exact (m := .rn) (F := f) (by trivial)
      (Nat.pos_of_ne_zero nonzero) facts.1 eq.symm (by simp)]
    simp [Layout.fieldVal, nonzero, signed]
    rw [signed_error,eq,sub_self,abs_zero]
    positivity
  · have top : f < layout.topField := by
      apply lt_of_le_of_ne facts.1
      intro z
      change f = layout.topField at z
      rw [z] at l eq
      exact eq (le_antisymm l hi)
    have above : |x| < (mag (f+1) : ℝ) :=
      lt_of_not_ge (facts.2.2 (n := f+1) (Nat.lt_succ_self f) top)
    have step := Layout.round_between (m := .rn) (ov := .inf) (zneg := false) (F := f)
      (by trivial) top (lt_of_le_of_ne l eq) above (by simp)
    obtain ⟨up, round, near⟩ := nearest |x| (mag f) (mag (f+1)) (decide (x<0))
      (f%2==0) l above.le
    have gap : (mag (f+1) : ℝ) - (mag f : ℝ) ≤ (mag f : ℝ)/128 := by
      exact_mod_cast spacing f lower
    cases up
    · refine ⟨signed x (mag f), ?_, ?_⟩
      rw [step]
      simp [round,Layout.fieldVal,nonzero,signed]
      rw [signed_error]
      simp only [Bool.false_eq_true,ite_false] at near
      linarith
    · refine ⟨signed x (mag (f+1)), ?_, ?_⟩
      rw [step]
      simp [round,Layout.fieldVal,signed]
      rw [signed_error]
      simp only [ite_true] at near
      linarith

/-- A zero or finite normal operand can be passed to the coefficient proof through the
numeric value of the actual conversion, including when the result is signed zero. -/
def inRange (x : ℝ) : Prop :=
  x = 0 ∨ ((mag 128 : ℝ) ≤ |x| ∧ |x| ≤ (mag layout.topField : ℝ))

def rounded (x : ℝ) := (layout.round .rn .inf x false).bind FVal.num

theorem value (x : ℝ) (h : inRange x) :
    ∃ y : ℚ, rounded x = some y ∧ |(y:ℝ)-x| ≤ (1/256)*|x| := by
  rcases h with rfl | ⟨lo,hi⟩
  · refine ⟨0, ?_, by norm_num⟩
    unfold rounded
    rw [Layout.round_zero (by trivial)]
    rfl
  · obtain ⟨y, result, err⟩ := relative x lo hi
    exact ⟨y, by simp [rounded,result,FVal.num], by linarith⟩

end
end FlashKda.OperandRound
