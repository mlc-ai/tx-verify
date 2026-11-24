-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.GatePair
import Mathlib.Tactic

/-! Keep the actual 16-term gate prefix inside the ordinary binary32 exponential range.
The model accepts separate products and additions and an implementation that fuses them. -/
@[expose] public section
namespace FlashKda.GateRange
open PTX RootContract
noncomputable section

/-- Numeric value of a specified round-to-nearest binary32 result with subnormal flushing. -/
def rounded (x q : ℚ) : Prop := ∃ w, format.roundFtz .rn true (x:ℝ) = some w ∧ w.num = some q

theorem bounded_core {floor cap : Nat} (ok : floor ≤ cap) (hc : cap ≤ format.topField)
    {x : ℝ} (lower : (magnitude floor : ℝ) ≤ |x|)
    (neg : x < 0) (limit : |x| ≤ (magnitude cap : ℝ)) :
    ∃ f, floor ≤ f ∧ f ≤ cap ∧
      format.round .rn .inf x false = some (Layout.fieldVal 8 23 f true) := by
  change ∃ f, floor ≤ f ∧ f ≤ cap ∧ (Layout.binary 8 23 true .ieee).round .rn .inf x false = _
  obtain ⟨f,ff,top,fx,eq|⟨ht,lt,next⟩⟩ := NormRange.locate ok lower limit
  have sign : decide (x<0) = true := by simp [neg]
  · have nz : f ≠ 0 := by
      rintro rfl
      simp [magnitude,Layout.magnitude_zero,abs_of_neg neg] at eq
      linarith
    refine ⟨f,ff,top,?_⟩
    rw [Layout.round_exact (m := .rn) (by trivial) (Nat.pos_of_ne_zero nz)
      (top.trans hc) eq.symm (by simp),sign]
  · have step := Layout.round_between (eb := 8) (mb := 23) (signed := true) (sp := .ieee)
      (x := x) (m := .rn) (ov := .inf) (zneg := false) (F := f) (by trivial)
      (lt_of_lt_of_le ht hc) lt next (by simp)
    obtain ⟨up,choice,_⟩ := OperandRound.nearest |x| (magnitude f) (magnitude (f+1))
      true (f%2==0) fx next.le
    rw [show decide (x<0) = true by simp [neg]] at step
    cases up
    · exact ⟨f,ff,top,by simpa [choice] using step⟩
    · exact ⟨f+1,by omega,ht,by simpa [choice] using step⟩

/-- Rounding cannot leave an interval between negative representable magnitude and zero. -/
theorem interval {cap : Nat} (hc : cap ≤ format.topField) {x q : ℚ}
    (lo : -(magnitude cap) ≤ x) (hi : x ≤ 0) (r : rounded x q) :
    -(magnitude cap) ≤ q ∧ q ≤ 0 := by
  obtain ⟨w,hr,hq⟩ := r
  obtain ⟨v,hv,rfl⟩ := NormRange.before_flush hr
  by_cases zero : x = 0
  · subst x
    simp only [Rat.cast_zero] at hv
    change (Layout.binary 8 23 true .ieee).round .rn .inf 0 false = _ at hv
    rw [Layout.round_zero (by trivial)] at hv
    cases hv
    have eq : (0:ℚ) = q := Option.some.inj hq
    subst q
    exact ⟨lo,le_rfl⟩
  have neg : (x:ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne hi zero
  have bound : |(x:ℝ)| ≤ (magnitude cap : ℝ) := by rw [abs_of_neg neg]; exact_mod_cast neg_le.mp lo
  obtain ⟨f,_,top,field⟩ := bounded_core (Nat.zero_le _) hc
    (by simp [magnitude,Layout.magnitude_zero]) neg bound
  rw [field] at hv
  cases hv
  have below := (Layout.magnitude_strictMono 8 23).monotone top
  have above := Layout.magnitude_nonneg 8 23 f
  have capPos := Layout.magnitude_nonneg 8 23 cap
  unfold Layout.fieldVal at hq
  split at hq
  · have eq : (0:ℚ) = q := Option.some.inj hq
    subst q; exact ⟨by linarith,le_rfl⟩
  · simp only [ite_true,Layout.flush] at hq
    split at hq
    · have eq : (0:ℚ) = q := Option.some.inj hq
      subst q; exact ⟨by linarith,le_rfl⟩
    · have eq : -magnitude f = q := Option.some.inj hq
      subst q; exact ⟨neg_le_neg below,by linarith⟩

/-- Positive binary32 boundaries at exact multiples of 7.5, including the full-tile 120. -/
def field (n : Nat) : Nat := [
  0x00000000,0x40f00000,0x41700000,0x41b40000,0x41f00000,0x42160000,
  0x42340000,0x42520000,0x42700000,0x42870000,0x42960000,0x42a50000,
  0x42b40000,0x42c30000,0x42d20000,0x42e10000,0x42f00000][n]?.getD 0

theorem capacities : ∀ n : Fin 17,
    magnitude (field n.val) = (15:ℚ)/2*n.val ∧ field n.val ≤ format.topField := by decide +kernel

private theorem within {n : Nat} (hn : n ≤ 16) {x q : ℚ}
    (lo : -(15/2*(n:ℚ)) ≤ x) (hi : x ≤ 0) (r : rounded x q) :
    -(15/2*(n:ℚ)) ≤ q ∧ q ≤ 0 := by
  obtain ⟨val,top⟩ := capacities ⟨n,by omega⟩
  exact val ▸ interval top (val ▸ lo) hi r

/-- The activation may overshoot one by up to 1/1024 here. Padding corresponds to
activation zero. The supplied scale is the rounded scalar passed to the device. -/
inductive Update (scale s t : ℚ) : Prop
  | fused {a} : 0 ≤ a → a ≤ 1025/1024 → rounded (s+scale*a) t → Update scale s t
  | separate {a p} : 0 ≤ a → a ≤ 1025/1024 → rounded (scale*a) p →
      rounded (s+p) t → Update scale s t

theorem delta {scale s t : ℚ} (scaleLo : -29/4 ≤ scale) (scaleHi : scale ≤ 0)
    (step : Update scale s t) : ∃ p, -(15/2) ≤ p ∧ p ≤ 0 ∧ rounded (s+p) t := by
  have term (a : ℚ) (lo : 0 ≤ a) (hi : a ≤ 1025/1024) :
      -(15/2) ≤ scale*a ∧ scale*a ≤ 0 :=
    ⟨by nlinarith [mul_le_mul_of_nonneg_right scaleLo lo],
      mul_nonpos_of_nonpos_of_nonneg scaleHi lo⟩
  cases step with
  | fused a0 a1 last => exact ⟨_,(term _ a0 a1).1,(term _ a0 a1).2,last⟩
  | separate a0 a1 prod last =>
    have raw := term _ a0 a1
    have r := within (n := 1) (by decide) (by simpa using raw.1) raw.2 prod
    exact ⟨_,by simpa using r.1,r.2,last⟩

inductive Prefix (scale : ℚ) : Nat → ℚ → Prop
  | zero : Prefix scale 0 0
  | next {n s t} : Prefix scale n s → Update scale s t → Prefix scale (n+1) t

theorem bounded_prefix {scale s : ℚ} (scaleLo : -29/4 ≤ scale) (scaleHi : scale ≤ 0)
    {n : Nat} (len : n ≤ 16) (run : Prefix scale n s) : -(15/2*(n:ℚ)) ≤ s ∧ s ≤ 0 := by
  induction run with
  | zero => norm_num
  | next prev step ih =>
    obtain ⟨p,lo,hi,last⟩ := delta scaleLo scaleHi step
    obtain ⟨prevLo,prevHi⟩ := ih (by omega)
    exact within len (by push_cast; linarith) (add_nonpos prevHi hi) last

theorem paired_prefix {scale s : ℚ} (scaleLo : -29/4 ≤ scale) (scaleHi : scale ≤ 0)
    {n : Nat} (len : n ≤ 16) (run : Prefix scale n s) {a b : ℝ}
    (decay : GatePair.allowed (s:ℝ) a) (restore : GatePair.allowed (-(s:ℝ)) b) :
    |a*b-1| ≤ 1/1000000 := by
  have bound := bounded_prefix scaleLo scaleHi len run
  apply GatePair.pair _ decay restore
  rw [abs_le]
  have n16 : (n:ℚ) ≤ 16 := by exact_mod_cast len
  constructor
  · exact_mod_cast (show (-120:ℚ) ≤ s by linarith [bound.1])
  · exact_mod_cast (show s ≤ (120:ℚ) by linarith [bound.2])

end
end FlashKda.GateRange
