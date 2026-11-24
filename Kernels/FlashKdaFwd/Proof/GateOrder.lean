-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.GateRange
import Mathlib.Tactic

/-! Order of computed gate prefixes within the same tile, including underflow to zero. -/
@[expose] public section
namespace FlashKda.GateRange
open PTX RootContract
noncomputable section

/-- The previous prefix is either numeric zero or a negative normal binary32 word. -/
def Word (q : ℚ) : Prop := q = 0 ∨ ∃ f, 8388608 ≤ f ∧ f ≤ format.topField ∧ q = -magnitude f

private theorem bottom : magnitude 8388608 = format.minNormal := by decide +kernel

private theorem zero_round {q : ℚ} (h : rounded 0 q) : q = 0 := by
  obtain ⟨w,hr,num⟩ := h
  obtain ⟨v,rv,rfl⟩ := NormRange.before_flush hr
  have exactZero : format.round .rn .inf 0 false = some (.zero false) :=
    Layout.round_zero (eb := 8) (mb := 23) (sp := .ieee) (by trivial)
  simp only [Rat.cast_zero,exactZero,Option.some.injEq] at rv
  subst v
  exact (Option.some.inj num).symm

private theorem classify {cap : Nat} (hc : cap ≤ format.topField) {x q : ℚ}
    (lo : -magnitude cap ≤ x) (hi : x ≤ 0) (h : rounded x q) : Word q := by
  by_cases zero : x = 0
  · exact Or.inl (zero_round (zero ▸ h))
  obtain ⟨w,hr,num⟩ := h
  obtain ⟨v,rv,rfl⟩ := NormRange.before_flush hr
  have neg : (x:ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne hi zero
  have limit : |(x:ℝ)| ≤ (magnitude cap : ℝ) := by rw [abs_of_neg neg]; exact_mod_cast neg_le.mp lo
  obtain ⟨f,_,top,field⟩ := bounded_core (Nat.zero_le _) hc
    (by simp [magnitude,Layout.magnitude_zero]) neg limit
  rw [field] at rv
  cases rv
  by_cases fz : f = 0
  · subst f; exact Or.inl (Option.some.inj num).symm
  simp only [Layout.fieldVal,fz,ite_false,ite_true,Layout.flush] at num
  split at num
  · exact Or.inl (Option.some.inj num).symm
  · rename_i keep
    have pos := Layout.magnitude_pos (eb := 8) (mb := 23) (Nat.pos_of_ne_zero fz)
    have bound : 8388608 ≤ f := by
      by_contra! small
      have lt : magnitude f < magnitude 8388608 := (Layout.magnitude_strictMono 8 23) small
      rw [bottom] at lt
      simp [Layout.subnormal,abs_of_pos pos,ne_of_gt pos,lt] at keep
    exact Or.inr ⟨f,bound,top.trans hc,(Option.some.inj num).symm⟩

private theorem never_rises {cap : Nat} (hc : cap ≤ format.topField) {s x t : ℚ}
    (prev : Word s) (lo : -magnitude cap ≤ x) (le : x ≤ s) (h : rounded x t) : t ≤ s := by
  rcases prev with rfl | ⟨f,normal,_,rfl⟩
  · exact (interval hc lo le h).2
  have pos := Layout.magnitude_pos (eb := 8) (mb := 23) (show 0 < f by omega)
  have neg : (x:ℝ) < 0 := by exact_mod_cast lt_of_le_of_lt le (neg_neg_of_pos pos)
  have order : f ≤ cap := by
    by_contra! bad
    linarith [(Layout.magnitude_strictMono 8 23) bad]
  have lower : (magnitude f : ℝ) ≤ |(x:ℝ)| := by rw [abs_of_neg neg]; exact_mod_cast le_neg.mp le
  have upper : |(x:ℝ)| ≤ (magnitude cap : ℝ) := by rw [abs_of_neg neg]; exact_mod_cast neg_le.mp lo
  obtain ⟨g,fg,_,rg⟩ := bounded_core order hc lower neg upper
  obtain ⟨w,hw,num⟩ := h
  obtain ⟨v,rv,rfl⟩ := NormRange.before_flush hw
  rw [rg] at rv
  cases rv
  have keep : format.minNormal ≤ magnitude g := by
    rw [← bottom]
    exact (Layout.magnitude_strictMono 8 23).monotone (normal.trans fg)
  have gz : g ≠ 0 := by omega
  have sub : format.subnormal (-magnitude g) = false := by
    simp [Layout.subnormal,abs_of_nonneg (Layout.magnitude_nonneg ..),not_lt.mpr keep]
  simp only [Layout.fieldVal,gz,ite_false,ite_true,Layout.flush,sub,Bool.false_eq_true,
    FVal.num,Option.some.injEq] at num
  rw [← num]
  exact neg_le_neg ((Layout.magnitude_strictMono 8 23).monotone fg)

/-- Every computed prefix is nonincreasing in the token index. Prefixes at different
positions can therefore be used directly in the causal coefficient theorem. -/
theorem ordered {scale : ℚ} (scaleLo : -29/4 ≤ scale) (scaleHi : scale ≤ 0)
    (s : Nat → ℚ) (start : s 0 = 0) (length : Nat) (fit : length ≤ 16)
    (steps : ∀ i < length, Update scale (s i) (s (i+1))) {j t : Nat}
    (causal : j ≤ t) (live : t ≤ length) : s t ≤ s j := by
  have words (n : Nat) (hn : n ≤ length) : Prefix scale n (s n) ∧ Word (s n) := by
    induction n with
    | zero => rw [start]; exact ⟨.zero,Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨prev,_⟩ := ih (by omega)
      have update := steps n (by omega)
      obtain ⟨p,lo,hi,q⟩ := delta scaleLo scaleHi update
      obtain ⟨pl,ph⟩ := bounded_prefix scaleLo scaleHi (by omega) prev
      obtain ⟨mag,cap⟩ := capacities ⟨n+1,by omega⟩
      refine ⟨.next prev update,classify cap ?_ (add_nonpos ph hi) q⟩
      rw [mag]; push_cast; linarith
  have step (n) (hn : n < length) : s (n+1) ≤ s n := by
    obtain ⟨prev,word⟩ := words n (by omega)
    obtain ⟨p,lo,hi,q⟩ := delta scaleLo scaleHi (steps n hn)
    obtain ⟨pl,_⟩ := bounded_prefix scaleLo scaleHi (by omega) prev
    obtain ⟨mag,cap⟩ := capacities ⟨n+1,by omega⟩
    apply never_rises cap word _ (by linarith : s n+p ≤ s n) q
    rw [mag]; push_cast; linarith
  induction causal with
  | refl => exact le_rfl
  | step jt ih => exact (step _ (by omega)).trans (ih (by omega))

end
end FlashKda.GateRange
