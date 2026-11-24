-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.RootContract
public import Core.Float.Ieee
import Mathlib.Tactic

/-! The range of specified single-precision rounded results on nonnegative arguments. -/
@[expose] public section
namespace FlashKda.NormRange
open PTX RootContract
set_option maxRecDepth 16000
noncomputable section

/-- A nonnegative binary32 result is either positive infinity or an encoded field at
least as large as the stated lower field. Field zero denotes positive zero. -/
def AtLeast (lower : Nat) (v : FVal) : Prop :=
  v = .inf false ∨ ∃ f, lower ≤ f ∧ f ≤ format.topField ∧ v = Layout.fieldVal 8 23 f false

/-- Locate a nonnegative input in a finite interval of positive float fields. Keeping the
upper field symbolic also keeps the proof independent of the size of the float format. -/
theorem locate {low top : Nat} (ordered : low ≤ top) {x : ℝ}
    (hlo : (magnitude low : ℝ) ≤ x) (hhi : x ≤ (magnitude top : ℝ)) :
    ∃ f, low ≤ f ∧ f ≤ top ∧ (magnitude f : ℝ) ≤ x ∧
      ((magnitude f : ℝ) = x ∨ f < top ∧ (magnitude f : ℝ) < x ∧ x < (magnitude (f+1) : ℝ)) := by
  classical
  let p := fun n => (magnitude n : ℝ) ≤ x
  let f := Nat.findGreatest p top
  have facts := Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest p top = f)
  have lowF : low ≤ f := by
    by_contra! small
    exact facts.2.2 small ordered hlo
  have below : (magnitude f : ℝ) ≤ x := by
    by_cases hz : f = 0
    · simpa [hz,magnitude,Layout.magnitude_zero] using
        (le_trans (by exact_mod_cast Layout.magnitude_nonneg 8 23 low) hlo)
    · exact facts.2.1 hz
  refine ⟨f,lowF,facts.1,below,?_⟩
  · by_cases e : (magnitude f : ℝ) = x
    · exact Or.inl e
    · have ht : f < top := by
        apply lt_of_le_of_ne facts.1
        intro eq
        change f = top at eq
        apply e
        rw [eq]
        exact le_antisymm (eq ▸ below) hhi
      exact Or.inr ⟨ht,lt_of_le_of_ne below e,lt_of_not_ge (facts.2.2 (Nat.lt_succ_self f) ht)⟩

theorem rounded {lower : Nat} (hl : lower ≤ format.topField) {x : ℝ}
    (hx : (magnitude lower : ℝ) ≤ x) {v : FVal}
    (h : format.round .rn .inf x false = some v) : AtLeast lower v := by
  classical
  change (Layout.binary 8 23 true .ieee).round .rn .inf x false = some v at h
  have nonneg : 0 ≤ x := le_trans (by exact_mod_cast Layout.magnitude_nonneg 8 23 lower) hx
  have sign : decide (x < 0) = false := by simp [not_lt.mpr nonneg]
  have ax := abs_of_nonneg nonneg
  by_cases z : x = 0
  · subst x
    rw [Layout.round_zero (by trivial)] at h
    have zero : lower = 0 := by
      by_contra! hn
      have pos : (0:ℝ) < magnitude lower := by exact_mod_cast Layout.magnitude_pos (by omega)
      linarith
    exact Or.inr ⟨0,by omega,Nat.zero_le _,(Option.some.inj h).symm⟩
  by_cases large : (format.maxNorm : ℝ) < |x|
  · rw [Layout.round_inf_ieee (m := .rn) (by trivial) large] at h
    simp only [sign] at h
    split at h
    · exact Or.inr ⟨_,hl,le_rfl,(Option.some.inj h).symm⟩
    · exact Or.inl (Option.some.inj h).symm
  obtain ⟨f,above,top,_,eq|⟨ht,lt,next⟩⟩ := locate hl (by simpa only [ax] using hx)
    (le_of_not_gt large : |x| ≤ (magnitude format.topField : ℝ))
  · have nf : 0 < f := by
      by_contra! hf
      have fz : f = 0 := by omega
      simp [fz,magnitude,Layout.magnitude_zero,ax] at eq
      exact z eq.symm
    rw [Layout.round_exact (m := .rn) (by trivial) nf top eq.symm (by simp), sign] at h
    exact Or.inr ⟨_,above,top,(Option.some.inj h).symm⟩
  · rw [Layout.round_between (m := .rn) (by trivial) ht lt next (by simp), sign] at h
    obtain ⟨b,_,hb⟩ := Option.map_eq_some_iff.mp h
    cases b
    · exact Or.inr ⟨_,above,top,hb.symm⟩
    · exact Or.inr ⟨_,by omega,ht,hb.symm⟩

/-- Values which can appear in a nonnegative square sum, including positive overflow. -/
def Nonneg : FVal → Prop
  | .zero _ => True
  | .fin x => 0 ≤ x
  | .inf sign => sign = false
  | .nan _ => False

def Finite : FVal → Prop
  | .zero _ | .fin _ => True
  | _ => False

def RootArg : FVal → Prop
  | .fin x => normal x
  | .inf sign => sign = false
  | _ => False

theorem flush_nonneg {v : FVal} (h : Nonneg v) : Nonneg (format.flush v) := by
  cases v <;> simp only [Layout.flush] <;> try assumption
  split <;> simp_all [Nonneg]

theorem flush_finite {v : FVal} (h : Finite v) : Finite (format.flush v) := by
  cases v <;> simp only [Layout.flush] <;> try assumption
  split <;> trivial

theorem before_flush {x : ℝ} {v : FVal} (h : format.roundFtz .rn true x = some v) :
    ∃ w, format.round .rn .inf x false = some w ∧ v = format.flush w := by
  unfold Layout.roundFtz at h
  cases hw : format.round .rn .inf x false with
  | none => simp [hw] at h
  | some w =>
    simp only [hw,bind,Option.bind,↓reduceIte] at h
    split at h <;> simp_all

theorem round_nonneg {x : ℝ} (nonneg : 0 ≤ x) {v : FVal}
    (h : format.roundFtz .rn true x = some v) : Nonneg v := by
  obtain ⟨w,hw,rfl⟩ := before_flush h
  apply flush_nonneg
  have low : (magnitude 0 : ℝ) ≤ x := by
    simpa only [magnitude,Layout.magnitude_zero,Rat.cast_zero] using nonneg
  rcases rounded (Nat.zero_le _) low hw with rfl | ⟨f,_,_,rfl⟩
  · rfl
  · unfold Layout.fieldVal
    split <;> simp [Nonneg,Layout.magnitude_nonneg]

/-- Once the exact positive argument reaches the smallest normal value, its rounded
and flushed result is either positive normal or positive infinity. -/
theorem root_argument {x : ℝ} (large : (format.minNormal : ℝ) ≤ x) {v : FVal}
    (h : format.roundFtz .rn true x = some v) : RootArg v := by
  obtain ⟨w,hw,rfl⟩ := before_flush h
  have bottom : magnitude (2^23) = format.minNormal := by decide +kernel
  rcases rounded (lower := 2^23) (by decide) (bottom ▸ large) hw with rfl | ⟨f,lo,hi,rfl⟩
  · rfl
  · have nz : f ≠ 0 := by omega
    have lower : format.minNormal ≤ magnitude f := bottom ▸
      (Layout.magnitude_strictMono 8 23).monotone lo
    have upper : magnitude f ≤ format.maxNorm := (Layout.magnitude_strictMono 8 23).monotone hi
    have keep : format.subnormal (magnitude f) = false := by
      simp [Layout.subnormal,abs_of_nonneg (Layout.magnitude_nonneg ..),not_lt.mpr lower]
    change RootArg (format.flush (Layout.fieldVal 8 23 f false))
    have fld : Layout.fieldVal 8 23 f false = .fin (magnitude f) := by simp [Layout.fieldVal,nz]
    rw [fld]
    simp only [Layout.flush,keep,Bool.false_eq_true,↓reduceIte]
    exact ⟨lower,upper⟩

end
end FlashKda.NormRange
