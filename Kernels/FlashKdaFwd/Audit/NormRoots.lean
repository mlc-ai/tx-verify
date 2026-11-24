-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.NormArguments
import Kernels.FlashKdaFwd.Audit.OneTokenPipeline

/-! Enumerate every positive binary32 inverse norm allowed by the conservative PTX bound
on this input. The argument constrains possible results without choosing a hardware algorithm. -/
namespace FlashKda.Binary
open PTX OneToken
noncomputable section

def firstRootWord (key : Bool) : Nat := if key then 0x3f88c2e8 else 0x3f13c70f
def measuredWord (key : Bool) : Nat := firstRootWord key + 1
abbrev mag (w : Nat) := Layout.magnitude 8 23 w

theorem squared_contract {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    admissibleRoot x y ↔ (1-1/4194304)^2 ≤ y^2*x ∧ y^2*x ≤ (1+1/4194304)^2 := by
  have h : 0 ≤ y * Real.sqrt x := mul_nonneg hy (Real.sqrt_nonneg _)
  have eq : (y * Real.sqrt x)^2 = y^2*x := by rw [mul_pow, Real.sq_sqrt hx.le]
  rw [← eq, sq_le_sq₀ (by norm_num) h, sq_le_sq₀ h (by norm_num)]
  unfold admissibleRoot
  rw [abs_le]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

def inContract (key : Bool) (field : Nat) : Prop :=
  (1-1/4194304 : ℚ)^2 ≤ mag field ^ 2 * inputValue key ∧
  mag field ^ 2 * inputValue key ≤ (1+1/4194304 : ℚ)^2

instance (key : Bool) (field : Nat) : Decidable (inContract key field) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem field_contract (key : Bool) (field : Nat) :
    admissibleRoot (inputValue key) (mag field) ↔ inContract key field := by
  rw [squared_contract (by cases key <;> norm_num [inputValue])
    (by exact_mod_cast Layout.magnitude_nonneg 8 23 field)]
  unfold inContract
  let lo : ℚ := (1-1/4194304)^2
  let hi : ℚ := (1+1/4194304)^2
  have low : (lo : ℝ) = (1-1/4194304 : ℝ)^2 := by norm_num [lo]
  have high : (hi : ℝ) = (1+1/4194304 : ℝ)^2 := by norm_num [hi]
  rw [← low, ← high]
  norm_cast

theorem increasing (key : Bool) : Monotone (fun w => mag w ^ 2 * inputValue key) := by
  intro a b hab
  have h := (Layout.magnitude_strictMono 8 23).monotone hab
  apply mul_le_mul_of_nonneg_right _ (by cases key <;> norm_num [inputValue])
  exact (sq_le_sq₀ (Layout.magnitude_nonneg 8 23 a) (Layout.magnitude_nonneg 8 23 b)).mpr h

/-- There are four possible output fields per reciprocal square root. The adjacent outside
fields already violate the relative error bound and monotonicity excludes all others. -/
theorem all_root_words (key : Bool) (w : Nat) :
    admissibleRoot (inputValue key) (mag w) ↔ ∃ i : Fin 4, w = firstRootWord key + i.val := by
  rw [field_contract]
  constructor
  · intro h
    have before : mag (firstRootWord key - 1)^2 * inputValue key < (1-1/4194304 : ℚ)^2 :=
      by cases key <;> decide +kernel
    have after : (1+1/4194304 : ℚ)^2 < mag (firstRootWord key + 4)^2 * inputValue key :=
      by cases key <;> decide +kernel
    have lo : firstRootWord key ≤ w := by
      by_contra! contra
      exact (not_lt.mpr h.1) (lt_of_le_of_lt (increasing key (show w ≤ firstRootWord key-1
        by omega)) before)
    have hi : w < firstRootWord key + 4 := by
      by_contra! contra
      exact (not_lt.mpr h.2) (lt_of_lt_of_le after (increasing key contra))
    exact ⟨⟨w-firstRootWord key, by omega⟩, by simp; omega⟩
  · rintro ⟨i,rfl⟩
    have inRange : ∀ b : Bool, ∀ j : Fin 4, inContract b (firstRootWord b + j.val) :=
      by decide +kernel
    exact inRange key i

theorem observed_roots (key : Bool) :
    binary32.decode (measuredWord key) = some (.fin (mag (measuredWord key))) ∧
    admissibleRoot (inputValue key) (mag (measuredWord key)) :=
  ⟨by cases key <;> decide +kernel, (all_root_words key _).mpr ⟨1,rfl⟩⟩

end
end FlashKda.Binary
