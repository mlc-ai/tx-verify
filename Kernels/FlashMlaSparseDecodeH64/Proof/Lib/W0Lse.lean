-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi

@[expose] public section

/-! # The LSE word a row's lane computes is the reference's

The epilogue word `w0LseV` of the sum `s = l + l'` of the two lanes' carried sums and the carried
maximum `m`: when the row sum `R = s 2 ^ m` is zero the word is `+inf`, and otherwise the word
is the number `lseLog2Factor * log2 R` that the Spec's `lse` is. A lane with no true maximum
(`r = -inf`) has an empty row. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- **The row's LSE word** (`w0LseV`): `+inf` bits for a zero row sum, else the Spec's number. -/
theorem w0LseV_row {r : EReal} {l lP m R : ℝ} (hl : 0 ≤ l) (hlP : 0 ≤ lP)
    (hs : (l + lP) * (2 : ℝ) ^ m = R) (hbot : r = ⊥ → R = 0) :
    (R = 0 ∧ w0LseV (w0ESum r l + w0ESum r lP) (w0EMax r m) =
        .bits 32 (BitVec.ofNat 64 2139095040)) ∨
      (R ≠ 0 ∧ w0LseV (w0ESum r l + w0ESum r lP) (w0EMax r m) =
        .float .f32 (lseLog2Factor * (Real.log R / Real.log 2))) := by
  by_cases hr : r = ⊥
  · left
    refine ⟨hbot hr, ?_⟩
    simp [w0LseV, w0ESum, w0EMax, hr]
  · have hE : ∀ x, w0ESum r x = x := fun x => by simp [w0ESum, hr]
    have hM : w0EMax r m = (m : EReal) := by simp [w0EMax, hr]
    rw [hE, hE, hM]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ m := Real.rpow_pos_of_pos (by norm_num) m
    by_cases hR : R = 0
    · left
      refine ⟨hR, ?_⟩
      have : l + lP = 0 := by
        rw [hR] at hs
        rcases mul_eq_zero.mp hs with h | h
        · exact h
        · exact absurd h h2.ne'
      simp [w0LseV, this]
    · right
      refine ⟨hR, ?_⟩
      have hpos : 0 < l + lP := by
        rcases (add_nonneg hl hlP).lt_or_eq with h | h
        · exact h
        · exfalso; apply hR; rw [← hs, ← h]; simp
      have hne : ¬ (l + lP = 0 ∨ (m : EReal) = ⊥) := by
        rintro (h | h)
        · exact hpos.ne' h
        · exact EReal.coe_ne_bot _ h
      simp only [w0LseV, hne, ↓reduceIte, EReal.toReal_coe]
      congr 1
      have hlog : Real.log R = Real.log (l + lP) + m * Real.log 2 := by
        rw [← hs, Real.log_mul hpos.ne' h2.ne', Real.log_rpow (by norm_num)]
      rw [hlog, add_div, mul_div_cancel_right₀ _ (Real.log_pos (by norm_num)).ne']
      ring

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
