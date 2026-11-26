-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi

@[expose] public section

/-! # The output a row's lane stores is the reference's

The accumulator word `O` of a column, with `O 2 ^ m = N` (the numerator of the column), times the
factor `w0Fac (l + l') sk m` of the sums `l`, `l'` of the lane and its partner, with
`(l + l') 2 ^ m = R` the row sum and the sink word `sk` of weight `W`: `0` for a zero row sum,
else `N / (R + W)`, the Spec's `attn` (`w0Fac_attn`). A lane with no true maximum has an empty
row. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- **The factor of the output** gives the reference's quotient. -/
theorem w0Fac_attn {r sk : EReal} {l lP m R N O W : ℝ} (hl : 0 ≤ l) (hlP : 0 ≤ lP)
    (hs : (l + lP) * (2 : ℝ) ^ m = R) (hbot : r = ⊥ → R = 0) (hO : O * (2 : ℝ) ^ m = N)
    (hsk : (sk = ⊥ ∧ W = 0) ∨ ∃ x : ℝ, sk = (x : EReal) ∧ W = (2 : ℝ) ^ x) :
    O * w0Fac (w0ESum r l + w0ESum r lP) sk m = if R = 0 then 0 else N / (R + W) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := Real.rpow_pos_of_pos (by norm_num) m
  have hz : ∀ s : ℝ, s = 0 → O * w0Fac s sk m = 0 := fun s hs0 => by simp [w0Fac, hs0]
  by_cases hr : r = ⊥
  · have hR := hbot hr
    simp only [hR, ↓reduceIte]
    exact hz _ (by simp [w0ESum, hr])
  have hE : ∀ x, w0ESum r x = x := fun x => by simp [w0ESum, hr]
  rw [hE, hE]
  by_cases hR : R = 0
  · simp only [hR, ↓reduceIte]
    refine hz _ ?_
    rw [hR] at hs
    rcases mul_eq_zero.mp hs with h | h
    · exact h
    · exact absurd h h2.ne'
  simp only [hR, ↓reduceIte]
  have hs0 : l + lP ≠ 0 := fun h => hR (by rw [← hs, h, zero_mul])
  have hsk2 : w0Sk2 sk m * (2 : ℝ) ^ m = W := by
    rcases hsk with ⟨h, rfl⟩ | ⟨x, h, rfl⟩
    · simp [w0Sk2, h]
    · subst h
      simp only [w0Sk2, EReal.coe_ne_bot, ↓reduceIte, EReal.toReal_coe]
      rw [← Real.rpow_add (by norm_num)]
      simp
  have hpos : 0 ≤ w0Sk2 sk m := by
    unfold w0Sk2
    split_ifs
    · exact le_rfl
    · exact (Real.rpow_pos_of_pos (by norm_num) _).le
  have hden : (l + lP) + w0Sk2 sk m ≠ 0 := by
    have : 0 < l + lP := lt_of_le_of_ne (add_nonneg hl hlP) (Ne.symm hs0)
    exact (add_pos_of_pos_of_nonneg this hpos).ne'
  have hR' : R + W ≠ 0 := by
    rw [← hs, ← hsk2, ← add_mul]
    exact mul_ne_zero hden h2.ne'
  unfold w0Fac
  simp only [hs0, ↓reduceIte]
  rw [← hs, ← hsk2, ← add_mul] at *
  field_simp
  rw [← hO]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
