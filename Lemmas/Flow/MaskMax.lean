-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.RuleStep

@[expose] public section

/-! # The maximum of masked scores, with the mask as one number

A proof tool for the closed form of a maximum over the elements a bit mask selects, as the
walk of `seg_sym` leaves it when a role opts in to conditional `selp` values
(`sym_selp_value`): each element is `if c i = true then .float .f32 (x i) else` the bits of
`-∞`, read by a rule step as `if c i = true then ↑(x i) else ⊥`, and the `max.f32` steps write
`erealValue .f32` of the maximum of those readings. Nothing here is specific to a kernel.

* `maskMax n c x`: the maximum of `x i` over the `i < n` with `c i`, `⊥` when there is none;
  `maskMax_succ` adds one element, `maskMax_le_iff` and `le_maskMax` characterise it.
* `ones_shr_testBit`: the mask word `0xffffffff >>> s` (the code's `shr.u32` of `-1`) has bit `i`
  exactly when `i + s < 32`, so a mask computed from a count selects the first elements. -/

namespace PTX.Flow
open PTX PTX.Assumption

noncomputable section

/-- The maximum of the extended reals `x i` over `i < n` with `c i`; `⊥` when no `c i` holds. -/
def maskMax (n : Nat) (c : Nat → Bool) (x : Nat → ℝ) : EReal :=
  (Finset.range n).sup fun i => if c i = true then (x i : EReal) else ⊥

@[simp] theorem maskMax_zero (c : Nat → Bool) (x : Nat → ℝ) : maskMax 0 c x = ⊥ := rfl

/-- One more element. -/
theorem maskMax_succ (n : Nat) (c : Nat → Bool) (x : Nat → ℝ) :
    maskMax (n + 1) c x = max (maskMax n c x) (if c n = true then (x n : EReal) else ⊥) := by
  unfold maskMax
  rw [Finset.range_add_one, Finset.sup_insert]
  exact max_comm _ _

/-- An upper bound of the masked maximum bounds every selected element. -/
theorem maskMax_le_iff {n : Nat} {c : Nat → Bool} {x : Nat → ℝ} {y : EReal} :
    maskMax n c x ≤ y ↔ ∀ i < n, c i = true → (x i : EReal) ≤ y := by
  unfold maskMax
  rw [Finset.sup_le_iff]
  refine ⟨fun h i hi hc => ?_, fun h i hi => ?_⟩
  · simpa [hc] using h i (Finset.mem_range.mpr hi)
  · split
    · exact h i (Finset.mem_range.mp hi) ‹_›
    · exact bot_le

/-- Every selected element is at most the masked maximum. -/
theorem le_maskMax {n i : Nat} {c : Nat → Bool} {x : Nat → ℝ} (hi : i < n) (hc : c i = true) :
    (x i : EReal) ≤ maskMax n c x := by
  have := Finset.le_sup (f := fun i => if c i = true then (x i : EReal) else ⊥)
    (Finset.mem_range.mpr hi)
  simpa [maskMax, hc] using this

/-- The masked maximum is `⊥` exactly when no element is selected. -/
theorem maskMax_eq_bot_iff {n : Nat} {c : Nat → Bool} {x : Nat → ℝ} :
    maskMax n c x = ⊥ ↔ ∀ i < n, c i = false := by
  rw [← le_bot_iff, maskMax_le_iff]
  refine ⟨fun h i hi => ?_, fun h i hi hc => ?_⟩
  · cases hc : c i
    · rfl
    · exact absurd (h i hi hc) (by simp)
  · simp [h i hi] at hc

/-- Bit `i` of the 32-bit mask word `0xffffffff >>> s`. -/
theorem ones_shr_testBit (s i : Nat) :
    ((BitVec.ofNat 64 (2 ^ 32 - 1) >>> s).getLsbD i) = decide (i + s < 32) := by
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]
  by_cases h : s + i < 64
  · simp only [h, decide_true, Bool.true_and]
    rw [Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_decide]
    omega
  · simp only [h, decide_false, Bool.false_and]
    symm
    simp only [decide_eq_false_iff_not]
    omega

end
end PTX.Flow
