-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.MaskedSoftmax

@[expose] public section

namespace PTX.Numeric

noncomputable section

open Finset

/-- The old accumulator's factor after a reference change. An absent reference represents
an all-masked prefix with a zero accumulator. -/
def maskedRescale (old new : Option ℝ) : ℝ :=
  old.elim 0 fun x => (2 : ℝ) ^ (x - new.getD 0)

/-- Factoring the reference out of a block of weighted terms preserves zero masked terms. -/
theorem sum_masked_shift {ι : Type*} (s : Finset ι) (visible : ι → Prop)
    [DecidablePred visible] (score value : ι → ℝ) (ref : ℝ) :
    (∑ i ∈ s, if visible i then (2 : ℝ) ^ (score i - ref) * value i else 0) =
      (2 : ℝ) ^ (-ref) * ∑ i ∈ s, if visible i then (2 : ℝ) ^ score i * value i else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [two_rpow_sub_eq_mul]
    ring
  · rw [mul_zero]

/-- Accumulation with possibly all-masked initial blocks. The exponent for new terms uses
zero as its finite reference while the stored reference is absent. An absent old reference
requires the old unshifted sum to be zero, so its actual scale of zero is valid. -/
theorem shifted_acc_masked {n : Nat} {blockSum acc : Nat → ℝ} {ref : Nat → Option ℝ}
    (h0 : acc 0 = (2 : ℝ) ^ (-(ref 0).getD 0) * blockSum 0)
    (hs : ∀ τ, τ + 1 < n → acc (τ + 1) = acc τ * maskedRescale (ref τ) (ref (τ + 1)) +
      (2 : ℝ) ^ (-(ref (τ + 1)).getD 0) * blockSum (τ + 1))
    (hempty : ∀ τ < n, ref τ = none → (∑ i ∈ range (τ + 1), blockSum i) = 0) :
    ∀ τ < n, acc τ = (2 : ℝ) ^ (-(ref τ).getD 0) * ∑ i ∈ range (τ + 1), blockSum i := by
  intro τ hτ
  induction τ with
  | zero => simpa using h0
  | succ τ ih =>
    rw [hs τ hτ, Finset.sum_range_succ (n := τ + 1), mul_add]
    congr 1
    have hprev : τ < n := by omega
    rw [ih hprev]
    cases h : ref τ with
    | none => simp [maskedRescale, hempty τ hprev h]
    | some old =>
      simp only [Option.getD_some, maskedRescale, Option.elim_some]
      have hpow : (2 : ℝ) ^ (-old) * 2 ^ (old - (ref (τ + 1)).getD 0) =
          2 ^ (-(ref (τ + 1)).getD 0) := by
        rw [← two_rpow_add]
        congr 1
        ring
      rw [mul_right_comm, hpow]

end
end PTX.Numeric
