-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxShift
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxExponent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric

noncomputable section

theorem scalePositive {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    0 < abiFloat p.scaleLog2Bits ∧ 0 < abiFloat p.invScaleBits := by
  obtain ⟨s, u, hs, hu, hS, hU⟩ := hp.scales
  simp only [abiFloat, hs, hu, Option.getD_some]
  exact ⟨by exact_mod_cast hS, by exact_mod_cast hU⟩

/-- A score before scale is applied, with no numeric payload for a masked key. -/
def maskedLogit (p : Params) (b h row key : Nat) : Option ℝ :=
  if key < p.keyCount b row then some (score p b h row key / abiFloat p.scaleLog2Bits) else none

/-- The exponent contributed by a key in the running reference's units. -/
def shiftedWeight (p : Params) (b h row key : Nat) (reference : ℝ) : ℝ :=
  if key < p.keyCount b row then (2 : ℝ) ^ (-reference) * weight p b h row key else 0

private theorem affineLogit_live {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b h row key : Nat} (hk : key < p.keyCount b row) (reference : ℝ) :
    affineScore (abiFloat p.scaleLog2Bits) (-reference) (maskedLogit p b h row key) =
      some (score p b h row key + (-reference)) := by
  simp only [affineScore, maskedLogit, ite_eq_left hk, Option.map_some]
  rw [div_mul_cancel₀ _ (ne_of_gt (scalePositive hp).1)]

private theorem affineLogit_masked {p : Params} {b h row key : Nat}
    (hk : p.keyCount b row ≤ key) (reference : ℝ) :
    affineScore (abiFloat p.scaleLog2Bits) (-reference) (maskedLogit p b h row key) =
      none := by simp [affineScore, maskedLogit, Nat.not_lt_of_ge hk]

/-- The hardware exp2 value is the reference-shifted weight, including a zero for a masked key. -/
theorem hardwareShiftedWeight {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (b h row key : Nat) (reference : ℝ) :
    ex2E true (scoreValue (affineScore (abiFloat p.scaleLog2Bits) (-reference)
      (maskedLogit p b h row key))) =
      .ok (.float .f32 (shiftedWeight p b h row key reference)) := by
  by_cases hk : key < p.keyCount b row
  · rw [affineLogit_live hp hk, shiftedWeight, ite_eq_left hk, scoreValue,
      ex2E_fin (x := score p b h row key + (-reference)) (by simp [valFloat, pure, Except.pure])]
    simp [weight, two_rpow_add, mul_comm]
  · rw [affineLogit_masked (Nat.le_of_not_gt hk), shiftedWeight, ite_eq_right hk, scoreValue]
    exact hardwareExponentNegInf

/-- The software exp2 segment uses the same weights as the hardware sites. -/
theorem softwareShiftedWeight {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (b h row key : Nat) (reference : ℝ) :
    Assumptions.swExp2Lane (scoreValue (affineScore (abiFloat p.scaleLog2Bits) (-reference)
      (maskedLogit p b h row key))) =
      .ok (shiftedWeight p b h row key reference) := by
  by_cases hk : key < p.keyCount b row
  · rw [affineLogit_live hp hk, shiftedWeight, ite_eq_left hk]
    change Except.ok ((2 : ℝ) ^ (score p b h row key + (-reference))) = _
    simp [weight, two_rpow_add, mul_comm]
  · rw [affineLogit_masked (Nat.le_of_not_gt hk), shiftedWeight, ite_eq_right hk, scoreValue]
    exact Assumptions.swExp2Lane_negInf

/-- The shifted products contributing to one PV element use the same normalization as the sum.
Setting all entries of `value` to one gives the partial row sum. -/
theorem shiftedBlockProducts (p : Params) (b h row blocks visit : Nat) (reference : ℝ)
    (value : Nat → ℝ) :
    (∑ col ∈ Finset.range 128,
      shiftedWeight p b h row (visitKey blocks visit col) reference *
        value (visitKey blocks visit col)) =
      (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount b row) blocks visit
        (fun key => weight p b h row key * value key) := by
  unfold maskedBlockSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  unfold shiftedWeight
  split <;> simp [mul_assoc]

end
end PTX.Kernels.TmlFa4Fwd.Softmax
