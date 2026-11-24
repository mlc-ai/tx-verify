-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxReals
public import Lemmas.Real.Rescale
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # The real numbers of a softmax row as sums

The value table's terms (`SoftmaxReals`) in the form the value facts state them
(`SoftValues`), with reference exponent `c = sc · m`:

* a probability is `2 ^ (sc · s j - c)` (`p0_eq`, `p1_eq`, with `c = sc · mN` in a loop tile);
* the rescale factor is `2 ^ (c - c')` for the old and new references, and the reference does
  not decrease (`alpha_eq`, `Numeric.lazy_rescale` with threshold `-8`);
* the row sums are the sums of the probabilities over the 128 columns, after the rescaled old
  row sum in a loop tile (`lsum0_eq`, `lsum1_eq`): the `add.rn.f32x2` trees reassociated. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A first tile's probability. -/
theorem p0_eq (L : Launch) (d : D) (j : Nat) :
    p0 L d j = (2 : ℝ) ^ (sc L * d.s j - sc L * d.mR) := by
  show (2 : ℝ) ^ (d.s j * sc L + negM L d.mR) = _
  unfold negM
  congr 1
  ring

/-- A loop tile's probability. -/
theorem p1_eq (L : Launch) (d : D) (j : Nat) :
    p1 L d j = (2 : ℝ) ^ (sc L * d.s j - sc L * mN L d) := by
  show (2 : ℝ) ^ (d.s j * sc L + negM L (mN L d)) = _
  unfold negM
  congr 1
  ring

/-- The rescale factor of a loop tile, and the reference does not decrease. -/
theorem alpha_eq (L : Launch) (d : D) :
    alpha L d = (2 : ℝ) ^ (sc L * d.mR - sc L * mN L d) ∧ sc L * d.mR ≤ sc L * mN L d :=
  Numeric.lazy_rescale (sc L) d.mR (mx d.mR d.s) (-8) (by norm_num)

/-- The first tile's row sum. -/
theorem lsum0_eq (L : Launch) (d : D) : lsum0 L d = ∑ j ∈ Finset.range 128, p0 L d j := by
  simp only [lsum0, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- A loop tile's row sum. -/
theorem lsum1_eq (L : Launch) (d : D) :
    lsum1 L d = d.lR * alpha L d + ∑ j ∈ Finset.range 128, p1 L d j := by
  simp only [lsum1, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
