-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Activation
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Algebra used by the FLA chunk backward kernels
The causal product, inverse solve, reverse cumulative sum and stable sigmoid slope appear in
`fla/ops/kda/chunk_bwd.py` and `gate.py`. Matrices below contain real numbers. -/
@[expose] public section
namespace FlashKda.Backward.Fla
open Finset Matrix Algorithm
open scoped Matrix
noncomputable section
variable {m n p : ℕ}

def inner (x y : Matrix (Fin m) (Fin n) ℝ) := (xᵀ * y).trace

theorem mul_right (x : Matrix (Fin m) (Fin n) ℝ) (y : Matrix (Fin n) (Fin p) ℝ)
    (b : Matrix (Fin m) (Fin p) ℝ) : inner (x*y) b = inner y (xᵀ * b) := by
  simp only [inner, transpose_mul, Matrix.mul_assoc]

theorem mul_left (x : Matrix (Fin m) (Fin n) ℝ) (y : Matrix (Fin n) (Fin p) ℝ)
    (b : Matrix (Fin m) (Fin p) ℝ) : inner (x*y) b = inner x (b * yᵀ) := by
  rw [inner, inner, transpose_mul, Matrix.mul_assoc, trace_mul_comm yᵀ, Matrix.mul_assoc]

theorem inner_sum (x y b : Matrix (Fin m) (Fin n) ℝ) :
    inner (x+y) b = inner x b + inner y b := by
  simp [inner, Matrix.add_mul]

def mask (keep : Fin m → Fin n → Prop) [DecidableRel keep] (x : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => if keep i j then x i j else 0

theorem mask_scale (keep : Fin m → Fin n → Prop) [DecidableRel keep] (s : ℝ)
    (x b : Matrix (Fin m) (Fin n) ℝ) : inner (s • mask keep x) b = inner x (s • mask keep b) := by
  simp only [inner, trace, diag_apply, Matrix.mul_apply, transpose_apply, Matrix.smul_apply,
    smul_eq_mul, mask, of_apply]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  split <;> ring

/-- FLA loads the stored, scaled causal coefficient matrix transposed for the value gradient.
For the unscaled query/key coefficients its gradient includes the output scale. The mask may
also exclude padding in the last chunk. -/
theorem causal_product (keep : Fin n → Fin n → Prop) [DecidableRel keep]
    (s : ℝ) (a da : Matrix (Fin n) (Fin n) ℝ)
    (v dv outBar : Matrix (Fin n) (Fin p) ℝ) :
    inner ((s • mask keep da) * v + (s • mask keep a) * dv) outBar =
      inner da (s • mask keep (outBar * vᵀ)) + inner dv ((s • mask keep a)ᵀ * outBar) := by
  rw [inner_sum, mul_left, mask_scale, mul_right]

/-- Differentiate the unit lower-triangular solve using its defining equation.
The kernel implements the two transpose products and the minus sign on the active entries. -/
theorem inverse_pull (a inv da dinv bar : Matrix (Fin n) (Fin n) ℝ)
    (hinv : inv * a = 1) (hd : a * dinv + da * inv = 0) :
    inner dinv bar = inner da (-(invᵀ * bar * invᵀ)) := by
  have h : dinv = -(inv * (da * inv)) := by
    have h := congrArg (fun m => inv * m) hd
    simp only [mul_add, ← Matrix.mul_assoc, hinv, one_mul, mul_zero] at h
    simpa only [Matrix.mul_assoc] using eq_neg_of_add_eq_zero_left h
  rw [h]
  simp only [inner, transpose_neg, transpose_mul, neg_mul, mul_neg, trace_neg, neg_inj]
  have a1 := mul_right inv (da * inv) bar
  have a2 := mul_left da inv (invᵀ * bar)
  simpa only [inner, transpose_mul] using a1.trans a2

/-- Transposing the inclusive prefix sum accumulates all later gradient contributions.
Chunk-local indices select exactly the live entries in that chunk. -/
theorem reverse_prefix (dx w : Fin n → ℝ) :
    (∑ i, (∑ j, if j ≤ i then dx j else 0) * w i) =
      ∑ j, dx j * ∑ i, if j ≤ i then w i else 0 := by
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  split <;> simp_all

/-- The state-gradient scan in FLA's chunked backward. Here q and a already include the
output scale. The corrected values are u - w*h. The two forward results are q*h + a*f and
e*h + k*f, where f denotes those corrected values and e is the diagonal decay matrix.
The weights from both forward results contribute to the same corrected-value gradient. -/
theorem state_scan {d n v : ℕ}
    (h dh : Matrix (Fin d) (Fin v) ℝ) (u du do_ : Matrix (Fin n) (Fin v) ℝ)
    (w dw q dq : Matrix (Fin n) (Fin d) ℝ) (a da : Matrix (Fin n) (Fin n) ℝ)
    (e de : Matrix (Fin d) (Fin d) ℝ) (k dk : Matrix (Fin d) (Fin n) ℝ)
    (last : Matrix (Fin d) (Fin v) ℝ) :
    let f := u - w * h
    let df := du - (dw * h + w * dh)
    let bf := aᵀ * do_ + kᵀ * last
    inner (dq*h + q*dh + da*f + a*df) do_ + inner (de*h + e*dh + dk*f + k*df) last =
      inner dh (qᵀ * do_ + eᵀ * last - wᵀ * bf) + inner du bf -
      inner dw (bf * hᵀ) + inner dq (do_ * hᵀ) + inner da (do_ * fᵀ) +
      inner de (last * hᵀ) + inner dk (last * fᵀ) := by
  dsimp only
  have rightAdd {i j : ℕ} (x y z : Matrix (Fin i) (Fin j) ℝ) :
      inner x (y+z) = inner x y + inner x z := by simp [inner, Matrix.mul_add]
  have leftSub {i j : ℕ} (x y z : Matrix (Fin i) (Fin j) ℝ) :
      inner (x-y) z = inner x z - inner y z := by simp [inner, Matrix.sub_mul]
  have rightSub {i j : ℕ} (x y z : Matrix (Fin i) (Fin j) ℝ) :
      inner x (y-z) = inner x y - inner x z := by simp [inner, Matrix.mul_sub]
  simp only [inner_sum, rightSub, rightAdd, Matrix.mul_add, Matrix.add_mul]
  simp only [mul_right q dh, mul_right e dh, mul_left dq h, mul_left de h,
    mul_left da, mul_left dk, mul_right a, mul_right k, leftSub, inner_sum,
    mul_left dw h, mul_right w dh]
  ring

/-- The bounded gate in FLA computes the slope using exp(-abs(z)) for both signs. -/
theorem stable_sigmoid (z : ℝ) :
    let r := Real.exp (-|z|)
    r * ((1 / (1+r)) * (1 / (1+r))) = sigmoidSlope z := by
  dsimp only
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
    unfold sigmoidSlope sigmoid
    have h : 0 < 1 + Real.exp (-z) := by positivity
    field_simp
    ring
  · rw [abs_of_neg (lt_of_not_ge hz), neg_neg]
    unfold sigmoidSlope sigmoid
    rw [Real.exp_neg]
    have h := Real.exp_pos z
    have hp : 0 < 1 + Real.exp z := by positivity
    field_simp
    ring

end
end FlashKda.Backward.Fla
