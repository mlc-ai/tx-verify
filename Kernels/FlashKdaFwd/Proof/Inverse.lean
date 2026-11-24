-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Block
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The two diagonal solves and their merge

In the exact-real interpretation each of the eight lanes in a subgroup owns a row.
Initially the registers hold the strict lower entries and a unit diagonal. At pivot s,
each row below s subtracts its column-s multiplier times the finalized pivot row.
-/

namespace FlashKda.Inverse
noncomputable section
open Finset Matrix

def delta (i j : ℕ) : ℝ := if i = j then 1 else 0

/-- Forward substitution against one column of the identity matrix. -/
def inverseEntry (lower : ℕ → ℕ → ℝ) (r c : ℕ) : ℝ :=
  delta r c - ∑ j : Fin r, lower r j * inverseEntry lower j c
termination_by r

theorem entry_eq (a : ℕ → ℕ → ℝ) (r c : ℕ) : inverseEntry a r c =
    delta r c - ∑ j ∈ range r, a r j * inverseEntry a j c := by
  rw [inverseEntry, Fin.sum_univ_eq_sum_range (fun j => a r j * inverseEntry a j c) r]

theorem above (a : ℕ → ℕ → ℝ) {r c : ℕ} (h : r < c) : inverseEntry a r c = 0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rw [entry_eq]
    have zero : ∀ j ∈ range r, a r j * inverseEntry a j c = 0 := by
      intro j hj
      rw [ih j (mem_range.mp hj) (lt_trans (mem_range.mp hj) h), mul_zero]
    simp [delta, Nat.ne_of_lt h, sum_eq_zero zero]

theorem diagonal (a : ℕ → ℕ → ℝ) (r : ℕ) : inverseEntry a r r = 1 := by
  rw [entry_eq]
  have zero : ∀ j ∈ range r, a r j * inverseEntry a j r = 0 := by
    intro j hj
    rw [above a (mem_range.mp hj), mul_zero]
  simp [delta, sum_eq_zero zero]

/-- Register invariant after processing the first s pivots. -/
def partialRow (a : ℕ → ℕ → ℝ) (s r c : ℕ) : ℝ :=
  if s ≤ c ∧ c < r then a r c else
    delta r c - ∑ j ∈ range (min s r), a r j * inverseEntry a j c

theorem start (a : ℕ → ℕ → ℝ) (r c : ℕ) :
    partialRow a 0 r c = if c < r then a r c else delta r c := by simp [partialRow]

theorem finished (a : ℕ → ℕ → ℝ) {s r : ℕ} (h : r ≤ s) (c : ℕ) :
    partialRow a s r c = inverseEntry a r c := by
  have hn : ¬(s ≤ c ∧ c < r) := by omega
  rw [partialRow, ite_eq_right hn, min_eq_right h, ← entry_eq]

/-- The actual register update: add the negative multiplier times the pivot row at columns
below s; negate the multiplier at s; keep the other columns and the pivot row intact. -/
def pivot (old : ℕ → ℕ → ℝ) (s r c : ℕ) : ℝ :=
  if s < r then
    if c < s then old r c - old r s * old s c
    else if c = s then -old r s else old r c
  else old r c

theorem next (a : ℕ → ℕ → ℝ) (s r c : ℕ) :
    partialRow a (s+1) r c = pivot (partialRow a s) s r c := by
  by_cases hr : s < r
  · have hs := Nat.le_of_lt hr
    have hc := Nat.succ_le_of_lt hr
    have multiplier : partialRow a s r s = a r s := by simp [partialRow, hr]
    rw [pivot, ite_eq_left hr]
    by_cases hcol : c < s
    · rw [ite_eq_left hcol, multiplier, finished a (le_refl s)]
      simp only [partialRow, show ¬(s+1 ≤ c ∧ c < r) by omega,
        show ¬(s ≤ c ∧ c < r) by omega, ite_false, min_eq_left hc, min_eq_left hs, sum_range_succ]
      ring
    · rw [ite_eq_right hcol]
      by_cases heq : c = s
      · subst c
        have zero : ∀ j ∈ range s, a r j * inverseEntry a j s = 0 := by
          intro j hj
          rw [above a (mem_range.mp hj), mul_zero]
        simp [partialRow, hr, delta, Nat.ne_of_gt hr, min_eq_left hc, sum_range_succ,
          sum_eq_zero zero, diagonal]
      · have hgt : s < c := by omega
        simp only [ite_eq_right heq, partialRow, min_eq_left hc, min_eq_left hs, sum_range_succ,
          above a hgt, mul_zero, add_zero, show s+1 ≤ c by omega, show s ≤ c by omega]
  · have hle : r ≤ s := by omega
    rw [pivot, ite_eq_right hr, finished a hle, finished a (by omega : r ≤ s+1)]

/-- Exact contents of the row registers after s unrolled iterations. -/
def registers (a : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0 => fun r c => if c < r then a r c else delta r c
  | s+1 => pivot (registers a s) s

theorem registers_eq (a : ℕ → ℕ → ℝ) (s : ℕ) : registers a s = partialRow a s := by
  induction s with
  | zero => funext r c; exact (start a r c).symm
  | succ s ih => funext r c; rw [registers, ih, next]

theorem seven_pivots (a : ℕ → ℕ → ℝ) (r c : Fin 8) :
    registers a 7 r c = inverseEntry a r c := by
  rw [registers_eq, finished a (by omega : r.val ≤ 7)]

/-- Unit-lower matrix, with arbitrary entries below its diagonal. -/
def system (n : ℕ) (a : ℕ → ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.val < i.val then a i j else delta i j

/-- Effect of one unit-lower matrix row, with indices written as natural numbers. -/
theorem row_sum {n r : ℕ} (hr : r < n) (a x : ℕ → ℝ) :
    ∑ j ∈ range n, (if j < r then a j else delta r j) * x j =
      x r + ∑ j ∈ range r, a j * x j := by
  have split : ∀ j, (if j < r then a j else delta r j) * x j =
      (if j < r then a j * x j else 0) + (if r = j then x j else 0) := by
    intro j
    by_cases h : j < r
    · simp [h, Nat.ne_of_gt h]
    · by_cases e : r = j <;> simp [h, delta, e]
  simp_rw [split]
  rw [sum_add_distrib]
  have cut : ∑ j ∈ range n, (if j < r then a j * x j else 0) =
      ∑ j ∈ range r, a j * x j := by
    calc
      _ = ∑ j ∈ range r, (if j < r then a j * x j else 0) := by
        symm
        apply sum_subset (range_mono hr.le)
        intro j _ hj
        simp [show ¬ j < r from fun h => hj (mem_range.mpr h)]
      _ = _ := sum_congr rfl fun j hj => by simp [mem_range.mp hj]
  rw [cut]
  simp [hr, add_comm]

theorem diagonal_inverse (n : ℕ) (a : ℕ → ℕ → ℝ) :
    system n a * (Matrix.of fun i j : Fin n => inverseEntry a i j) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ k : Fin n, (if k.val < i.val then a i k else delta i k) *
    inverseEntry a k j) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (if k < i.val then a i k else delta i k) * inverseEntry a k j) n,
    row_sum i.isLt]
  rw [entry_eq a i j]
  change _ = if i = j then 1 else 0
  simp only [sub_add_cancel, delta, Fin.val_inj]

/-- Two diagonal inverses and the two matrix products implementing the off-diagonal block. -/
theorem merge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c ai bi : Matrix ι ι ℝ) (ha : a * ai = 1) (hb : b * bi = 1) :
    let p := Matrix.fromBlocks ai 0 0 bi
    let m := Matrix.fromBlocks 0 0 c 0
    Matrix.fromBlocks a 0 c b * (p + -(p * m) * p) = 1 := by
  dsimp only
  rw [fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  simp only [fromBlocks_neg, fromBlocks_multiply, fromBlocks_add, neg_zero, mul_zero, zero_mul,
    add_zero, zero_add, neg_mul, mul_neg, ← mul_assoc, ha, hb, one_mul, add_neg_cancel,
    fromBlocks_one]

end
end FlashKda.Inverse
