-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Chunk
public import Kernels.FlashKdaFwd.Proof.Inverse
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

@[expose] public section
namespace FlashKda.Block
noncomputable section
open Matrix Finset Inverse Chunk

abbrev Half := Fin 8
abbrev Full := Fin 16
def order : Half ⊕ Half ≃ Full := finSumFinEquiv
def second (a : ℕ → ℕ → ℝ) (i j : ℕ) := a (8+i) (8+j)
def cross (a : ℕ → ℕ → ℝ) : Matrix Half Half ℝ := Matrix.of fun i j => a (8+i.val) j

theorem partition (a : ℕ → ℕ → ℝ) : (system 16 a).submatrix order order =
    fromBlocks (system 8 a) 0 (cross a) (system 8 (second a)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      change (if 8+j.val < i.val then _ else delta i.val (8+j.val)) = 0
      simp [delta, show ¬8+j.val < i.val by omega, show i.val ≠ 8+j.val by omega]
  | inr i =>
    cases j with
    | inl j =>
      change (if j.val < 8+i.val then _ else _) = _
      rw [ite_eq_left (by omega)]
      rfl
    | inr j =>
      change (if 8+j.val < 8+i.val then _ else delta (8+i.val) (8+j.val)) = _
      simp [system, second, delta, fromBlocks, order]
      rfl

def halfRegs (a : ℕ → ℕ → ℝ) : Matrix Half Half ℝ := Matrix.of fun i j => registers a 7 i j

theorem half_right_inverse (a : ℕ → ℕ → ℝ) : system 8 a * halfRegs a = 1 := by
  have h : halfRegs a = Matrix.of (fun i j : Half => inverseEntry a i j) :=
    Matrix.ext fun i j => seven_pivots a i j
  rw [h, diagonal_inverse]

def blockInverse (a : ℕ → ℕ → ℝ) : Matrix Full Full ℝ :=
  let p := fromBlocks (halfRegs a) 0 0 (halfRegs (second a))
  let m := fromBlocks 0 0 (cross a) 0
  (p + -(p*m)*p).submatrix order.symm order.symm

theorem right_inverse (a : ℕ → ℕ → ℝ) : system 16 a * blockInverse a = 1 := by
  have hm := merge (system 8 a) (system 8 (second a)) (cross a) _ _
    (half_right_inverse a) (half_right_inverse (second a))
  rw [← partition] at hm
  have h := congrArg (fun m : Matrix (Half ⊕ Half) (Half ⊕ Half) ℝ =>
    m.submatrix order.symm order.symm) hm
  rw [← submatrix_mul_equiv _ _ _ order.symm, submatrix_one_equiv] at h
  simpa only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id, blockInverse] using h

variable {d : ℕ}

def coefficient (cum key : ℕ → Row d) (beta : ℕ → ℝ) (t j : ℕ) : ℝ :=
  beta t * dot (restored cum key j) (weighted cum key t)

def rhs (initial : Row d) (cum key : ℕ → Row d) (v beta : ℕ → ℝ) (t : Full) : ℝ :=
  beta t * (v t - dot initial (weighted cum key t))

def corrections (initial : Row d) (cum key : ℕ → Row d) (v beta : ℕ → ℝ) (t : ℕ) : ℝ :=
  if h : t < 16 then
    (blockInverse (coefficient cum key beta) *ᵥ rhs initial cum key v beta) ⟨t,h⟩
  else 0

theorem corrections_solve (initial : Row d) (cum key : ℕ → Row d) (v beta : ℕ → ℝ) :
    Solves 16 initial cum key v beta (corrections initial cum key v beta) := by
  let a := coefficient cum key beta
  let u := corrections initial cum key v beta
  have hu : (fun j : Full => u j) = blockInverse a *ᵥ rhs initial cum key v beta := by
    funext j
    simp [u, corrections, j.isLt, a]
  have solved : system 16 a *ᵥ (fun j : Full => u j) = rhs initial cum key v beta := by
    rw [hu, mulVec_mulVec, right_inverse, one_mulVec]
  intro t ht
  have row := congrFun solved (⟨t,ht⟩ : Full)
  change (∑ j : Full, (if j.val < t then a t j else delta t j) * u j) =
    beta t * (v t - dot initial (weighted cum key t)) at row
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j < t then a t j else delta t j) * u j) 16,
    row_sum ht] at row
  change u t = _
  rw [eq_sub_of_add_eq row]
  dsimp only [a, coefficient]
  simp only [mul_sub, mul_sum, u]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

end
end FlashKda.Block
