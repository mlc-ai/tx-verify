-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.Residual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Energy bounds on the triangular inverse constructed by the KDA preparation kernel. -/
@[expose] public section
namespace FlashKda.InverseStability
open Matrix Finset Chunk Block Sequence Algorithm Stability Inverse
noncomputable section
variable {d : ℕ}

def lower (x : Tokens d) := coefficient (cum x.logDecay) x.key x.strength
def column (x : Tokens d) (c t : ℕ) := inverseEntry (lower x) t c
def response (x : Tokens d) (c : ℕ) := Residual.state x (fun _ => 0) (column x c)

theorem feedback (x : Tokens d) (c t : ℕ) :
    column x c t = delta t c -
      x.strength t * dot (Residual.decayed x (response x c t) t) (x.key t) := by
  unfold response
  rw [Residual.prediction, history_projection]
  rw [show dot (fun _ => 0) (weighted (cum x.logDecay) x.key t) = 0 by simp [dot], zero_add]
  rw [column, entry_eq]
  simp only [lower, coefficient, column, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

theorem shrink (x : Tokens d) (good : admissible x) (s : Row d) (t : ℕ) :
    energy (Residual.decayed x s t) ≤ energy s := by
  apply sum_le_sum
  intro i _
  simp only [Residual.decayed, mul_pow]
  have hg := (good t).1 i
  exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith [mul_nonneg hg.1 (sub_nonneg.mpr hg.2)])

/-- Between impulses, each squared correction can be paid for by the loss in state energy. -/
theorem dissipate (z k : Row d) (beta : ℝ) (hk : energy k ≤ 1) (hb : 0 ≤ beta ∧ beta ≤ 1) :
    let u := -beta * dot z k
    energy (fun i => z i + u*k i) + u^2 ≤ energy z := by
  let u := -beta * dot z k
  have expansion : energy (fun i => z i + u*k i) = energy z + 2*u*dot z k + u^2*energy k := by
    simp only [energy, dot, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change energy (fun i => z i + u*k i) + u^2 ≤ energy z
  rw [expansion]
  have h := mul_le_mul_of_nonneg_left hk (sq_nonneg u)
  have hb' := mul_nonneg (mul_nonneg hb.1 (sub_nonneg.mpr hb.2)) (sq_nonneg (dot z k))
  dsimp [u] at *
  nlinarith only [h, hb']

theorem before (x : Tokens d) (c t : ℕ) (h : t ≤ c) : response x c t = fun _ => 0 := by
  funext i
  unfold response Residual.state blockState history
  have hz : ∀ j ∈ range t, column x c j *
      restored (cum x.logDecay) x.key j i = 0 := by
    intro j hj
    rw [column, above _ (lt_of_lt_of_le (mem_range.mp hj) h), zero_mul]
  rw [sum_eq_zero hz]
  ring

/-- The column's diagonal impulse has size one. All subsequent squared entries sum to at
most one for any horizon, even when the gate and key vary at each token. -/
theorem column_energy (x : Tokens d) (good : admissible x) (c n : ℕ) :
    energy (response x c n) + ∑ t ∈ range n, (column x c t)^2 ≤
      (if c < n then 2 else 0) := by
  induction n with
  | zero => simp [before x c 0 (by omega), energy]
  | succ n ih =>
    by_cases eq : n = c
    · subst n
      have hdiag : column x c c = 1 := diagonal _ _
      have hz : ∀ j ∈ range c, (column x c j)^2 = 0 := by
        intro j hj
        simp [column, above _ (mem_range.mp hj)]
      have started : response x c (c+1) = x.key c := by
        unfold response
        rw [Residual.state_succ]
        change (fun i => Residual.decayed x (response x c c) c i + column x c c * _) = _
        rw [before x c c le_rfl, hdiag]
        simp [Residual.decayed]
      rw [started, sum_range_succ, sum_eq_zero hz, hdiag]
      simp only [Nat.lt_succ_self, ite_true, one_pow, zero_add]
      linarith [(good c).2.1]
    · let z := Residual.decayed x (response x c n) n
      have hu : column x c n = -x.strength n * dot z (x.key n) := by
        rw [feedback, delta, ite_eq_right eq]
        ring
      have hs : response x c (n+1) = fun i => z i + column x c n * x.key n i :=
        Residual.state_succ _ _ _ n
      have diss := dissipate z (x.key n) (x.strength n) (good n).2.1 (good n).2.2
      change energy (fun i => z i + _ * x.key n i) + _ ≤ energy z at diss
      rw [← hu, ← hs] at diss
      have cost := diss.trans (shrink x good (response x c n) n)
      rw [sum_range_succ]
      have e : c < n+1 ↔ c < n := by omega
      rw [if_congr e rfl rfl]
      linarith

theorem block_column (x : Tokens d) (i j : Full) :
    blockInverse (lower x) i j = column x j i := by
  let a := lower x
  let natural := Matrix.of (fun i j : Full => inverseEntry a i j)
  have left : natural * system 16 a = 1 := mul_eq_one_comm.mp (diagonal_inverse 16 a)
  have h : blockInverse a = natural := calc
    blockInverse a = (natural * system 16 a) * blockInverse a := by rw [left, one_mul]
    _ = natural := by rw [Matrix.mul_assoc, right_inverse, mul_one]
  exact congrArg (fun m : Matrix Full Full ℝ => m i j) h

theorem column_square_bound (x : Tokens d) (good : admissible x) (j : Full) :
    ∑ i : Full, (blockInverse (lower x) i j)^2 ≤ 2 := by
  simp_rw [block_column]
  rw [Fin.sum_univ_eq_sum_range (fun i => (column x j i)^2) 16]
  have bound := column_energy x good j 16
  rw [ite_eq_left j.isLt] at bound
  linarith [energy_nonneg (response x j 16)]

/-- The last column consists of its unit diagonal, saving one unit in the tile-wide bound. -/
theorem last_column (x : Tokens d) : ∑ i : Full, (blockInverse (lower x) i 15)^2 = 1 := by
  simp_rw [block_column]
  change ∑ i : Full, (column x 15 i)^2 = 1
  rw [Fin.sum_univ_eq_sum_range (fun i => (column x 15 i)^2) 16, sum_range_succ]
  have hz : ∀ i ∈ range 15, (column x 15 i)^2 = 0 := by
    intro i hi
    simp [column, above _ (mem_range.mp hi)]
  rw [sum_eq_zero hz]
  simp [column, diagonal]

theorem frobenius_squared (x : Tokens d) (good : admissible x) :
    ∑ i : Full, ∑ j : Full, (blockInverse (lower x) i j)^2 ≤ 31 := by
  rw [sum_comm, Fin.sum_univ_castSucc]
  have h := sum_le_sum (s := (univ : Finset (Fin 15)))
    (fun i _ => column_square_bound x good i.castSucc)
  have e : Fin.last 15 = (15 : Full) := rfl
  rw [e, last_column]
  norm_num at h
  linarith

/-- If a computed solve has triangular residual r, this bounds the squared error of all
sixteen corrections by 31 times the squared residual norm. -/
theorem solve_error (x : Tokens d) (good : admissible x) (u v : Full → ℝ) :
    let a := system 16 (lower x)
    let residual := a *ᵥ (u-v)
    ∑ i, (u i - v i)^2 ≤ 31 * ∑ j, (residual j)^2 := by
  let a := system 16 (lower x)
  let inv := blockInverse (lower x)
  let r := a *ᵥ (u-v)
  have left : inv * a = 1 := mul_eq_one_comm.mp (right_inverse _)
  have recovered : inv *ᵥ r = u-v := by
    dsimp [r]
    rw [Matrix.mulVec_mulVec, left, Matrix.one_mulVec]
  have row (i : Full) : (u i-v i)^2 ≤ (∑ j, (inv i j)^2) * ∑ j, (r j)^2 := by
    change ((u-v) i)^2 ≤ _
    rw [← recovered]
    exact sum_mul_sq_le_sq_mul_sq univ (inv i) r
  calc
    ∑ i, (u i-v i)^2 ≤ ∑ i, ((∑ j, (inv i j)^2) * ∑ j, (r j)^2) := sum_le_sum fun i _ => row i
    _ = (∑ i, ∑ j, (inv i j)^2) * ∑ j, (r j)^2 := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (frobenius_squared x good)
      (sum_nonneg fun _ _ => sq_nonneg _)

/-- Bound the error of the entire stored inverse using its directly checkable matrix residual. -/
theorem inverse_residual (x : Tokens d) (good : admissible x) (j : Matrix Full Full ℝ) :
    let a := system 16 (lower x)
    let inv := blockInverse (lower x)
    ∑ c, ∑ i, (j i c - inv i c)^2 ≤ 31 * ∑ c, ∑ i, ((a*j-1) i c)^2 := by
  let inv := blockInverse (lower x)
  let a := system 16 (lower x)
  have h (c : Full) := solve_error x good (fun i => j i c) (fun i => inv i c)
  have residual (c : Full) : a *ᵥ ((fun i => j i c) - fun i => inv i c) =
      fun i => (a*j-1) i c := by
    rw [Matrix.mulVec_sub]
    funext i
    change (a*j) i c - (a*inv) i c = (a*j) i c - (1 : Matrix Full Full ℝ) i c
    rw [show a*inv = 1 from right_inverse _]
  change ∑ c, ∑ i, (j i c-inv i c)^2 ≤ 31 * ∑ c, ∑ i, ((a*j-1) i c)^2
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  have hh := h c
  change _ ≤ 31 * ∑ i, ((a *ᵥ ((fun j' => j j' c) - fun j' => inv j' c)) i)^2 at hh
  rwa [residual] at hh

/-- Relate the triangular residual of the KDA tile to the error in its live solve vector. -/
theorem correction_error (x : Tokens d) (good : admissible x) (s : Row d) (u : ℕ → ℝ) :
    let v := corrections s (cum x.logDecay) x.key x.value x.strength
    ∑ i : Full, (u i - v i)^2 ≤ 31 * ∑ i : Full, (Residual.residual x s u i)^2 := by
  let a := system 16 (lower x)
  let v := corrections s (cum x.logDecay) x.key x.value x.strength
  let rhsVec := rhs s (cum x.logDecay) x.key x.value x.strength
  have hv : (fun j : Full => v j) = blockInverse (lower x) *ᵥ rhsVec := by
    funext j
    simp [v, corrections, j.isLt, lower, rhsVec]
  have solved : a *ᵥ (fun j : Full => v j) = rhsVec := by
    rw [hv, Matrix.mulVec_mulVec, show a * blockInverse (lower x) = 1 from right_inverse _,
      Matrix.one_mulVec]
  have residual : a *ᵥ ((fun j : Full => u j) - fun j : Full => v j) =
      fun i : Full => Residual.residual x s u i := by
    rw [Matrix.mulVec_sub, solved]
    funext i
    change (∑ j : Full, (if j.val < i.val then lower x i j else delta i j) * u j) - _ = _
    rw [Fin.sum_univ_eq_sum_range (fun j => (if j < i.val then lower x i j else delta i j) * u j)
      16, row_sum i.isLt]
    simp only [lower, coefficient, rhsVec, rhs, Residual.residual, mul_sub, mul_sum]
    ring_nf
    congr 1
    apply sum_congr rfl
    intro j _
    ring
  have h := solve_error x good (fun i : Full => u i) (fun i : Full => v i)
  change _ ≤ 31 * ∑ i, ((a *ᵥ ((fun j : Full => u j) - fun j : Full => v j)) i)^2 at h
  rwa [residual] at h

end
end FlashKda.InverseStability
