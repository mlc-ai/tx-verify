-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Data.Recurrence
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
The algebra of one block of tokens: the recurrence `Recurrence.sequential` written with the
decay accumulated from the start of the block (`blockState`, `blockOutput`). The rows, the
inner product `dot`, `weighted`, `restored`, `step` and `sequential` are the specification's
definitions in `Data/Recurrence.lean`.
-/

namespace PTX.Kernels.FlashKdaFwd.Math.Chunk
noncomputable section

open Finset Recurrence
variable {d : ℕ}

def history (initial : Row d) (invKey : ℕ → Row d) (u : ℕ → ℝ) (n : ℕ) : Row d :=
  fun i => initial i + ∑ j ∈ range n, u j * invKey j i

theorem history_projection (initial x : Row d) (invKey : ℕ → Row d) (u : ℕ → ℝ) (n : ℕ) :
    dot (history initial invKey u n) x =
      dot initial x + ∑ j ∈ range n, u j * dot (invKey j) x := by
  unfold dot history
  simp only [add_mul, sum_add_distrib, sum_mul, mul_sum, mul_assoc]
  congr 1
  exact sum_comm

def Solves (n : ℕ) (initial : Row d) (cumulative key : ℕ → Row d) (v beta u : ℕ → ℝ) : Prop :=
  ∀ t < n, u t = beta t * (v t - dot initial (weighted cumulative key t) -
    ∑ j ∈ range t, u j * dot (restored cumulative key j) (weighted cumulative key t))

theorem solve_unique {n : ℕ} {initial : Row d} {cumulative key : ℕ → Row d}
    {v beta u w : ℕ → ℝ}
    (hu : Solves n initial cumulative key v beta u)
    (hw : Solves n initial cumulative key v beta w) :
    ∀ t < n, u t = w t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    rw [hu t ht, hw t ht]
    congr 2
    apply sum_congr rfl
    intro j hj
    rw [ih j (mem_range.mp hj) (lt_trans (mem_range.mp hj) ht)]

def blockState (initial : Row d) (cumulative key : ℕ → Row d) (u : ℕ → ℝ) (n : ℕ) : Row d :=
  fun i => cumulative n i * history initial (restored cumulative key) u n i

theorem block_state_eq {n : ℕ} (initial : Row d) (cumulative decay key : ℕ → Row d)
    (v beta u : ℕ → ℝ) (start : ∀ i, cumulative 0 i = 1)
    (advance : ∀ t i, cumulative (t+1) i = cumulative t i * decay t i)
    (nz : ∀ t i, cumulative (t+1) i ≠ 0) (sol : Solves n initial cumulative key v beta u) :
    ∀ t ≤ n, blockState initial cumulative key u t = sequential initial decay key v beta t := by
  intro t
  induction t with
  | zero =>
    intro _
    funext i
    simp [blockState, history, sequential, start]
  | succ t ih =>
    intro ht
    have htn : t < n := ht
    have predDot :
        dot (fun i => blockState initial cumulative key u t i * decay t i) (key t) =
          dot (history initial (restored cumulative key) u t) (weighted cumulative key t) := by
      unfold dot
      apply sum_congr rfl
      intro i _
      simp only [blockState, weighted, advance]
      ring
    have update : beta t * (v t -
        dot (fun i => blockState initial cumulative key u t i * decay t i) (key t)) = u t := by
      rw [sol t htn, predDot, history_projection]
      ring
    rw [sequential, ← ih (Nat.le_of_lt htn)]
    funext i
    simp only [step, update]
    simp only [blockState, history, sum_range_succ, restored]
    have cancel : cumulative (t + 1) i * (u t * (key t i / cumulative (t + 1) i)) =
        u t * key t i := by field_simp [nz]
    rw [← add_assoc, mul_add, cancel, advance]
    ring

def blockOutput (initial : Row d) (cumulative key query : ℕ → Row d)
    (u : ℕ → ℝ) (scale : ℝ) (t : ℕ) : ℝ :=
  let x := fun i => scale * weighted cumulative query t i
  dot initial x + ∑ j ∈ range (t + 1), u j * dot (restored cumulative key j) x

theorem block_output_eq {n : ℕ} (initial : Row d) (cumulative decay key query : ℕ → Row d)
    (v beta u : ℕ → ℝ) (scale : ℝ) (start : ∀ i, cumulative 0 i = 1)
    (advance : ∀ t i, cumulative (t+1) i = cumulative t i * decay t i)
    (nz : ∀ t i, cumulative (t+1) i ≠ 0) (sol : Solves n initial cumulative key v beta u)
    {t : ℕ} (ht : t < n) :
    blockOutput initial cumulative key query u scale t =
      scale * dot (sequential initial decay key v beta (t+1)) (query t) := by
  unfold blockOutput
  rw [← history_projection,
    ← block_state_eq initial cumulative decay key v beta u start advance nz sol (t+1) ht]
  unfold dot
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [blockState, weighted]
  ring

end
end PTX.Kernels.FlashKdaFwd.Math.Chunk
