-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Stability
import Mathlib.Tactic

/-! A posteriori absolute forward errors from triangular residuals, tile carries and outputs. -/
@[expose] public section
namespace FlashKda.Residual
open Chunk Sequence Algorithm Stability Finset
noncomputable section
variable {d : ℕ}

/-- Physical state reconstructed from a tile's entering state and its proposed corrections. -/
def state (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (n : ℕ) :=
  blockState s (cum x.logDecay) x.key u n

/-- Residual of one live row of the unit-lower triangular system. It uses the raw-input
coefficients, the tile entry, and the proposed corrections, so an exact solve is unnecessary. -/
def residual (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (t : ℕ) :=
  let p := cum x.logDecay
  u t - x.strength t * (x.value t - dot s (weighted p x.key t) -
    ∑ j ∈ range t, u j * dot (restored p x.key j) (weighted p x.key t))

theorem state_zero (x : Tokens d) (s : Row d) (u : ℕ → ℝ) : state x s u 0 = s := by
  funext i
  simp [state, blockState, cum, history]

def decayed (x : Tokens d) (v : Row d) (t : ℕ) : Row d :=
  fun i => v i * Real.exp (x.logDecay t i)

theorem prediction (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (t : ℕ) :
    dot (decayed x (state x s u t) t) (x.key t) =
      dot (history s (restored (cum x.logDecay) x.key) u t)
        (weighted (cum x.logDecay) x.key t) := by
  apply sum_congr rfl
  intro i _
  simp only [decayed, state, blockState, weighted, cum, sum_range_succ, Real.exp_add]
  ring

theorem state_succ (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (t : ℕ) :
    state x s u (t+1) = fun i => decayed x (state x s u t) t i + u t * x.key t i := by
  funext i
  simp only [state, blockState, decayed, history, restored, cum, sum_range_succ, Real.exp_add]
  field_simp
  ring

theorem local_residual (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (t : ℕ) :
    residual x s u t =
      u t - x.strength t * (x.value t - dot (decayed x (state x s u t) t) (x.key t)) := by
  rw [prediction, history_projection]
  unfold residual
  ring

/-- The state defect induced by an arbitrary correction has exactly this Euclidean norm. -/
theorem defect (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (t : ℕ) :
    distance (state x s u (t+1)) (step (state x s u t) (fun i => Real.exp (x.logDecay t i))
      (x.key t) (x.value t) (x.strength t)) = |residual x s u t| * length (x.key t) := by
  rw [state_succ]
  have diff (i : Fin d) :
      decayed x (state x s u t) t i + u t*x.key t i -
        step (state x s u t) (fun j => Real.exp (x.logDecay t j))
          (x.key t) (x.value t) (x.strength t) i = residual x s u t * x.key t i := by
    rw [local_residual]
    unfold step decayed
    ring
  simp only [distance, length, energy, diff, mul_pow, ← mul_sum,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

def solveError (x : Tokens d) (s : Row d) (u : ℕ → ℝ) (n : ℕ) :=
  ∑ t ∈ range n, |residual x s u t| * length (x.key t)

/-- A tile's correction residuals bound every intermediate state error. -/
theorem within_tile (x : Tokens d) (good : admissible x) (s initial : Row d) (u : ℕ → ℝ) (n : ℕ) :
    distance (state x s u n) (tokenState x initial n) ≤
      distance s initial + solveError x s u n := by
  induction n with
  | zero => simp [state_zero, tokenState, sequential, solveError]
  | succ n ih =>
    obtain ⟨hg,hk,hb⟩ := good n
    let update := fun v => step v (fun i => Real.exp (x.logDecay n i)) (x.key n)
      (x.value n) (x.strength n)
    have h := triangle (state x s u (n+1)) (update (state x s u n))
      (update (tokenState x initial n))
    have stable := step_nonexpansive (state x s u n) (tokenState x initial n) _ _
      (x.value n) _ hg hk hb
    change distance (update _) (update _) ≤ _ at stable
    have err := defect x s u n
    change distance _ (update _) = _ at err
    change distance (state x s u (n+1)) (update (tokenState x initial n)) ≤ _
    rw [err] at h
    rw [show solveError x s u (n+1) = solveError x s u n + _ from sum_range_succ _ n]
    have full := h.trans (add_le_add le_rfl (stable.trans ih))
    linarith only [full]

/-- The gap from a reconstructed exit to the observed next carry includes stores, rounding
and errors in all remaining carry arithmetic. -/
def exitGap (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (b : ℕ) :=
  distance (c (b+1)) (state (suffix x (cursor total b)) (c b) (u b) (liveRows total b))

def boundaryBound (x : Tokens d) (total : ℕ) (initial : Row d) (c : ℕ → Row d)
    (u : ℕ → ℕ → ℝ) (n : ℕ) :=
  distance (c 0) initial + ∑ b ∈ range n, (exitGap x total c u b +
    solveError (suffix x (cursor total b)) (c b) (u b) (liveRows total b))

theorem boundaries (x : Tokens d) (good : admissible x) (total : ℕ) (initial : Row d)
    (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (n : ℕ) :
    distance (c n) (tokenState x initial (cursor total n)) ≤
      boundaryBound x total initial c u n := by
  apply (accumulated x good total initial c n).trans
  unfold boundaryBound
  apply add_le_add le_rfl
  apply sum_le_sum
  intro b _
  let y := suffix x (cursor total b)
  let k := liveRows total b
  have bound := within_tile y (fun t => good (cursor total b + t)) (c b) (c b) (u b) k
  have zero : distance (c b) (c b) = 0 := by simp [distance, length, energy]
  rw [zero, zero_add] at bound
  exact (triangle (c (b+1)) (state y (c b) (u b) k) (tokenState y (c b) k)).trans
    (add_le_add le_rfl bound)

/-- Bound a reported live output without evaluating any exact KDA state. -/
def outputBound (x : Tokens d) (total : ℕ) (initial : Row d) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (o : ℕ → ℝ) (scale : ℝ) (t : ℕ) :=
  let b := t/16
  let y := suffix x (cursor total b)
  let n := t%16+1
  |o t - scale * dot (state y (c b) (u b) n) (x.query t)| +
    |scale| * (boundaryBound x total initial c u b + solveError y (c b) (u b) n)

theorem outputs (x : Tokens d) (good : admissible x) (hq : ∀ t, energy (x.query t) ≤ 1)
    (total : ℕ) (initial : Row d) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (o : ℕ → ℝ) (scale : ℝ) {t : ℕ} (ht : t < total) :
    |o t - output x initial total scale t| ≤ outputBound x total initial c u o scale t := by
  let b := t/16
  let first := cursor total b
  let y := suffix x first
  let n := t%16+1
  have index : first + n = t+1 := by dsimp [first,b,cursor,n]; omega
  have start := boundaries x good total initial c u b
  have localBound := within_tile y (fun j => good (first+j)) (c b)
    (tokenState x initial first) (u b) n
  rw [state_shift x initial first n, index] at localBound
  have radius := localBound.trans (add_le_add start le_rfl)
  have proj := (output_bound (state y (c b) (u b) n) (tokenState x initial (t+1))
    (x.query t) scale (hq t)).trans (mul_le_mul_of_nonneg_left radius (abs_nonneg _))
  rw [(forward x initial total scale).1 t ht]
  exact (abs_sub_le _ _ _).trans (add_le_add le_rfl proj)

theorem final_state (x : Tokens d) (good : admissible x) (total : ℕ) (initial : Row d)
    (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) :
    distance (c ((total+15)/16)) (tokenState x initial total) ≤
      boundaryBound x total initial c u ((total+15)/16) := by
  have e := boundaries x good total initial c u ((total+15)/16)
  have last : cursor total ((total+15)/16) = total := by unfold cursor; omega
  rwa [last] at e

end
end FlashKda.Residual
