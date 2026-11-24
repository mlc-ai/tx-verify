-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Block
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

@[expose] public section
namespace FlashKda.Algorithm
noncomputable section
open Chunk Block Finset

def sigmoid (x : ℝ) := 1 / (1 + Real.exp (-x))

def normalize {d : ℕ} (x : Row d) : Row d :=
  fun i => x i / Real.sqrt (dot x x + 1 / 1000000)

def logGate {d : ℕ} (lower parameter : ℝ) (bias gate : Row d) : Row d :=
  fun i => lower * sigmoid (Real.exp parameter * (gate i + bias i))

def cum {d : ℕ} (logDecay : ℕ → Row d) (t : ℕ) : Row d :=
  fun i => Real.exp (∑ j ∈ range t, logDecay j i)

def exitState {d : ℕ} (initial : Row d) (cum key : ℕ → Row d) (u : ℕ → ℝ) : Row d :=
  fun i => initial i * cum 16 i +
    ∑ j ∈ range 16, (restored cum key j i * cum 16 i) * u j

theorem exit_eq {d : ℕ} (initial : Row d) (cum key : ℕ → Row d) (u : ℕ → ℝ) :
    exitState initial cum key u = blockState initial cum key u 16 := by
  funext i
  simp only [exitState, blockState, history, mul_add, mul_sum]
  rw [mul_comm (initial i)]
  congr 1
  apply sum_congr rfl
  intro j _
  ring

theorem padded_step {d : ℕ} (old : Row d) (v beta : ℝ) :
    step old (fun _ => 1) (fun _ => 0) v beta = old := by
  funext i
  simp [step]

theorem forward_chunk {d : ℕ} {len : ℕ} (hlen : len ≤ 16) (initial : Row d)
    (logDecay key query : ℕ → Row d) (v beta : ℕ → ℝ) (scale : ℝ) :
    let lg := fun t => if t < len then logDecay t else fun _ => 0
    let k := fun t => if t < len then key t else fun _ => 0
    let p := cum lg
    let u := corrections initial p k v beta
    let seq := sequential initial (fun t i => Real.exp (logDecay t i)) key v beta
    (∀ t < len, blockOutput initial p k query u scale t = scale * dot (seq (t+1)) (query t)) ∧
    exitState initial p k u = seq len := by
  dsimp only
  let lg := fun t => if t < len then logDecay t else fun _ => 0
  let k := fun t => if t < len then key t else fun _ => 0
  let p := cum lg
  let u := corrections initial p k v beta
  let dec := fun t i => Real.exp (lg t i)
  let sim := sequential initial dec k v beta
  let seq := sequential initial (fun t i => Real.exp (logDecay t i)) key v beta
  have agree (t : ℕ) : sim t = seq (min t len) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      by_cases h : t < len
      · rw [min_eq_left (Nat.succ_le_of_lt h)]
        change step (sim t) (dec t) (k t) (v t) (beta t) = step (seq t) _ _ _ _
        simp only [ih, min_eq_left h.le, dec, lg, k, h, ite_true]
      · rw [min_eq_right (by omega)]
        change step (sim t) (dec t) (k t) (v t) (beta t) = seq len
        simp only [ih, min_eq_right (by omega : len ≤ t), dec, lg, k, h, ite_false,
          Real.exp_zero, padded_step]
  have start (i : Fin d) : p 0 i = 1 := by simp [p, cum]
  have advance (t : ℕ) (i : Fin d) : p (t+1) i = p t i * dec t i := by
    simp [p, cum, dec, sum_range_succ, Real.exp_add]
  have nz (t : ℕ) (i : Fin d) : p (t+1) i ≠ 0 := Real.exp_ne_zero _
  have hs := corrections_solve initial p k v beta
  constructor
  · intro t ht
    change blockOutput initial p k query u scale t = scale * dot (seq (t+1)) (query t)
    rw [block_output_eq initial p dec k query v beta u scale start advance nz hs (by omega)]
    rw [show sequential initial dec k v beta (t+1) = seq (t+1) by
      simpa only [min_eq_left (by omega : t+1 ≤ len)] using agree (t+1)]
  · change exitState initial p k u = seq len
    rw [exit_eq, block_state_eq initial p dec k v beta u start advance nz hs 16 (by decide)]
    exact (agree 16).trans (by rw [min_eq_right hlen])

end
end FlashKda.Algorithm
