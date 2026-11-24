-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StatelessBounds
import Kernels.FlashKdaFwd.Audit.Cancellation

/-! Evaluate all 33 tokens of the documented stateless input against the real KDA recurrence. -/
namespace FlashKda.Stateless
open Chunk Sequence Cancellation
noncomputable section

def rawKey (t : ℕ) : Row 128 :=
  if t=15 then pair 1 0 else if t=31 then pair tiny 1 else pair 0 0
def rawQuery (t : ℕ) : Row 128 := if t=32 then pair 1 0 else pair 0 0
def rawGate (t : ℕ) : Row 128 := fun _ => if t=31 then 0 else -40
def inputs : Tokens 128 := activate rawQuery rawKey rawGate
  (fun t => if t=15 then 3 else 0) (fun t => if t=15 then 1/65536 else 0)
  bound 0 (fun _ => 0)
def state := tokenState inputs (fun _ => 0)
def normA := Real.sqrt (1+eps)
def written := (beta*3) / normA

theorem pair_product (a b c d : ℝ) : dot (pair a b) (pair c d) = a*c + b*d := by
  rw [dot_pair]
  norm_num [pair]

theorem pair_scaled (a b m : ℝ) :
    (fun i => pair a b i * m) = pair (a*m) (b*m) := by
  funext i
  by_cases h : i=0 <;> by_cases h' : i=1 <;> simp [pair, h, h']

theorem pair_normalize (a b : ℝ) :
    Algorithm.normalize (pair a b) = pair (a / Real.sqrt (a^2+b^2+eps))
      (b / Real.sqrt (a^2+b^2+eps)) := by
  funext i
  simp only [Algorithm.normalize, pair_product, ← sq, eps]
  by_cases h : i=0 <;> by_cases h' : i=1 <;> simp [pair, h, h']

theorem pair_step (a b c d m v z : ℝ) :
    step (pair a b) (fun _ => m) (pair c d) v z =
      pair (a*m + z*(v-(a*m*c+b*m*d))*c) (b*m + z*(v-(a*m*c+b*m*d))*d) := by
  unfold step
  rw [pair_scaled]
  dsimp only
  rw [pair_product]
  funext i
  by_cases h : i=0 <;> by_cases h' : i=1 <;> simp [pair, h, h']

theorem next (t : ℕ) : state (t+1) =
    step (state t) (fun _ => if t=31 then strongDecay else weakDecay)
      (Algorithm.normalize (rawKey t)) (if t=15 then 3 else 0)
      (if t=15 then beta else 1/2) := by
  change step (state t) _ _ _ _ = _
  by_cases h : t=31 <;> by_cases h' : t=15 <;>
    simp [inputs, activate, rawGate, Algorithm.logGate, Algorithm.sigmoid,
      strongDecay, weakDecay, beta, h, h', div_eq_mul_inv] <;> norm_num

theorem zero_until (t : ℕ) (ht : t ≤ 15) : state t = pair 0 0 := by
  induction t with
  | zero => funext i; simp [state, tokenState, sequential, pair]
  | succ t ih =>
    have h : t ≠ 15 := by omega
    have h' : t ≠ 31 := by omega
    rw [next, ih (by omega)]
    simp [rawKey, h, h', pair_normalize, pair_step]

theorem first_written : state 16 = pair written 0 := by
  rw [show 16 = 15+1 from rfl, next, zero_until 15 (by decide)]
  norm_num [rawKey, pair_normalize, pair_step, written, normA, div_eq_mul_inv]

theorem before_second (j : ℕ) (hj : j ≤ 15) :
    state (16+j) = pair (written * weakDecay^j) 0 := by
  induction j with
  | zero => simpa using first_written
  | succ j ih =>
    change state ((16+j)+1) = _
    rw [next, ih (by omega)]
    have h : 16+j ≠ 15 := by omega
    have h' : 16+j ≠ 31 := by omega
    simp [rawKey, h, h', pair_normalize, pair_step, pow_succ, mul_assoc]

theorem first_coordinate :
    state 32 0 = written * weakDecay^15 * strongDecay * factor := by
  rw [show 32 = 31+1 from rfl, next, show state 31 = _ from before_second 15 (by decide)]
  norm_num [rawKey, pair_normalize, pair_step, pair]
  have normsq : (Real.sqrt (tiny^2+1+eps))^2 = tiny^2+1+eps :=
    Real.sq_sqrt (by unfold tiny eps; positivity)
  unfold factor
  field_simp
  rw [normsq, show tiny^2 + 1 + eps = 1 + eps + tiny^2 by ring]
  ring

theorem end_to_end : output inputs (fun _ => 0) 33 1 32 = answer := by
  rw [(Sequence.forward inputs _ 33 1).1 32 (by decide), one_mul]
  change dot (state (32+1)) (Algorithm.normalize (rawQuery 32)) = _
  rw [next]
  have symm (a b : Row 128) : dot a b = dot b a := by simp [dot, mul_comm]
  rw [symm]
  norm_num [rawQuery, rawKey, pair_normalize, dot_pair, step, pair]
  rw [first_coordinate]
  have h : normA^2 = 1+eps := Real.sq_sqrt (by unfold eps; positivity)
  unfold answer written
  calc
    _ = 3 * beta * weakDecay^16 * strongDecay / normA^2 * factor := by unfold normA; ring
    _ = _ := by rw [h]

/-- The correctly rounded bfloat16 answer for the measured default-state public input. -/
theorem exact_output_rounds_up :
    PTX.FloatFmt.bf16.layout.round .rn .inf (output inputs (fun _ => 0) 33 1 32) false =
      some (.fin (65/64)) := by rw [end_to_end]; exact correctly_rounded

/-- Compare the recorded public bfloat16 result with the rounded mathematical output. -/
theorem measured_output_differs :
    PTX.FloatFmt.bf16.layout.round .rn .inf (output inputs (fun _ => 0) 33 1 32) false ≠
      some (.fin (129/128)) := by rw [exact_output_rounds_up]; decide +kernel

end
end FlashKda.Stateless
