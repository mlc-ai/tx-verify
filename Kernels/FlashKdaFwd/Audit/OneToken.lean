-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Sequence
import Mathlib.Tactic

/-! Exact one-token reference on two nearly perpendicular four-component vectors. -/
@[expose] public section
namespace FlashKda.OneToken
open Chunk Sequence Algorithm Finset
noncomputable section

def four (a b c d : ℝ) : Row 128 := fun i =>
  (if i=0 then a else 0) + (if i=1 then b else 0) +
  (if i=2 then c else 0) + (if i=3 then d else 0)

theorem dot_four (a b c d : ℝ) (x : Row 128) :
    dot (four a b c d) x = a*x 0 + b*x 1 + c*x 2 + d*x 3 := by
  simp [dot, four, add_mul, ite_mul, sum_add_distrib]

def query (d : ℝ) := four 1 1 (-1) (-d)
def key (d : ℝ) := four (1/4) (1/2) (3/4) d
def tokens (d : ℝ) := activate (fun _ => query d) (fun _ => key d) (fun _ _ => 0)
  (fun _ => 1) (fun _ => 0) 0 0 (fun _ => 0)
def answer (d scale : ℝ) := output (tokens d) (fun _ => 0) 1 scale 0

/-- With zero starting state, the first output is the strength times value times the normalized
key-query inner product, with output scaling. -/
theorem single {dim : Nat} (x : Tokens dim) (scale : ℝ) :
    output x (fun _ => 0) 1 scale 0 =
      scale * (x.strength 0 * x.value 0) * dot (x.key 0) (x.query 0) := by
  rw [(forward x _ 1 scale).1 0 (by decide)]
  simp [tokenState, sequential, step, dot, mul_assoc, ← mul_sum]

theorem normalize_dot {dim : Nat} (k q : Row dim) :
    dot (normalize k) (normalize q) =
      dot k q / (Real.sqrt (dot k k+1/1000000) * Real.sqrt (dot q q+1/1000000)) := by
  unfold Algorithm.normalize
  simp only [dot, div_mul_div_comm, ← sum_div]

theorem dots (d : ℝ) :
    dot (key d) (query d) = -d^2 ∧ dot (key d) (key d) = 7/8+d^2 ∧
    dot (query d) (query d) = 3+d^2 := by
  unfold key query
  simp only [dot_four]
  norm_num [four]
  ring

theorem real_answer (d scale : ℝ) :
    answer d scale = -scale*d^2 /
      (2 * Real.sqrt (7/8+d^2+1/1000000) * Real.sqrt (3+d^2+1/1000000)) := by
  rw [answer, single]
  simp only [tokens, activate, sigmoid, neg_zero, Real.exp_zero, normalize_dot,
    (dots d).1, (dots d).2.1, (dots d).2.2]
  ring

theorem zero_exact (scale : ℝ) : answer 0 scale = 0 := by rw [real_answer]; simp

theorem negative {d scale : ℝ} (hd : 0 < d) (hs : 0 < scale) : answer d scale < 0 := by
  rw [real_answer]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) (by positivity))
    (by positivity)

/-- On the observed one-token, default-state input the real answer is nonzero, and the
observed positive output gives relative error above one. -/
theorem sign_error {d scale measured : ℝ} (hd : 0 < d) (hs : 0 < scale) (hm : 0 < measured) :
    1 < |measured - answer d scale| / |answer d scale| := by
  have hx := negative hd hs
  rw [abs_of_neg hx, abs_of_pos (by linarith), lt_div_iff₀ (by linarith)]
  linarith

end
end FlashKda.OneToken
