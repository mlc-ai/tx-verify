-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Sequence
import Mathlib.Tactic

/-! Sensitivity of one real KDA update to its incoming state, and accumulation across tiles. -/
@[expose] public section
namespace FlashKda.Stability
open Chunk Sequence Algorithm Finset
noncomputable section
variable {d : ℕ}

def energy (x : Row d) : ℝ := ∑ i, x i ^ 2
def length (x : Row d) : ℝ := Real.sqrt (energy x)
def distance (x y : Row d) : ℝ := length (fun i => x i - y i)

theorem energy_nonneg (x : Row d) : 0 ≤ energy x := sum_nonneg fun _ _ => sq_nonneg _
theorem square_length (x : Row d) : length x ^ 2 = energy x := Real.sq_sqrt (energy_nonneg x)

theorem length_add (x y : Row d) :
    length (fun i => x i + y i) ≤ length x + length y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have product : dot x y ≤ length x * length y := Real.sum_mul_le_sqrt_mul_sqrt univ x y
  have expand : energy (fun i => x i + y i) = energy x + 2 * dot x y + energy y := by
    simp only [energy, dot, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [expand, add_sq, square_length, square_length]
  linarith

theorem triangle (x y z : Row d) : distance x z ≤ distance x y + distance y z := by
  have h : (fun i => x i - z i) = (fun i => (x i-y i)+(y i-z i)) := by
    funext i
    ring
  unfold distance
  rw [h]
  exact length_add _ _

theorem normalized_energy (x : Row d) : energy (Algorithm.normalize x) ≤ 1 := by
  have self : dot x x = energy x := by simp [dot, energy, pow_two]
  have nonneg := energy_nonneg x
  have denom : 0 < energy x + 1/1000000 := by linarith
  unfold energy Algorithm.normalize
  simp_rw [div_pow, self, Real.sq_sqrt denom.le]
  rw [← sum_div]
  exact (div_le_one denom).2 (by change energy x ≤ _; linarith)

theorem sigmoid_range (x : ℝ) : 0 ≤ sigmoid x ∧ sigmoid x ≤ 1 := by
  have h := Real.exp_pos (-x)
  constructor
  · unfold sigmoid
    positivity
  · unfold sigmoid
    exact (div_le_one (by positivity)).2 (by linarith)

theorem raw_decay (lower parameter : ℝ) (bias gate : Row d) (hl : lower ≤ 0) (i : Fin d) :
    0 ≤ Real.exp (logGate lower parameter bias gate i) ∧
    Real.exp (logGate lower parameter bias gate i) ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg hl (sigmoid_range _).1

/-- Subtracting an update in the key direction cannot amplify differences in entering states. -/
theorem rank_one (x key : Row d) (beta : ℝ) (hk : energy key ≤ 1)
    (hb : 0 ≤ beta) (hb' : beta ≤ 1) :
    energy (fun i => x i - beta * dot x key * key i) ≤ energy x := by
  let p := dot x key
  have expand : energy (fun i => x i - beta * p * key i) =
      energy x - 2 * beta * p * dot x key + (beta*p)^2 * energy key := by
    simp only [energy, dot, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change energy (fun i => x i - beta*p*key i) ≤ _
  rw [expand]
  change energy x - 2*beta*p*p + (beta*p)^2 * energy key ≤ _
  have factor : 0 ≤ beta * (2 - beta * energy key) :=
    mul_nonneg hb (by nlinarith [mul_le_mul_of_nonneg_left hk hb])
  nlinarith [mul_nonneg factor (sq_nonneg p)]

theorem step_nonexpansive (x y decay key : Row d) (v beta : ℝ)
    (hg : ∀ i, 0 ≤ decay i ∧ decay i ≤ 1) (hk : energy key ≤ 1)
    (hb : 0 ≤ beta ∧ beta ≤ 1) :
    distance (step x decay key v beta) (step y decay key v beta) ≤ distance x y := by
  let z := fun i => (x i-y i)*decay i
  have difference :
      dot (fun i => x i * decay i) key - dot (fun i => y i * decay i) key = dot z key := by
    unfold dot
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [z]
    ring
  have rows : (fun i => step x decay key v beta i - step y decay key v beta i) =
      (fun i => z i - beta * dot z key * key i) := by
    funext i
    rw [← difference]
    simp only [step, z]
    ring
  unfold distance length
  rw [rows]
  apply Real.sqrt_le_sqrt
  refine (rank_one z key beta hk hb.1 hb.2).trans ?_
  apply sum_le_sum
  intro i _
  dsimp [z]
  rw [mul_pow]
  have hh := mul_nonneg (hg i).1 (sub_nonneg.mpr (hg i).2)
  exact mul_le_of_le_one_right (sq_nonneg _) (by nlinarith [(hg i).2])

/-- Properties supplied by the public query/key normalization and safe gate. -/
def admissible (x : Tokens d) : Prop := ∀ t,
  (∀ i, 0 ≤ Real.exp (x.logDecay t i) ∧ Real.exp (x.logDecay t i) ≤ 1) ∧
  energy (x.key t) ≤ 1 ∧ 0 ≤ x.strength t ∧ x.strength t ≤ 1

theorem activated_admissible (q k gate : ℕ → Row d) (v logits : ℕ → ℝ)
    (lower parameter : ℝ) (bias : Row d) (hl : lower ≤ 0) :
    admissible (activate q k gate v logits lower parameter bias) := by
  intro t
  exact ⟨raw_decay lower parameter bias (gate t) hl, normalized_energy (k t),
    sigmoid_range (logits t)⟩

theorem sequence_nonexpansive (x : Tokens d) (good : admissible x) (s s' : Row d) (n : ℕ) :
    distance (tokenState x s n) (tokenState x s' n) ≤ distance s s' := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    obtain ⟨hg, hk, hb⟩ := good n
    exact (step_nonexpansive _ _ _ _ _ _ hg hk hb).trans ih

/-- The local error of a computed tile is measured against a real update from that tile's
own incoming state. This definition accepts arbitrary computed boundary states. -/
def tileError (x : Tokens d) (total : ℕ) (computed : ℕ → Row d) (b : ℕ) : ℝ :=
  distance (computed (b+1))
    (tokenState (suffix x (cursor total b)) (computed b) (liveRows total b))

/-- Numerical state errors add across tiles with coefficient one, including a short last tile. -/
theorem accumulated (x : Tokens d) (good : admissible x) (total : ℕ) (initial : Row d)
    (computed : ℕ → Row d) (blocks : ℕ) :
    distance (computed blocks) (tokenState x initial (cursor total blocks)) ≤
      distance (computed 0) initial + ∑ b ∈ range blocks, tileError x total computed b := by
  induction blocks with
  | zero => simp [cursor, tokenState, sequential]
  | succ b ih =>
    let start := cursor total b
    let count := liveRows total b
    let input := tokenState x initial start
    let next := tokenState (suffix x start) (computed b) count
    have goodSuffix : admissible (suffix x start) := fun t => good (start+t)
    have nonexp := sequence_nonexpansive (suffix x start) goodSuffix (computed b) input count
    have next_eq : tokenState (suffix x start) input count =
        tokenState x initial (cursor total (b+1)) := by
      rw [show tokenState (suffix x start) input count = tokenState x initial (start+count)
        from state_shift x initial start count, next_cursor]
    have bound := triangle (computed (b+1)) next (tokenState x initial (cursor total (b+1)))
    change distance next (tokenState (suffix x start) input count) ≤ _ at nonexp
    rw [next_eq] at nonexp
    change distance (computed b) input ≤ _ at ih
    change distance (computed (b+1)) _ ≤ tileError x total computed b + _ at bound
    rw [sum_range_succ]
    linarith

/-- With a normalized query, reading an output multiplies state error by at most |scale|. -/
theorem output_bound (x y q : Row d) (scale : ℝ) (hq : energy q ≤ 1) :
    |scale * dot x q - scale * dot y q| ≤ |scale| * distance x y := by
  let diff := fun i => x i - y i
  have linear : dot x q - dot y q = dot diff q := by
    unfold dot
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp [diff, sub_mul]
  rw [← mul_sub, abs_mul, linear]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg scale)
  have cs : (dot diff q)^2 ≤ energy diff * energy q :=
    sum_mul_sq_le_sq_mul_sq univ diff q
  have bound := cs.trans (mul_le_of_le_one_right (energy_nonneg _) hq)
  change |dot diff q| ≤ Real.sqrt (energy diff)
  apply Real.le_sqrt_of_sq_le
  simpa using bound

end
end FlashKda.Stability
