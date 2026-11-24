-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.InverseStability
import Mathlib.Tactic

/-! Transfer numerical defects to perturbations of the input values. Their gate-weighted
squared magnitudes add across the whole sequence, including across block boundaries. -/
@[expose] public section
namespace FlashKda.ValuePerturbation
open Chunk Sequence Algorithm Stability Residual Finset
noncomputable section
variable {d : ℕ}

/-- Input values receive additive perturbations; the preparation keys and gates stay fixed. -/
def shifted (x : Tokens d) (w : ℕ → ℝ) : Tokens d :=
  {x with value := fun t => x.value t + w t}

def cost (x : Tokens d) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, x.strength t * (w t)^2

/-- One KDA update stores part of the perturbation and dissipates the prior key prediction. -/
theorem update_energy (z k : Row d) (b w : ℝ) (hb : 0 ≤ b) (hk : b * energy k ≤ 1) :
    energy (fun i => z i + b*(w-dot z k)*k i) + b*(dot z k)^2 ≤ energy z + b*w^2 := by
  let a := b*(w-dot z k)
  have expand : energy (fun i => z i + a*k i) = energy z + 2*a*dot z k + a^2*energy k := by
    simp only [energy, dot, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  change energy (fun i => z i + a*k i) + _ ≤ _
  rw [expand]
  have h := mul_le_mul_of_nonneg_left hk (mul_nonneg hb (sq_nonneg (w-dot z k)))
  dsimp [a]
  nlinarith only [h]

private theorem step_bound (x : Tokens d) (good : admissible x) (w : ℕ → ℝ)
    (s' s : Row d) (t : ℕ) :
    let decay := fun i => Real.exp (x.logDecay t i)
    distance (step s' decay (x.key t) (x.value t+w t) (x.strength t))
      (step s decay (x.key t) (x.value t) (x.strength t)) ^ 2 ≤
        distance s' s ^ 2 + x.strength t*(w t)^2 := by
  let diff := fun i => s' i - s i
  let z := decayed x diff t
  have projection : dot (decayed x s' t) (x.key t) - dot (decayed x s t) (x.key t) =
      dot z (x.key t) := by
    simp only [dot, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [decayed,z,diff]
    ring
  obtain ⟨_,key,low,high⟩ := good t
  have h := update_energy z (x.key t) (x.strength t) (w t) low
    ((mul_le_mul_of_nonneg_left key low).trans (by simpa using high))
  have difference : (fun i => step s' (fun j => Real.exp (x.logDecay t j))
      (x.key t) (x.value t+w t) (x.strength t) i -
      step s (fun j => Real.exp (x.logDecay t j)) (x.key t) (x.value t) (x.strength t) i) =
      fun i => z i + x.strength t*(w t - dot z (x.key t))*x.key t i := by
    funext i
    rw [← projection]
    simp only [step, z, dot, decayed, diff]
    ring
  dsimp only
  simp only [distance, square_length, difference]
  have atten := InverseStability.shrink x good diff t
  change energy z ≤ energy diff at atten
  change _ ≤ energy diff + _
  linarith only [h, atten, mul_nonneg low (sq_nonneg (dot z (x.key t)))]

/-- One bound on the error from all additive value perturbations up to this token. -/
theorem states (x : Tokens d) (good : admissible x) (w : ℕ → ℝ)
    (first initial : Row d) (n : ℕ) :
    distance (tokenState (shifted x w) first n) (tokenState x initial n) ≤
      √(distance first initial ^ 2 + cost x w n) := by
  apply Real.le_sqrt_of_sq_le
  induction n with
  | zero => simp [tokenState, sequential, cost]
  | succ n ih =>
    have h := step_bound x good w (tokenState (shifted x w) first n) (tokenState x initial n) n
    change distance (tokenState (shifted x w) first (n+1)) (tokenState x initial (n+1))^2 ≤ _ at h
    rw [cost, sum_range_succ]
    change _ ≤ _ + (cost x w n + _)
    linarith

/-- Within a tile the remaining scalar residual is determined exactly by the chosen shifts. -/
theorem remainder (x : Tokens d) (w : ℕ → ℝ) (s : Row d) (u : ℕ → ℝ) (offset t : ℕ) :
    residual (suffix (shifted x w) offset) s u t =
      residual (suffix x offset) s u t - x.strength (offset+t)*w (offset+t) := by
  simp only [Residual.residual, suffix, shifted]
  ring

/-- An arbitrary reported output is controlled by the remaining tile defects, boundary stores,
and a single square root over the initial state difference and all preceding value shifts. -/
theorem outputs (x : Tokens d) (good : admissible x) (hq : ∀ t, energy (x.query t) ≤ 1)
    (w : ℕ → ℝ) (total : ℕ) (initial : Row d) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (o : ℕ → ℝ) (scale : ℝ) {t : ℕ} (ht : t < total) :
    |o t - output x initial total scale t| ≤
      outputBound (shifted x w) total (c 0) c u o scale t +
      |scale| * √(distance (c 0) initial ^ 2 + cost x w (t+1)) := by
  let y := shifted x w
  have a := Residual.outputs y good hq total (c 0) c u o scale ht
  have b := output_bound (tokenState y (c 0) (t+1)) (tokenState x initial (t+1))
    (x.query t) scale (hq t)
  have bound := b.trans (mul_le_mul_of_nonneg_left (states x good w (c 0) initial (t+1))
    (abs_nonneg scale))
  have e := abs_sub_le (o t) (output y (c 0) total scale t) (output x initial total scale t)
  apply e.trans
  apply add_le_add a
  rw [(forward y (c 0) total scale).1 t ht, (forward x initial total scale).1 t ht]
  exact bound

theorem final_state (x : Tokens d) (good : admissible x) (w : ℕ → ℝ) (total : ℕ)
    (initial : Row d) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) :
    distance (c ((total+15)/16)) (tokenState x initial total) ≤
      boundaryBound (shifted x w) total (c 0) c u ((total+15)/16) +
      √(distance (c 0) initial ^ 2 + cost x w total) := by
  exact (triangle _ (tokenState (shifted x w) (c 0) total) _).trans
    (add_le_add (Residual.final_state (shifted x w) good total (c 0) c u)
      (states x good w (c 0) initial total))

/-- One residual per live token in global time order. -/
def atToken (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (t : ℕ) :=
  let b := t/16
  Residual.residual (suffix x (cursor total b)) (c b) (u b) (t%16)

def charge (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (n : ℕ) :=
  ∑ t ∈ range n, (atToken x total c u t)^2 / x.strength t

def gaps (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (blocks : ℕ) :=
  ∑ b ∈ range blocks, exitGap x total c u b

def shifts (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (t : ℕ) :=
  atToken x total c u t / x.strength t

private theorem shifts_cost (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (pos : ∀ t < total, 0 < x.strength t) {n : ℕ} (hn : n ≤ total) :
    cost x (shifts x total c u) n = charge x total c u n := by
  apply sum_congr rfl
  intro t ht
  have nz := (pos t (lt_of_lt_of_le (mem_range.mp ht) hn)).ne'
  simp only [shifts, div_pow]
  field_simp

private theorem no_remainder (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (pos : ∀ t < total, 0 < x.strength t) (b n : ℕ) (hn : n ≤ liveRows total b) :
    solveError (suffix (shifted x (shifts x total c u)) (cursor total b)) (c b) (u b) n = 0 := by
  apply sum_eq_zero
  intro t ht
  have live := lt_of_lt_of_le (mem_range.mp ht) hn
  unfold liveRows cursor at live
  have start : cursor total b = 16*b := by unfold cursor; omega
  have index : cursor total b + t < total := by rw [start]; omega
  have block : (cursor total b+t)/16=b := by rw [start]; omega
  have row : (cursor total b+t)%16=t := by rw [start]; omega
  have nz := (pos _ index).ne'
  have cancel (a : ℝ) : x.strength (cursor total b+t) * (a/x.strength (cursor total b+t)) = a :=
    by field_simp
  simp only [remainder, shifts, atToken, block, row, cancel,
    sub_self, abs_zero, zero_mul]

private theorem boundaries_eq (x : Tokens d) (total : ℕ) (c : ℕ → Row d) (u : ℕ → ℕ → ℝ)
    (pos : ∀ t < total, 0 < x.strength t) (b : ℕ) :
    boundaryBound (shifted x (shifts x total c u)) total (c 0) c u b = gaps x total c u b := by
  have zero : distance (c 0) (c 0) = 0 := by simp [distance, length, energy]
  simp only [boundaryBound, zero, zero_add, no_remainder x total c u pos _ _ le_rfl, add_zero]
  rfl

/-- Accumulation directly in terms of observed correction residuals, with one global square
root, measured carry gaps, and the observed readout gap. Positive strengths suffice on live rows. -/
theorem forward (x : Tokens d) (good : admissible x) (hq : ∀ t, energy (x.query t) ≤ 1)
    (total : ℕ) (pos : ∀ t < total, 0 < x.strength t) (initial : Row d)
    (c : ℕ → Row d) (u : ℕ → ℕ → ℝ) (o : ℕ → ℝ) (scale : ℝ) :
    (∀ t < total,
      let b := t/16
      let s := state (suffix x (cursor total b)) (c b) (u b) (t%16+1)
      |o t - output x initial total scale t| ≤ |o t - scale*dot s (x.query t)| +
        |scale| * (gaps x total c u b + √(distance (c 0) initial ^ 2 + charge x total c u (t+1))))
    ∧ distance (c ((total+15)/16)) (tokenState x initial total) ≤
      gaps x total c u ((total+15)/16) +
        √(distance (c 0) initial ^ 2 + charge x total c u total) := by
  constructor
  · intro t ht
    have live : t%16+1 ≤ liveRows total (t/16) := by unfold liveRows cursor; omega
    have h := outputs x good hq (shifts x total c u) total initial c u o scale ht
    simp only [outputBound, boundaries_eq x total c u pos,
      no_remainder x total c u pos _ _ live, add_zero, shifts_cost x total c u pos ht] at h
    dsimp only
    rw [mul_add, ← add_assoc]
    exact h
  · have h := final_state x good (shifts x total c u) total initial c u
    rwa [boundaries_eq x total c u pos, shifts_cost x total c u pos le_rfl] at h

/-- Every finite real raw strength logit supplies the strict-positivity premise. -/
theorem positive_strength (q k gate : ℕ → Row d) (v logits : ℕ → ℝ) (lower parameter : ℝ)
    (bias : Row d) (t : ℕ) : 0 < (activate q k gate v logits lower parameter bias).strength t := by
  change 0 < 1 / (1 + Real.exp _)
  positivity

end
end FlashKda.ValuePerturbation
