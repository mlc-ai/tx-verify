-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.InverseStability
public import Kernels.FlashKdaFwd.Proof.OperandRound
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! Error budgets for the key products that build the unit-lower triangular system. -/
@[expose] public section
namespace FlashKda.Seed
open Matrix Finset Chunk Block Algorithm Stability Sequence Inverse InverseStability
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {d : ℕ}

theorem cumulative_antitone (x : Tokens d) (good : admissible x) (i : Fin d) :
    Antitone (fun t => cum x.logDecay t i) := by
  apply antitone_nat_of_succ_le
  intro t
  simp only [cum, sum_range_succ, Real.exp_add]
  exact mul_le_of_le_one_right (Real.exp_pos _).le ((good t).1 i).2

/-- The large restored factor and small decayed factor cancel in the absolute product
sum for a *causal* dot product. This also covers arbitrary coordinatewise decays. -/
theorem absolute_products (x : Tokens d) (good : admissible x) {j t : ℕ} (ht : j ≤ t) :
    ∑ i, |restored (cum x.logDecay) x.key j i * weighted (cum x.logDecay) x.key t i| ≤ 1 := by
  let p := cum x.logDecay
  have hp (n i) : 0 < p n i := Real.exp_pos _
  have causal (i) : p (t+1) i / p (j+1) i ≤ 1 :=
    (div_le_one (hp _ _)).2 (cumulative_antitone x good i (by omega))
  calc
    _ ≤ ∑ i, |x.key j i| * |x.key t i| := by
      apply sum_le_sum
      intro i _
      have h : |restored p x.key j i * weighted p x.key t i| =
          p (t+1) i / p (j+1) i * (|x.key j i| * |x.key t i|) := by
        simp only [restored, weighted, abs_mul, abs_div, abs_of_pos (hp _ _)]
        ring
      rw [h]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (causal i)
    _ ≤ length (x.key j) * length (x.key t) := by
      simpa [length, energy, sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt univ
        (fun i => |x.key j i|) (fun i => |x.key t i|)
    _ ≤ 1 := by
      have small (n) : length (x.key n) ≤ 1 :=
        Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa using (good n).2.1⟩
      simpa using mul_le_mul (small j) (small t) (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

/-- Relative operand errors produce an absolute computed-dot error even near cancellation. -/
theorem dot_round (a b a' b' : Row d) {e : ℝ} (he : 0 ≤ e)
    (ha : ∀ i, |a' i-a i| ≤ e*|a i|) (hb : ∀ i, |b' i-b i| ≤ e*|b i|) :
    |dot a' b' - dot a b| ≤ (2*e+e^2) * ∑ i, |a i*b i| := by
  unfold dot
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro i _
  let da := a' i-a i
  let db := b' i-b i
  have id : a' i*b' i-a i*b i = da*db + da*b i + a i*db := by dsimp [da,db]; ring
  have prod := mul_le_mul (ha i) (hb i) (abs_nonneg _) (mul_nonneg he (abs_nonneg _))
  have left := mul_le_mul_of_nonneg_right (ha i) (abs_nonneg (b i))
  have right := mul_le_mul_of_nonneg_left (hb i) (abs_nonneg (a i))
  rw [id]
  calc
    _ ≤ |da*db| + |da*b i| + |a i*db| := (abs_add_le ..).trans
      (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ _ := by simp only [abs_mul,da,db]; nlinarith only [prod,left,right]

/-- The seed at a strict-lower position: operand formation and the remaining dot/gate
arithmetic have independent error budgets. -/
theorem entry (x : Tokens d) (good : admissible x) {j t : ℕ} (ht : j < t)
    (a' b' : Row d) {e eta observed : ℝ} (he : 0 ≤ e)
    (ha : ∀ i, let a := restored (cum x.logDecay) x.key j i; |a' i-a| ≤ e*|a|)
    (hb : ∀ i, let b := weighted (cum x.logDecay) x.key t i; |b' i-b| ≤ e*|b|)
    (hm : |observed-x.strength t*dot a' b'| ≤ eta) :
    |observed-lower x t j| ≤ eta+(2*e+e^2) := by
  have dotErr := (dot_round _ _ a' b' he ha hb).trans
    (mul_le_mul_of_nonneg_left (absolute_products x good ht.le) (by positivity))
  have scaled := mul_le_mul_of_nonneg_left dotErr (good t).2.2.1
  have cap := mul_le_of_le_one_left (by positivity : 0 ≤ 2*e+e^2) (good t).2.2.2
  have split := abs_sub_le observed (x.strength t*dot a' b') (lower x t j)
  simp only [lower, coefficient, ← mul_sub, abs_mul, abs_of_nonneg (good t).2.2.1] at split
  rw [mul_one] at scaled
  exact split.trans (add_le_add hm (scaled.trans cap))

/-- A dot of two nearest-even bfloat16 conversions of zero or normal real operands.
The budget eta covers the subsequent dot product and multiplication by the token strength. -/
theorem converted_entry (x : Tokens d) (good : admissible x) {j t : ℕ} (ht : j < t)
    (a' b' : Fin d → ℚ) {eta observed : ℝ}
    (ha : ∀ i, let a := restored (cum x.logDecay) x.key j i
      OperandRound.inRange a ∧ OperandRound.rounded a = some (a' i))
    (hb : ∀ i, let b := weighted (cum x.logDecay) x.key t i
      OperandRound.inRange b ∧ OperandRound.rounded b = some (b' i))
    (hm : |observed-x.strength t*dot (fun i => (a' i : ℝ)) (fun i => (b' i : ℝ))| ≤ eta) :
    |observed-lower x t j| ≤ eta+(2*(1/256)+(1/256)^2) := by
  have bound (z : ℝ) (w : ℚ) (h : OperandRound.inRange z ∧ OperandRound.rounded z = some w) :
      |(w:ℝ)-z| ≤ (1/256)*|z| := by
    obtain ⟨y, eq, le⟩ := OperandRound.value z h.1
    rw [h.2] at eq
    exact Option.some.inj eq ▸ le
  exact entry x good ht _ _ (by norm_num : (0:ℝ) ≤ 1/256)
    (fun i => bound _ _ (ha i)) (fun i => bound _ _ (hb i)) hm

theorem norm_sq (m : Matrix Full Full ℝ) :
    ‖m‖^2 = ∑ i, ∑ j, (m i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  exact Real.sq_sqrt (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)

theorem strict_lower_norm (m : Matrix Full Full ℝ) {e : ℝ}
    (below : ∀ i j, j < i → |m i j| ≤ e) (above : ∀ i j, i ≤ j → m i j = 0) :
    ‖m‖^2 ≤ 120*e^2 := by
  have count : (∑ i : Full, ∑ j : Full, (if j < i then 1 else 0 : ℕ)) = 120 := by decide +kernel
  have realCount : (∑ i : Full, ∑ j : Full, (if j < i then 1 else 0 : ℝ)) = 120 := by
    exact_mod_cast count
  rw [norm_sq, ← realCount, sum_mul]
  apply sum_le_sum
  intro i _
  rw [sum_mul]
  apply sum_le_sum
  intro j _
  by_cases h : j < i
  · simp only [ite_eq_left h, one_mul]
    exact (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (below i j h))).2
      (below i j h) |> fun hh => by simpa using hh
  · simp [h, above i j (le_of_not_gt h)]

/-- A per-entry absolute error of at most 1/1024 beyond two operand errors of 1/256
moves the entire triangular seed by less than one tenth in Frobenius norm. -/
theorem seed_budget (x : Tokens d) (m : Matrix Full Full ℝ)
    (below : ∀ i j : Full, j < i →
      |m i j - lower x i j| ≤ 1/1024 + (2*(1/256)+(1/256)^2))
    (above : ∀ i j : Full, i ≤ j → m i j = delta i j) :
    ‖m-system 16 (lower x)‖ < 1/10 := by
  have h := strict_lower_norm (m-system 16 (lower x))
    (e := 1/1024 + (2*(1/256)+(1/256)^2))
    (fun i j h => by simpa [system,h] using below i j h)
    (fun i j h => by simp [system, show ¬(j.val < i.val) from not_lt.mpr h, above i j h])
  nlinarith only [h, norm_nonneg (m-system 16 (lower x))]

theorem exact_inverse_norm (x : Tokens d) (good : admissible x) :
    ‖blockInverse (lower x)‖ ≤ √31 := by
  have h := frobenius_squared x good
  rw [← norm_sq] at h
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 31)
  nlinarith [Real.sqrt_nonneg (31:ℝ)]

set_option maxHeartbeats 800000 in
/-- Perturbation of the computed inverse, using only the seed error and the residual of
inversion of that seed. The spectral norm is bounded by this Frobenius guarantee as well. -/
theorem perturb (x : Tokens d) (good : admissible x) (m j : Matrix Full Full ℝ) {e eta : ℝ}
    (seed : ‖m-system 16 (lower x)‖ ≤ e) (solve : ‖m*j-1‖ ≤ eta) (small : √31*e < 1) :
    ‖j-blockInverse (lower x)‖ ≤ (√31*eta + 31*e)/(1-√31*e) := by
  let a := system 16 (lower x)
  let v := blockInverse (lower x)
  have left : v*a = 1 := mul_eq_one_comm.mp (right_inverse _)
  have diff : j-v = v*((m*j-1) + (a-m)*j) := by
    rw [show (m*j-1)+(a-m)*j = a*j-1 by rw [sub_mul]; abel]
    rw [mul_sub, ← Matrix.mul_assoc, left, one_mul, mul_one]
  have ne : 0 ≤ e := (norm_nonneg _).trans seed
  have rev : ‖a-m‖ ≤ e := by rw [norm_sub_rev]; exact seed
  have h1 : ‖j-v‖ ≤ √31*(eta + e*‖j‖) := calc
    _ = _ := congrArg norm diff
    _ ≤ _ := (Matrix.frobenius_norm_mul ..).trans (mul_le_mul (exact_inverse_norm x good)
      ((norm_add_le ..).trans (add_le_add solve ((Matrix.frobenius_norm_mul ..).trans
        (mul_le_mul_of_nonneg_right rev (norm_nonneg _))))) (norm_nonneg _) (Real.sqrt_nonneg _))
  have h2 : ‖j‖ ≤ ‖j-v‖ + √31 := by
    calc
      _ = ‖(j-v)+v‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le (j-v) v).trans (add_le_add le_rfl (exact_inverse_norm x good))
  have mono := mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.sqrt_nonneg 31) ne)
  have root := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 31)
  apply (le_div_iff₀ (by linarith)).2
  change ‖j-v‖ * (1-√31*e) ≤ _
  have cross : e * (√31)^2 = e*31 := congrArg (e * ·) root
  nlinarith only [h1,mono,cross]

/-- With seed error at most 1/10, the exact inverse of the perturbed seed has norm below 13. -/
theorem perturbed_inverse_norm (x : Tokens d) (good : admissible x) (m j : Matrix Full Full ℝ)
    (seed : ‖m-system 16 (lower x)‖ ≤ 1/10) (solve : m*j = 1) :
    ‖j‖ < 13 := by
  have root : √(31:ℝ) < 28/5 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have small : √(31:ℝ)*(1/10) < 1 := by linarith
  have h := perturb x good m j seed (eta := 0) (by simp [solve]) small
  have cap : (√(31:ℝ)*0 + 31*(1/10))/(1-√31*(1/10)) < 71/10 := by
    apply (div_lt_iff₀ (by linarith)).2
    linarith
  have v := exact_inverse_norm x good
  have total := norm_add_le (j-blockInverse (lower x)) (blockInverse (lower x))
  rw [sub_add_cancel] at total
  linarith

end
end FlashKda.Seed
