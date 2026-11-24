-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.StatelessForward
import Kernels.FlashKdaFwd.Audit.OneTokenRound
import Kernels.FlashKdaFwd.Audit.ResidualSample

/-! Both published output comparisons on the two-head finite input. The device and the
references supply the observed words. The dense tensor norm includes every output coordinate. -/
namespace FlashKda.Criteria
open Sequence Chunk Algorithm Finset
noncomputable section

def pattern (first last : ℝ) (t : ℕ) (h : Fin 2) (v : Fin 128) : ℝ :=
  if t=0 then (if h=1 then first else 0)
  else if t=32 ∧ h=0 ∧ v=0 then last else 0

def kernel := pattern (69/256) (129/128)
def mixed := pattern (69/256) (65/64)
def gold := pattern (-10105/32768) (1060871/1048576)
def tensorEnergy (n : ℕ) (o : ℕ → Fin 2 → Fin 128 → ℝ) :=
  ∑ t ∈ range n, ∑ h, ∑ v, (o t h v)^2
def rms (n : ℕ) (o : ℕ → Fin 2 → Fin 128 → ℝ) :=
  √(tensorEnergy n o / (n*256 : ℝ))
def ratio (n : ℕ) (ref actual : ℕ → Fin 2 → Fin 128 → ℝ) :=
  rms n (ref-actual) / (rms n ref + 1/100000000)
def squares (a b : ℝ) := 128*a^2 + b^2

theorem words :
    PTX.f32Value 0x3e8a0000 = some (69/256) ∧ PTX.f32Value 0x3f810000 = some (129/128) ∧
    PTX.f32Value 0x3f820000 = some (65/64) ∧ PTX.f32Value 0xbe9de400 = some (-10105/32768) ∧
    PTX.f32Value 0x3f818038 = some (1060871/1048576) := by decide +kernel

theorem exact_disagrees : kernel 32 0 0 ≠ mixed 32 0 0 := by norm_num [kernel, mixed, pattern]

theorem sub_pattern (a b c d : ℝ) : pattern a b - pattern c d = pattern (a-c) (b-d) := by
  funext t h v
  simp only [Pi.sub_apply, pattern]
  split_ifs <;> simp

theorem energy_pattern {n : ℕ} (hn : 32 < n) (a b : ℝ) :
    tensorEnergy n (pattern a b) = squares a b := by
  have row (t : ℕ) :
      ∑ h, ∑ v, (pattern a b t h v)^2 =
        (if t=0 then 128*a^2 else 0) + (if t=32 then b^2 else 0) := by
    by_cases h0 : t=0
    · subst t
      simp [pattern]
    by_cases h32 : t=32
    · subst t
      simp [pattern, Fin.sum_univ_two, ite_pow]
    · simp [pattern, h0, h32]
  simp only [tensorEnergy, row, sum_add_distrib]
  simp [squares, hn, show 0 < n by omega]

theorem ratio_pattern {n : ℕ} (hn : 32 < n) (a b c d : ℝ) :
    ratio n (pattern a b) (pattern c d) =
    √(squares (a-c) (b-d)) /
      (√(squares a b) + √(n*256 : ℝ)/100000000) := by
  have hp : 0 < (n*256 : ℝ) := mul_pos (by exact_mod_cast (by omega : 0 < n)) (by norm_num)
  have hr := Real.sqrt_pos.mpr hp
  have split (p q : ℝ) := Real.sqrt_div
    (by unfold squares; positivity : 0 ≤ squares p q) (n*256 : ℝ)
  simp only [ratio, rms, sub_pattern, energy_pattern hn, split]
  have hnz : √(n*256 : ℝ) ≠ 0 := ne_of_gt hr
  field_simp

/-- This enclosure covers both the independent recurrence and the recorded FLA result. -/
theorem rejects {n : ℕ} (hn : 32 < n) (hmax : n ≤ 34) {a b d : ℝ}
    (ha : -31/100 ≤ a ∧ a ≤ -307/1000) (hb : 1 ≤ b ∧ b ≤ 102/100) :
    3/10 < |a - 69/256| ∧ 7/4 < ratio n (pattern a b) (pattern (69/256) d) := by
  constructor
  · rw [abs_of_neg (by linarith : a-69/256 < 0)]
    linarith
  rw [ratio_pattern hn]
  have ea := sq_le_sq' (b := (31/100 : ℝ)) (by linarith : -(31/100) ≤ a) (by linarith)
  have eb := sq_le_sq' (b := (102/100 : ℝ)) (by linarith : -(102/100) ≤ b) hb.2
  have err : 65/10 < √(squares (a-69/256) (b-d)) := by
    apply Real.lt_sqrt_of_sq_lt
    have large := (sq_le_sq₀ (by norm_num : 0 ≤ (576/1000 : ℝ))
      (by linarith : 0 ≤ -(a-69/256))).2 (by linarith)
    unfold squares
    nlinarith only [large, sq_nonneg (b-d)]
  have base : √(squares a b) < 366/100 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    unfold squares
    nlinarith
  have tailBound : √(n*256 : ℝ) ≤ 100 := by
    apply Real.sqrt_le_iff.mpr
    have h : (n : ℝ) ≤ 34 := by exact_mod_cast hmax
    exact ⟨by norm_num, by linarith⟩
  have pn : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (lt_div_iff₀ (by positivity)).2
  linarith

theorem measured_rejected {n : ℕ} (hn : 32 < n) (hmax : n ≤ 34) :
    kernel 32 0 0 ≠ mixed 32 0 0 ∧
    3/10 < |gold 0 1 0 - kernel 0 1 0| ∧ 7/4 < ratio n gold kernel :=
  ⟨exact_disagrees, rejects (a := -10105/32768) (b := 1060871/1048576) hn hmax
    (by norm_num) (by norm_num)⟩

/-- Elementwise equality is required only at the live coordinates of this call. -/
def agrees (n : ℕ) (x y : ℕ → Fin 2 → Fin 128 → ℝ) : Prop :=
  ∀ t < n, ∀ h v, x t h v = y t h v

/-- The default output assertion accepts small absolute error or the requested RMS ratio.
Continuous integration also accepts a one-percent ratio or a 0.3 absolute error. -/
def accepts (n : ℕ) (ref pred : ℕ → Fin 2 → Fin 128 → ℝ) (limit : ℝ) (ci : Bool) : Prop :=
  (∀ t < n, ∀ h v, |ref t h v - pred t h v| ≤ 1/1000000) ∨
  ratio n ref pred < limit ∨
  (ci = true ∧ (ratio n ref pred < 1/100 ∨
    ∀ t < n, ∀ h v, |ref t h v - pred t h v| ≤ 3/10))

theorem ratio_congr {n : ℕ} {ref x y : ℕ → Fin 2 → Fin 128 → ℝ} (equal : agrees n x y) :
    ratio n ref x = ratio n ref y := by
  have he : tensorEnergy n (ref-x) = tensorEnergy n (ref-y) := by
    apply sum_congr rfl
    intro t ht
    have row := funext fun h => funext (equal t (mem_range.mp ht) h)
    simp only [Pi.sub_apply, row]
  simp only [ratio, rms, he]

/-- No output on the recorded finite input can pass both upstream comparisons, including
the absolute-error and continuous-integration exceptions in the upstream assertion. -/
theorem incompatible {n : ℕ} (hn : 32 < n) (hmax : n ≤ 34) {limit : ℝ}
    (hl : limit ≤ 1/100) (ci : Bool) :
    ¬ ∃ pred, agrees n pred mixed ∧ accepts n gold pred limit ci := by
  rintro ⟨pred, equal, passed⟩
  have h0 : 0 < n := by omega
  have bad := rejects (a := -10105/32768) (b := 1060871/1048576) (d := 65/64)
    hn hmax (by norm_num) (by norm_num)
  have rr : 7/4 < ratio n gold pred := by rw [ratio_congr equal]; exact bad.2
  have ab : 3/10 < |gold 0 1 0 - pred 0 1 0| := by
    rw [equal 0 h0 1 0]
    simpa [gold, mixed, pattern] using bad.1
  rcases passed with all | rat | ⟨_, rat | all⟩
  · linarith [all 0 h0 1 0]
  · linarith
  · linarith
  · linarith [all 0 h0 1 0]

theorem upstream_incompatible (ci : Bool) :
    (¬ ∃ pred, agrees 33 pred mixed ∧ accepts 33 gold pred (5/1000) ci) ∧
    (¬ ∃ pred, agrees 34 pred mixed ∧ accepts 34 gold pred (6/1000) ci) :=
  ⟨incompatible (by decide) (by decide) (by norm_num) ci,
    incompatible (by decide) (by decide) (by norm_num) ci⟩

/-- The real answer at token zero does not depend on gates that multiply a zero initial state. -/
def secondHead : Tokens 128 := activate
  (fun t => if t=0 then OneToken.query (1/32) else fun _ => 0)
  (fun t => if t=0 then OneToken.key (1/32) else fun _ => 0)
  (fun _ _ => -40) (fun t => if t=0 then 1024 else 0) (fun _ => 0)
  Stateless.bound 0 (fun _ => 0)

def realFirst := 1024 * OneToken.answer (1/32) 1

theorem first_output : output secondHead (fun _ => 0) 33 1 0 = realFirst := by
  have one := (forward secondHead (fun _ => 0) 1 1).1 0 (by decide)
  rw [(forward secondHead (fun _ => 0) 33 1).1 0 (by decide), ← one, OneToken.single]
  unfold realFirst OneToken.answer
  rw [OneToken.single]
  norm_num [secondHead, activate, OneToken.tokens, Algorithm.sigmoid]
  ring

def head (h : Fin 2) (v : Fin 128) :=
  if h=1 then secondHead else if v=0 then Stateless.inputs
  else {Stateless.inputs with value := fun _ => 0}

/-- Remaining time slots in a packed second sequence have zero queries. -/
def ideal (t : ℕ) (h : Fin 2) (v : Fin 128) :=
  if t < 33 then output (head h v) (fun _ => 0) 33 1 t else 0

theorem ideal_pattern : ideal = pattern realFirst Stateless.answer := by
  funext t h v
  by_cases lt : t < 33
  · simp only [ideal, ite_eq_left lt]
    by_cases h1 : h=1
    · simp only [head, ite_eq_left h1]
      by_cases t0 : t=0
      · subst t
        simp [first_output, pattern, h1]
      · rw [(forward secondHead (fun _ => 0) 33 1).1 t lt]
        simp [pattern, t0, h1, secondHead, activate, Algorithm.normalize, dot]
    · have hh : h=0 := by omega
      subst h
      by_cases v0 : v=0
      · subst v
        simp only [head, show ¬(0 : Fin 2)=1 by decide, ite_false, ite_true]
        by_cases t32 : t=32
        · subst t
          simpa [pattern] using Stateless.end_to_end
        · rw [(forward Stateless.inputs (fun _ => 0) 33 1).1 t lt]
          simp [Stateless.inputs, activate, Stateless.rawQuery, t32, pattern, Algorithm.normalize,
            dot, Cancellation.pair]
      · have hz := (Sample.zero_channels {Stateless.inputs with value := fun _ => 0}
          (fun _ => rfl)).2 33 t lt
        simpa [head, v0, pattern, show ¬(0 : Fin 2)=1 by decide] using hz
  · simp [ideal, lt, pattern, show t ≠ 0 by omega, show t ≠ 32 by omega]

theorem real_bounds : -31/100 ≤ realFirst ∧ realFirst ≤ -307/1000 := by
  unfold realFirst
  rw [OneToken.real_answer]
  let q := √(3+(1/32 : ℝ)^2+1/1000000)
  let k := √(7/8+(1/32 : ℝ)^2+1/1000000)
  have qlo : 1732/1000 < q := Real.lt_sqrt_of_sq_lt (by norm_num)
  have qhi : q < 1733/1000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have klo : 935/1000 < k := Real.lt_sqrt_of_sq_lt (by norm_num)
  have khi : k < 937/1000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have lo := mul_lt_mul_of_pos_right qlo (by linarith : 0 < k)
  have lo' := mul_lt_mul_of_pos_left klo (by norm_num : (0:ℝ) < 1732/1000)
  have hi := mul_lt_mul_of_pos_right qhi (by linarith : 0 < k)
  have hi' := mul_lt_mul_of_pos_left khi (by norm_num : (0:ℝ) < 1733/1000)
  change -31/100 ≤ 1024 * (-(1:ℝ)*(1/32)^2 / (2*k*q)) ∧
    1024 * (-(1:ℝ)*(1/32)^2 / (2*k*q)) ≤ -307/1000
  have pos : 0 < 2*k*q := by dsimp [k,q]; positivity
  simp only [← mul_div_assoc, le_div_iff₀ pos, div_le_iff₀ pos]
  constructor <;> nlinarith

theorem real_rejected {n : ℕ} (hn : 32 < n) (hmax : n ≤ 34) :
    3/10 < |ideal 0 1 0 - kernel 0 1 0| ∧ 7/4 < ratio n ideal kernel := by
  rw [ideal_pattern]
  apply rejects hn hmax real_bounds
  obtain ⟨lo,hi⟩ := Stateless.interval
  constructor <;> linarith

end
end FlashKda.Criteria
