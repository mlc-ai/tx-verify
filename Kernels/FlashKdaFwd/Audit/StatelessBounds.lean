-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Algorithm
public import Core.Float.Round
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! A rational enclosure for the exact-real scalar result of the 33-token default-state probe. -/
@[expose] public section
namespace FlashKda.Stateless
open Algorithm PTX Finset
noncomputable section

def bound : ℝ := -825889/1048576
def weakDecay := Real.exp (bound * sigmoid (-40))
def strongDecay := Real.exp (bound/2)
def beta := sigmoid (1/65536)
def tiny : ℝ := 1/2^28
def eps : ℝ := 1/1000000
def factor := 1 - tiny^2 / (2*(1+eps+tiny^2))
def answer := 3*beta * weakDecay^16 * strongDecay / (1+eps) * factor

theorem strong_bounds : 674479/1000000 < strongDecay ∧ strongDecay < 674480/1000000 := by
  have h := Real.exp_bound (x := bound/2) (n := 9) (by norm_num [bound]) (by decide)
  have ha := abs_le.mp h
  norm_num [bound, sum_range_succ, Nat.factorial] at ha
  unfold strongDecay bound
  constructor <;> linarith

theorem beta_bounds : 500003/1000000 < beta ∧ beta < 500005/1000000 := by
  have h := Real.exp_bound (x := -(1/65536)) (n := 2) (by norm_num) (by decide)
  have ha := abs_le.mp h
  norm_num [sum_range_succ, Nat.factorial] at ha
  unfold beta sigmoid
  have pos : 0 < 1 + Real.exp (-(1/65536)) := by positivity
  constructor
  · apply (lt_div_iff₀ pos).mpr
    linarith
  · apply (div_lt_iff₀ pos).mpr
    linarith

theorem weak_bounds : 99999999/100000000 < weakDecay^16 ∧ weakDecay^16 ≤ 1 := by
  have he : (2:ℝ)^40 < Real.exp 40 := by
    calc
      (2:ℝ)^40 < (Real.exp 1)^40 := by gcongr; exact Real.exp_one_gt_two
      _ = Real.exp 40 := by rw [← Real.exp_nat_mul]; norm_num
  have sig : 0 < sigmoid (-40) ∧ sigmoid (-40) < 1/1000000000000 := by
    unfold sigmoid
    rw [neg_neg]
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).mpr ?_⟩
    norm_num at he
    linarith
  unfold weakDecay
  rw [← Real.exp_nat_mul]
  have lo := Real.add_one_le_exp (16*(bound*sigmoid (-40)))
  have hi : 16 * (bound * sigmoid (-40)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num [bound]) sig.1.le)
  constructor
  · unfold bound at *
    norm_num at *
    linarith
  · exact Real.exp_le_one_iff.mpr hi

theorem factor_bounds : 99999999/100000000 < factor ∧ factor ≤ 1 := by norm_num [factor, tiny, eps]

theorem interval : 259/256 < answer ∧ answer < 65/64 := by
  obtain ⟨blo, bhi⟩ := beta_bounds
  obtain ⟨wlo, whi⟩ := weak_bounds
  obtain ⟨dlo, dhi⟩ := strong_bounds
  obtain ⟨flo, fhi⟩ := factor_bounds
  have bp : 0 ≤ beta := by linarith
  have wp : 0 ≤ weakDecay^16 := by positivity
  have dp : 0 ≤ strongDecay := by linarith
  have fp : 0 ≤ factor := by linarith
  constructor
  · calc
      (259:ℝ)/256 < 3*(500003/1000000)*(99999999/100000000)*(674479/1000000) /
          (1+eps) * (99999999/100000000) := by norm_num [eps]
      _ ≤ answer := by unfold answer; gcongr <;> unfold eps <;> positivity
  · calc
      answer ≤ 3*(500005/1000000)*1*(674480/1000000)/(1+eps)*1 := by
        unfold answer
        gcongr <;> unfold eps <;> positivity
      _ < 65/64 := by norm_num [eps]

theorem correctly_rounded : (Layout.binary 8 7 true .ieee).round .rn .inf answer false =
    some (.fin (65/64)) := by
  obtain ⟨lo, hi⟩ := interval
  have pos : 0 < answer := by linarith
  rw [Layout.round_between (m := .rn) (F := 0x3f81) (by trivial) (by decide)
    (by rw [abs_of_pos pos]; norm_num [Layout.magnitude, Layout.bias]; linarith)
    (by rw [abs_of_pos pos]; norm_num [Layout.magnitude, Layout.bias]; linarith) (by simp)]
  simp only [abs_of_pos pos]
  norm_num [RoundMode.away, Layout.fieldVal, Layout.magnitude, Layout.bias]
  exact Or.inr ⟨by linarith, pos.le⟩

end
end FlashKda.Stateless
