-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Proof.Softmax.BiasMaxValue
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarr1Kinds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

/-- The effective score of a column, including both the loaded bias and the diagonal mask. -/
def score (p : Params) (L : Launch) (g : Nat) (v : V) (r : Rd) (i : Nat) : EReal :=
  match r with
  | .first => mre (i / 32) (mcnt p L g v) (i % 32) (bpeB p v i)
  | .bias => bpeB p v i
  | .plain => v.score i

/-- The reference maximum actually subtracted. Later rounds can retain the previous maximum. -/
def maximum (p : Params) (L : Launch) (g : Nat) (v : V) : Rd → EReal
  | .first => foldF p L g v
  | .bias => maxB p v
  | .plain => maxR p v

def scale (p : Params) (M : EReal) : ℝ := (2 : ℝ) ^ (-(scl p : ℝ) * M.toReal)

def weight (p : Params) (x : EReal) : ℝ :=
  if x = ⊥ then 0 else (2 : ℝ) ^ ((scl p : ℝ) * x.toReal)

def probability (p : Params) (M x : EReal) : ℝ :=
  if x = ⊥ then 0 else (2 : ℝ) ^ (x.toReal * (scl p : ℝ) + M.toReal * -(scl p : ℝ))

theorem probability_eq (p : Params) (M x : EReal) :
    probability p M x = scale p M * weight p x := by
  by_cases h : x = ⊥
  · simp [probability, weight, h]
  · simp only [probability, weight, h, ite_false, scale]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring

theorem probR_eq (p : Params) (L : Launch) (g : Nat) (v : V) (i : Nat) :
    probR p v i = probability p (maximum p L g v .plain) (score p L g v .plain i) := by
  simp only [score, maximum, probability, EReal.coe_ne_bot, ite_false, EReal.toReal_coe]
  cases h : v.mf
  · simp only [probR, maxR, h, Real.rpow_eq_pow]
  · simp only [probR, maxR, h, Real.rpow_eq_pow]
    split <;> rfl

def sumAfter (p : Params) (L : Launch) (g : Nat) (v : V) : Rd → ℝ
  | .first => rs1 p L g v
  | .bias => rsB p L g v
  | .plain => rsPG p v

theorem afterRound_stats (p : Params) (L : Launch) (g : Nat) (d : D) (r : Rd) :
    let v := (afterRound p L g d r).v
    v.mf = finE (maximum p L g d.v r) ∧ v.mr = (maximum p L g d.v r).toReal ∧
      v.rs = sumAfter p L g d.v r := by
  have plain (v : V) : (plainEntry p L g v).v.mf = v.mf ∧
      (plainEntry p L g v).v.mr = v.mr ∧ (plainEntry p L g v).v.rs = v.rs := by
    unfold plainEntry D.ite
    split <;> exact ⟨rfl,rfl,rfl⟩
  cases r with
  | first =>
    simp only [afterRound, afterFirst, D.ite, maximum, sumAfter]
    split
    · exact plain _
    · exact ⟨rfl,rfl,rfl⟩
  | bias =>
    simp only [afterRound, afterBias, D.ite, maximum, sumAfter]
    split
    · exact ⟨rfl,rfl,rfl⟩
    · exact plain _
  | plain =>
    simp only [afterRound, afterPlain, D.ite, maximum, sumAfter, finE,
      EReal.toReal_coe]
    split <;> exact ⟨rfl,rfl,rfl⟩

theorem final_regs (p : Params) (L : Launch) (g : Nat) (v : V) (j : Fin 2)
    (k : Fin 4) (acc : List Value) :
    let d : D := ⟨.fin j, v, k, acc⟩
    valueOfD p L g d 7257 = .float .f32 v.rs ∧ valueOfD p L g d 7256 = mxVal v := ⟨rfl, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
