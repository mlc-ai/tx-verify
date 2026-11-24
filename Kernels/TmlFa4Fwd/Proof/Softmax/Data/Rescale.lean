-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Exponent
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs
import Lemmas.Flow.Recip
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarrBChain

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Proof PTX.Flow PTX.Assumption
noncomputable section

def carry (p : Params) (v : V) (keep : Bool) (candidate : ℝ) : ℝ :=
  bif v.mf then (bif keep then 1 else (2 : ℝ) ^ ((scl p : ℝ)*(v.mr + -candidate))) else 0

def factor (p : Params) (v : V) : Rd → ℝ
  | .first => 1
  | .bias => carry p v (keepB p v) (foldBR p v)
  | .plain => carry p v (keepP p v) (foldPT v.mr v.score)

theorem reads_one : Reads (.bits 32 (BitVec.ofNat 64 1065353216)) (1 : ℝ) := by
  have hc := classify_word f32Value_one one_ne_zero (by norm_num)
  rw [show truncBits 32 (BitVec.ofNat 64 1065353216) = BitVec.ofNat 64 1065353216 by decide] at hc
  exact ⟨one_fl.1, by simpa using
    (readEReal_bits_fin (w := 32) (x := BitVec.ofNat 64 1065353216) (s := 1) hc)⟩

theorem bias_factor (p : Params) (v : V) :
    Reads (lookupD (valuesBiasM p v) 1362) (factor p v .bias) := by
  change Reads (bif v.mf then (if keepB p v then _ else _) else _) _
  unfold factor carry
  cases v.mf <;> cases keepB p v <;> first | exact reads_one | exact reads_float _

theorem plain_factor (p : Params) (v : V) : Reads (facP p v) (factor p v .plain) := by
  unfold factor carry facP
  cases v.mf <;> cases keepP p v <;> first | exact reads_one | exact reads_float _

theorem stat_bias (p L g v k acc) :
    Reads (valueOfD p L g ⟨.stat false,v,k,acc⟩ 1362) (factor p v .bias) := bias_factor p v

theorem stat_plain (p L g v k acc) :
    Reads (valueOfD p L g ⟨.stat true,v,k,acc⟩ 1492) (factor p v .plain) := by
  have h1 : (valuesPlainP p v).lookup 1492 = some (facP p v) := by
    unfold valuesPlainP facP
    cases v.mf <;> rfl
  have h0 : (valuesPairs .plain v 64).lookup 1492 = none := by kernel_rfl
  simp only [valueOfD, valuesData, valuesData0, List.lookup_append, h0, h1, Option.none_or,
    Option.getD_some]
  exact plain_factor p v

private theorem ratio (p : Params) (a b : ℝ) :
    scale p (b : EReal) / scale p (a : EReal) = (2 : ℝ) ^ ((scl p : ℝ)*(a + -b)) := by
  simp only [scale, EReal.toReal_coe]
  rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem factor_ratio (p L g v r) (hr : r ≠ .first) (hm : v.mf = true) :
    factor p v r = scale p (maximum p L g v r) / scale p (v.mr : EReal) := by
  cases r with
  | first => exact (hr rfl).elim
  | bias =>
    simp only [factor, carry, maximum, maxB, hm, Bool.cond_true, Bool.true_and]
    cases keepB p v
    · simp only [Bool.cond_false, Bool.false_eq_true, ite_false]
      conv_rhs => rw [foldBE_real (p := p) hm, ratio]
    · simp only [ite_true, Bool.cond_true]; rw [ratio]; simp
  | plain =>
    simp only [factor, carry, maximum, maxR, hm, Bool.cond_true]
    cases keepP p v
    · exact (ratio p _ _).symm
    · simp only [ite_true, Bool.cond_true]; rw [ratio]; simp

private theorem carry_le (p : Params) (v : V) (b : ℝ) :
    carry p v (erealCompare .ge (((scl p : ℝ)*(v.mr + -b) : ℝ) : EReal)
      ((-8 : ℝ) : EReal)) b ≤ 1 := by
  unfold carry
  cases v.mf
  · exact zero_le_one
  · simp only [Bool.cond_true, erealCompare, EReal.coe_le_coe_iff]
    by_cases h : -8 ≤ (scl p : ℝ) * (v.mr + -b) <;> simp only [h, decide_true, decide_false,
      Bool.cond_true, Bool.cond_false]
    · exact le_rfl
    · apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have := lt_of_not_ge h
      linarith

theorem factor_le (p : Params) (v : V) (r : Rd) : factor p v r ≤ 1 := by
  cases r
  · exact le_rfl
  · exact carry_le p v _
  · exact carry_le p v _

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
