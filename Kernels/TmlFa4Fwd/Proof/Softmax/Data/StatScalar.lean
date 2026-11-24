-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.Rescale
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPlainRs

@[expose] public section

/-! # The factor stores' words: the factor's number, or the pattern of one -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Proof PTX.Flow

/-- A factor's word: its number, or the pattern `0f3F800000` when it is one. -/
def FactorWord (w : Value) (x : ℝ) : Prop :=
  w = .float .f32 x ∨ w = .bits 32 (BitVec.ofNat 64 1065353216) ∧ x = 1

theorem FactorWord.reads {w : Value} {x : ℝ} (h : FactorWord w x) : Reads w x := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact reads_float _
  · exact reads_one

theorem word_bias (p L g v k acc) :
    FactorWord (valueOfD p L g ⟨.stat false,v,k,acc⟩ 1362) (factor p v .bias) := by
  change FactorWord (bif v.mf then (if keepB p v then _ else _) else _) _
  unfold FactorWord factor carry
  cases v.mf <;> cases keepB p v <;> first | exact .inl rfl | exact .inr ⟨rfl, rfl⟩

theorem word_plain (p L g v k acc) :
    FactorWord (valueOfD p L g ⟨.stat true,v,k,acc⟩ 1492) (factor p v .plain) := by
  have h1 : (valuesPlainP p v).lookup 1492 = some (facP p v) := by
    unfold valuesPlainP facP
    cases v.mf <;> rfl
  have h0 : (valuesPairs .plain v 64).lookup 1492 = none := by kernel_rfl
  simp only [valueOfD, valuesData, valuesData0, List.lookup_append, h0, h1, Option.none_or,
    Option.getD_some]
  unfold FactorWord facP factor carry
  cases v.mf <;> cases keepP p v <;> first | exact .inl rfl | exact .inr ⟨rfl, rfl⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
