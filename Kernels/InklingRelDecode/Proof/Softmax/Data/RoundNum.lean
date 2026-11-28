-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaNum
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords

@[expose] public section

/-! # The maxima of the rounds are numbers or `-inf`

The scale word is a positive number (`Pre.scalePos`). When the words a lane's shuffles of pc 1838
sent and received are each a number or `-inf`, the running maximum and the round's new maximum
(`mRound`, `mxRound`) are, and so the rescale factor `alphaWord` is a number
(`Data/AlphaNum.lean`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode

noncomputable section

/-- **The scale word of the launch is a positive number.** -/
theorem scaleW_has {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) :
    (Kd.s .pw).Has (scaleW L) := by
  have h := scaleVal_float hp
  have e : scaleW L = .float .f32 (Q.scale * log2eF32) := by
    simp [scaleW, Lib.scaleWord, xFinal, XItem.upd, XItem.vals, Lib.scaleItem, fF, regsOf, mulL,
      fOpnd, lk, regOf, List.flatMap, mulE_fin h valFloat_log2e, okVal]
  have pos : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
  rw [e]
  exact ⟨clean_float _, _, pos, readEReal_float _⟩

theorem mxWord_has {m a b : Value} (hm : (Kd.s .ni).Has m) (ha : (Kd.s .ni).Has a)
    (hb : (Kd.s .ni).Has b) : (Kd.s .ni).Has (Lib.mxWord m a b) := by
  simp only [Lib.mxWord, Lib.maxItem, xFinal, XItem.upd, XItem.vals, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, Function.update_self]
  simp
  exact max3_has hm ha hb

theorem mNext_has {c m mx : Value} (hm : (Kd.s .ni).Has m) (hmx : (Kd.s .ni).Has mx) :
    (Kd.s .ni).Has (Lib.mNext c m mx) := by
  simp [Lib.mNext, oFinal, Lib.updItem, OItem.upd, OItem.vals, Function.update, Lib.alphaVal,
    Lib.alphaRest, xFinal, XItem.upd, XItem.vals, Lib.alphaIn, opndVal]
  split_ifs <;> assumption

theorem init_has : (Kd.s .ni).Has (b32 4286578688) := Or.inr rfl

/-- The running maximum after any rounds of words that are numbers or `-inf`. -/
theorem mAfter_has (c : Value) (ps : List (Value × Value))
    (h : ∀ p ∈ ps, (Kd.s .ni).Has p.1 ∧ (Kd.s .ni).Has p.2) : (Kd.s .ni).Has (mAfter c ps) := by
  induction ps using List.reverseRecOn with
  | nil => exact init_has
  | append_singleton ps p ih =>
    rw [mAfter_append]
    have ih := ih fun q hq => h q (List.mem_append_left _ hq)
    have hp := h p (List.mem_append_right _ (List.mem_singleton_self p))
    exact mNext_has ih (mxWord_has ih hp.1 hp.2)

/-- **The running maximum of a round** is a number or `-inf` when the words of the earlier
rounds are. -/
theorem mRound_has {L : Launch} {X : Execution} {g j : Nat}
    (h : ∀ p ∈ roundWords X g j, (Kd.s .ni).Has p.1 ∧ (Kd.s .ni).Has p.2) :
    (Kd.s .ni).Has (mRound L X g j) :=
  mAfter_has _ _ fun p hp => h p (List.mem_of_mem_dropLast hp)

/-- **The new maximum of a round** is a number or `-inf` when the words of the rounds are. -/
theorem mxRound_has {L : Launch} {X : Execution} {g j : Nat}
    (h : ∀ p ∈ roundWords X g j, (Kd.s .ni).Has p.1 ∧ (Kd.s .ni).Has p.2) :
    (Kd.s .ni).Has (mxRound L X g j) := by
  unfold mxRound
  cases hl : (roundWords X g j).getLast? with
  | none => exact SK.mono (a := .fl) (b := .ni) (by decide) zero_has
  | some p =>
    have hp := h p (List.mem_of_getLast? hl)
    exact mxWord_has (mRound_has h) hp.1 hp.2

/-- **The rescale factor of a round is a number.** -/
theorem alphaWord_has {Q : Params} {L : Launch} {m : Mem0} (hp : Pre Q L m) {X : Execution}
    {g j : Nat}
    (h : ∀ p ∈ roundWords X g j, (Kd.s .ni).Has p.1 ∧ (Kd.s .ni).Has p.2) :
    (Kd.s .fl).Has (alphaWord (scaleW L) (mRound L X g j) (mxRound L X g j)) :=
  alpha_real (scaleW_has hp) (mRound_has h) (mxRound_has h)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
