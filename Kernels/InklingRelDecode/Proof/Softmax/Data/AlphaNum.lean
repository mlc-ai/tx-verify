-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.NumLib
public import Kernels.InklingRelDecode.Proof.Lib.Alpha
import Lemmas.Flow.SetpReads
import Lemmas.Flow.Recip
import Lemmas.Flow.Step.RuleStep
import Lemmas.Flow.MulERealBot

@[expose] public section

/-! # The rescale factor is a number

The rescale factor of a round (`Lib.alphaVal`, register 507) is `1` or `2 ^ x` with `x` the scaled
difference of the running maximum and the round's maximum, where the maximum is replaced by `0` when
it is `-inf`. With a positive scale and both maxima a number or `-inf` the difference is a number
or `-inf`, so the factor is a number whichever way the test falls. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof

noncomputable section

theorem sub_has {fz : Bool} {d a b : Value} (ha : (Kd.s .ni).Has a) (hb : (Kd.s .fl).Has b) :
    (Kd.s .ni).Has (okVal d (subE fz a b)) := by
  obtain ⟨x, hx, lx⟩ := SK.lane_of (k := .ni) (by decide) ha
  obtain ⟨y, hy, ly⟩ := SK.lane_of (k := .fl) (by decide) hb
  obtain ⟨s, rfl⟩ := ly
  have hz : ∃ z, addEReal x (-(s : EReal)) = some z ∧ SK.ni.Lane z := by
    rcases lx with ⟨r, rfl⟩ | rfl
    · exact ⟨_, addEReal_coe_neg r s, .inl ⟨_, rfl⟩⟩
    · rw [← EReal.coe_neg]
      exact ⟨⊥, SK.addEReal_bot_coe _, .inr rfl⟩
  obtain ⟨z, hz, lz⟩ := hz
  rw [okVal_ok (subE_reads hx hy hz)]
  exact SK.has_erealValue lz

theorem mul_has {fz : Bool} {d a b : Value} (ha : (Kd.s .pw).Has a) (hb : (Kd.s .ni).Has b) :
    (Kd.s .ni).Has (okVal d (mulE fz a b)) := by
  obtain ⟨-, r, hr, hx⟩ := ha
  obtain ⟨y, hy, ly⟩ := SK.lane_of (k := .ni) (by decide) hb
  have hz : ∃ z, mulEReal (r : EReal) y = some z ∧ SK.ni.Lane z := by
    rcases ly with ⟨s, rfl⟩ | rfl
    · exact ⟨_, mulEReal_coe r s, .inl ⟨_, rfl⟩⟩
    · exact ⟨⊥, mulEReal_coe_bot_pos hr, .inr rfl⟩
  obtain ⟨z, hz, lz⟩ := hz
  rw [okVal_ok (mulE_reads hx hy hz)]
  exact SK.has_erealValue lz

theorem ex2_has {fz : Bool} {d a : Value} (ha : (Kd.s .ni).Has a) :
    (Kd.s .fl).Has (okVal d (ex2E fz a)) := by
  rcases ha with ⟨-, r, hr⟩ | rfl
  · rw [okVal_ok (ex2E_real hr)]
    exact has_float_fl _
  · rw [okVal_ok (ex2E_negInf fz)]
    exact has_float_fl _

/-- The maximum the factor uses: `0` when the new maximum is `-inf`, else the maximum. -/
theorem sel_mx_has {mx : Value} (hmx : (Kd.s .ni).Has mx) :
    (Kd.s .fl).Has (if predOf (.pred (okPred (setpE (.ord .eq) false mx
      (.bits 32 4286578688)))) = true then Value.bits 32 0 else mx) := by
  rcases hmx with h | rfl
  · obtain ⟨r, hr⟩ := h.2
    have hy : readEReal .f32 (.bits 32 4286578688) = some (.ok ⊥) := readEReal_negInf
    rw [setpE_reads (cmp := .eq) (Or.inl rfl) hr hy]
    simp only [okPred, erealCompare, predOf, EReal.coe_ne_bot, decide_false, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨h.1, r, hr⟩
  · have hy : readEReal .f32 (.bits 32 4286578688) = some (.ok ⊥) := readEReal_negInf
    rw [setpE_reads (cmp := .eq) (Or.inl rfl) readEReal_negInf hy]
    simp only [okPred, erealCompare, predOf, decide_true, ↓reduceIte]
    exact zero_has

/-- **The rescale factor is a number**: for a positive scale word and maxima that are a number or
`-inf`. -/
theorem alpha_real {c m mx : Value} (hc : (Kd.s .pw).Has c) (hm : (Kd.s .ni).Has m)
    (hmx : (Kd.s .ni).Has mx) : (Kd.s .fl).Has (Lib.alphaVal c m mx 507) := by
  have hs := sel_mx_has hmx
  simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals,
    Function.update, Lib.alphaIn, opndVal]
  generalize (if predOf (.pred (okPred (setpE (.ord .eq) false mx (.bits 32 4286578688)))) = true
    then Value.bits 32 0 else mx) = s at hs ⊢
  split_ifs
  · exact one_has
  · exact ex2_has (mul_has hc (sub_has hm hs))

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
