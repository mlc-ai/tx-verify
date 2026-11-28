-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpEst
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
public import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Lemmas.Flow.SetpReads
import Lemmas.Flow.MulERealBot

@[expose] public section

/-! # The exponent window's inputs are typed

The registers the exponent window reads are typed (`ExpIn`) when the value state is: the running
maximum and the round's maximum are numbers or `-inf`, the bias words and the scores are numbers.
The maximum used is a number, the scale positive, and the rescale test (`p168`) fails when the
running maximum is `-inf`, so a maximum that passes the test is a number. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode

set_option maxRecDepth 100000
noncomputable section

theorem f32Value_m8 : f32Value 3238002688 = some (-8) := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

/-- The threshold of the rescale test reads as `-8`. -/
theorem read_m8 : readEReal .f32 (.bits 32 (BitVec.ofNat 64 3238002688)) =
    some (.ok (((-8 : ℝ)) : EReal)) := by
  have := valFloat_b32 (b := 3238002688) (by norm_num) f32Value_m8
  have h2 := readEReal_of_valFloat (by simpa [b32] using this)
  simpa [b32] using h2

/-- **The rescale test fails when the running maximum is `-inf`.** -/
theorem alpha_pm_false {c mx : Value} (hc : (Kd.s .pw).Has c) (hmx : (Kd.s .ni).Has mx) :
    predOf (Lib.alphaVal c (b32 4286578688) mx 168) = false := by
  have hs := sel_mx_has hmx
  simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals,
    Function.update, Lib.alphaIn, opndVal]
  generalize (if predOf (.pred (okPred (setpE (.ord .eq) false mx (.bits 32 4286578688)))) = true
    then Value.bits 32 0 else mx) = s at hs ⊢
  obtain ⟨-, r, hr⟩ := hs
  have e1 : subE false (b32 4286578688) s = .ok (erealValue .f32 ⊥) :=
    subE_reads (x := ⊥) (y := r) readEReal_negInf hr
      (by rw [← EReal.coe_neg]; exact addEReal_bot_coe _)
  obtain ⟨-, q, hq, hqr⟩ := hc
  have e2 : mulE false c (erealValue .f32 ⊥) = .ok (erealValue .f32 ⊥) :=
    mulE_reads hqr (by rw [erealValue_bot]; exact readEReal_negInf) (mulEReal_coe_bot_pos hq)
  have e3 := setpE_reads (c := .ord .ge) (fz := false) (cmp := .ge) (Or.inl rfl)
    (va := erealValue .f32 ⊥) (by rw [erealValue_bot]; exact readEReal_negInf) read_m8
  rw [okVal_ok e1, okVal_ok e2]
  simp only [e3]
  simp [okPred, predOf, erealCompare]

/-- **A running maximum that passes the rescale test is a number.** -/
theorem alpha_pm {c m mx : Value} (hc : (Kd.s .pw).Has c) (hm : (Kd.s .ni).Has m)
    (hmx : (Kd.s .ni).Has mx) (h : predOf (Lib.alphaVal c m mx 168) = true) :
    (Kd.s .fl).Has m := by
  rcases hm with hf | rfl
  · exact hf
  · have hn := alpha_pm_false hc hmx
    change predOf (Lib.alphaVal c negInf32 mx 168) = false at hn
    rw [hn] at h
    exact absurd h (by decide)

/-- **The maximum the rescale run uses is a number.** -/
theorem alpha_mu {c m mx : Value} (hmx : (Kd.s .ni).Has mx) :
    (Kd.s .fl).Has (Lib.alphaVal c m mx 1523) := by
  have hs := sel_mx_has hmx
  simp [Lib.alphaVal, Lib.alphaRest, xFinal, XItem.upd, XItem.vals, OItem.vals,
    Function.update, Lib.alphaIn, opndVal]
  exact hs

/-- The words of the last run are numbers or `-inf`. -/
theorem m_facts_has (W : Nat → Value)
    (h : ∀ r, 2447 ≤ r → r < 2479 → (Kd.pr .ni).Has (W r)) :
    ∀ p ∈ runM.fs1 W, (Kd.s .ni).Has p.2 := by
  intro p hp
  simp only [runM, Gen.w1m_facts3, List.mem_cons, List.not_mem_nil, or_false] at hp
  repeat' rcases hp with rfl | hp
  all_goals dsimp only
  all_goals repeat' first
    | (apply h <;> omega)
    | apply split1_has | apply split2_has | apply max3_has | apply max2_has

theorem scoreRegs_runM : ∀ r ∈ scoreRegs, r ∈ runM.outs := by decide +kernel

/-- **The 64 masked scores are numbers or `-inf`.** -/
theorem w1_scores (V : Nat → Value) (h : W1In V) : ∀ r ∈ scoreRegs, (Kd.s .ni).Has (vFin V r) := by
  obtain ⟨W, hW, e⟩ := w1_file V h
  intro r hr
  rw [e]
  exact V'_out runM runM_ok (P := fun _ => (Kd.s .ni).Has) (m_facts_has W hW) (scoreRegs_runM r hr)

theorem scoreRegs_cls : ∀ r ∈ scoreRegs,
    ¬(r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523) ∧ r ≠ 499 := by decide +kernel

variable {e : Control.Entry} {L : Launch} {g : Nat}

/-- **The registers the exponent window reads are typed** when the scores it reads are. -/
theorem xV_expIn_s {Q : Params} {m : Mem0} (hp : Pre Q L m) {d : D}
    (hs : ∀ r ∈ scoreRegs, (Kd.s .ni).Has (xV e L g d r))
    (hm : (Kd.s .ni).Has (m0 d)) (hmx : (Kd.s .ni).Has d.v.mx) : ExpIn (xV e L g d) := by
  have hsc := scaleW_has hp
  have hx : ∀ r, (r = 168 ∨ r = 498 ∨ r = 1914 ∨ r = 1523) → xV e L g d r =
      Lib.alphaVal (scaleW L) (m0 d) d.v.mx r := fun r h => by simp [xV, h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx 1914 (by simp), alphaVal_m]
    exact hm
  · rw [hx 1523 (by simp)]
    exact alpha_mu hmx
  · intro h
    rw [hx 168 (by simp)] at h
    rw [hx 1914 (by simp), alphaVal_m]
    exact alpha_pm hsc hm hmx h
  · rw [hx 498 (by simp), alphaVal_c]
    exact hsc
  · have e499 : xV e L g d 499 = derV e L g 499 := by simp [xV]
    rw [e499, derV_499 (scaleVal_float hp)]
    exact has_float_fl _
  · exact hs

/-- **The registers the exponent window reads are typed** at a state whose words are. -/
theorem xV_expIn {Q : Params} {m : Mem0} (hp : Pre Q L m) {d : D} (hv : VTyp d.v)
    (hm : (Kd.s .ni).Has (m0 d)) (hmx : (Kd.s .ni).Has d.v.mx) : ExpIn (xV e L g d) := by
  refine xV_expIn_s hp (fun r hr => ?_) hm hmx
  obtain ⟨h1, h2⟩ := scoreRegs_cls r hr
  simp only [xV, h1, h2]
  exact w1_scores _ (w1_in hp hv) r hr

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
