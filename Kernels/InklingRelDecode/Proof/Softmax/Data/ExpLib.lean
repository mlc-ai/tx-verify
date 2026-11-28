-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.NumExp
public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesE
import Lemmas.Flow.W0Reads

@[expose] public section

/-! # Words that read as numbers: the selection, the sums and the pack of the exponents

Closure lemmas for the rest of the exponent window and the probability pack: a register select of
two numbers, the sum of two numbers and of two pairs of numbers. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

/-- **A select between two words of a kind** (Core's `selp.f32`) is a word of the kind (a number
kind), the first need only be one where the predicate picks it. -/
theorem selp2_has {k : SK} (hk : SK.fl.le k = true) {d a b p : Nat} {x y pv : Value}
    (hab : b ≠ a) (hpa : p ≠ a) (hpb : p ≠ b)
    (hx : predOf pv = true → (Kd.s k).Has x) (hy : (Kd.s k).Has y) :
    (Kd.s k).Has (okVal (.bits 32 0) (coreF (.int ⟨.selp, .float .f32, false, [some d],
      [.reg a, .reg b, .reg p]⟩) [a, b, p] [x, y, pv])) := by
  have hb : lk [a, b, p] [x, y, pv] b = y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have ha : lk [a, b, p] [x, y, pv] a = x := by simp [lk]
  unfold coreF coreW
  cases hp : lk [a, b, p] [x, y, pv] p <;> simp only [hp, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw, okVal]
  all_goals try exact SK.mono (a := .fl) (b := k) hk zero_has
  rename_i q
  have hpv : pv = .pred q := by
    simpa only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hpa,
      beq_false_of_ne hpb, beq_self_eq_true, Option.getD_some] using hp
  cases q
  · have h4 : y.bytes = (DType.float FType.f32).width / 8 := (SK.clean (k := k) hy).1
    simp only [oVal, hb, h4, pure, Except.pure, ite_true, Bool.false_eq_true, ite_false]
    exact hy
  · have hx' := hx (by simp [hpv, predOf])
    have h4 : x.bytes = (DType.float FType.f32).width / 8 := (SK.clean (k := k) hx').1
    simp only [oVal, ha, h4, pure, Except.pure, ite_true]
    exact hx'

/-- **A number times a number plus a number is a number.** -/
theorem fma_fl_has {fz : Bool} {d a b c : Value} (ha : (Kd.s .fl).Has a) (hb : (Kd.s .fl).Has b)
    (hc : (Kd.s .fl).Has c) : (Kd.s .fl).Has (okVal d (floatE (fmaI .rn fz) [a, b, c])) := by
  obtain ⟨-, r, hr⟩ := ha
  obtain ⟨-, s, hs⟩ := hb
  obtain ⟨-, u, hu⟩ := hc
  have hw : (mulEReal (r : EReal) (s : EReal)).bind (addEReal · (u : EReal)) =
      some (((r * s + u : ℝ)) : EReal) := by
    rw [mulEReal_coe]; exact addEReal_coe ..
  rw [okVal_ok (fmaE_reads hr hs hu hw), erealValue_coe]
  exact has_float_fl _

/-- **The sum of two numbers is a number.** -/
theorem add_fl_has {fz : Bool} {d a b : Value} (ha : (Kd.s .fl).Has a) (hb : (Kd.s .fl).Has b) :
    (Kd.s .fl).Has (okVal d (floatE (addI fz) [a, b])) := by
  obtain ⟨-, r, hr⟩ := ha
  obtain ⟨-, s, hs⟩ := hb
  rw [okVal_ok (addE_reads hr hs (addEReal_coe r s)), erealValue_coe]
  exact has_float_fl _

/-- **The sum of two pairs of numbers is a pair of numbers** (`add.f32x2`). -/
theorem add2N_fl_has {d a b : Value} (ha : (Kd.pr .fl).Has a) (hb : (Kd.pr .fl).Has b) :
    (Kd.pr .fl).Has (okVal d (add2NE a b)) := by
  obtain ⟨-, ha0, ha1⟩ := ha
  obtain ⟨-, hb0, hb1⟩ := hb
  obtain ⟨-, x0, hx0⟩ := ha0
  obtain ⟨-, x1, hx1⟩ := ha1
  obtain ⟨-, y0, hy0⟩ := hb0
  obtain ⟨-, y1, hy1⟩ := hb1
  have e : add2NE a b = .ok (.pair (erealValue .f32 ((x0 + y0 : ℝ) : EReal))
      (erealValue .f32 ((x1 + y1 : ℝ) : EReal))) := by
    unfold add2NE
    simp only [idealAdd2, pairRead_of_reads hx0 hx1, pairRead_of_reads hy0 hy1, bindRead,
      addEReal_coe, pure, Except.pure]
  rw [okVal_ok e]
  exact pair_has (SK.has_erealValue (k := .fl) ⟨_, rfl⟩) (SK.has_erealValue (k := .fl)
    ⟨_, rfl⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
