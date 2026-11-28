-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.AlphaExact

@[expose] public section

/-! # The shift of the exponent window on exact inputs

The first run of the exponent window selects the maximum it subtracts (the running maximum if the
rescale test holds, else the round's `m_safe`) and multiplies it by the negated scale. On exact
inputs the product is `mUse * (-sc)` with `mUse` the maximum of `SoftFold.step`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open Lib.SoftFold Classical

noncomputable section

/-- A select of two four-byte words is the one the predicate picks. -/
theorem selp_val {dd a b p : Nat} (hab : b ≠ a) (hpa : p ≠ a) (hpb : p ≠ b) (q : Bool)
    {x y : Value} (hx : x.bytes = 4) (hy : y.bytes = 4) (d : Value) :
    okVal d (coreF (.int ⟨.selp, .float .f32, false, [some dd], [.reg a, .reg b, .reg p]⟩)
      [a, b, p] [x, y, .pred q]) = if q then x else y := by
  unfold coreF coreW
  have hb : lk [a, b, p] [x, y, Value.pred q] b = y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have ha : lk [a, b, p] [x, y, Value.pred q] a = x := by simp [lk]
  have hp : lk [a, b, p] [x, y, Value.pred q] p = .pred q := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hpa,
      beq_false_of_ne hpb, beq_self_eq_true, Option.getD_some]
  cases q <;> simp [hp, hb, ha, hx, hy, oVal, DType.width, pure, Except.pure, okVal, bind,
    Except.bind]

theorem ev_bytes {v : Value} {x : EReal} (h : Ev v x) : v.bytes = 4 := by
  rw [h.1]
  induction x using EReal.rec with
  | bot => rw [erealValue_bot]; rfl
  | coe r => rw [erealValue_coe]; rfl
  | top => exact absurd rfl h.2

theorem ev_mul_rr {fz : Bool} {d a b : Value} {x y : ℝ} (ha : Rd a x) (hb : Rd b y) :
    Ev (okVal d (mulE fz a b)) ((x * y : ℝ) : EReal) :=
  ⟨by rw [okVal_ok (mulE_reads ha hb (mulEReal_coe x y)), erealValue_coe],
    EReal.coe_ne_top _⟩

theorem keep_ne_bot {sc : ℝ} (hpos : 0 < sc) {mE : EReal} (xE : EReal)
    (h : Keep (alphaLog2 sc mE xE)) : mE ≠ ⊥ := by
  rintro rfl
  simp only [alphaLog2, EReal.bot_sub, EReal.bot_mul_coe_of_pos hpos] at h
  exact not_keep_bot h

/-- **The shift constant**: the selected maximum times the negated scale. -/
theorem shift_ev {V : Nat → Value} {sc : ℝ} {mE xE : EReal} {b : Bool} (hpos : 0 < sc)
    (hm : Ev (V 1914) mE) (hmu : Rd (V 1523) (mSafe xE : ℝ)) (h1523 : (V 1523).bytes = 4)
    (hp : V 168 = .pred b) (hb : b = true ↔ Keep (alphaLog2 sc mE xE))
    (h499 : Ev (V 499) ((-sc : ℝ) : EReal)) :
    Ev (Gen.ex1_v1848 V) (((if Keep (alphaLog2 sc mE xE) then mE.toReal else mSafe xE) *
      (-sc) : ℝ) : EReal) := by
  have e : Gen.ex1_v1847 V = if b then V 1914 else V 1523 := by
    unfold Gen.ex1_v1847 Gen.ex1_op1847
    rw [hp]
    exact selp_val (dd := 1525) (by decide) (by decide) (by decide) b (ev_bytes hm) h1523 _
  unfold Gen.ex1_v1848
  rw [e]
  by_cases hk : Keep (alphaLog2 sc mE xE)
  · have hbt : b = true := hb.mpr hk
    obtain ⟨r, hr⟩ : ∃ r : ℝ, mE = r := by
      induction mE using EReal.rec with
      | bot => exact absurd rfl (keep_ne_bot hpos xE hk)
      | coe r => exact ⟨r, rfl⟩
      | top => exact absurd rfl hm.2
    subst hr
    simp only [hbt, hk, ite_true, EReal.toReal_coe]
    exact ev_mul_rr hm.read h499.read
  · have hbf : b = false := by simpa using mt hb.mp hk
    simp only [hbf, hk, Bool.false_eq_true, ite_false]
    exact ev_mul_rr hmu h499.read

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
