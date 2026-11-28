-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.RcpStep
public import Lemmas.Flow.TypedFloatJ
public import Lemmas.Flow.RcpCore
import Kernels.InklingRelDecode.Proof.Lib.RcpApprox

@[expose] public section

/-! # The reciprocal at 2602 writes a datum

`rcp.approx.ftz.f32` of a datum that is not a zero is the exact reciprocal (a number), or Core's
table row (an infinity or NaN): the value fact that the operand is not a zero gives
`Iface.RcpStep`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption

noncomputable section

private theorem rcpI_lane (fz : Bool) (x : FVal) (h : ∀ q, x ≠ .fin q) :
    ∃ o, FloatInstr.lane (rcpI fz) [x] = some (.val o) := by
  cases x with
  | zero n => cases n <;> cases fz <;> exact ⟨_, rfl⟩
  | fin q => exact absurd rfl (h q)
  | inf n => cases n <;> cases fz <;> exact ⟨_, rfl⟩
  | nan b => cases fz <;> exact ⟨_, rfl⟩

/-- The outcome of `rcp.approx.f32` on a datum that is not a zero is a datum. -/
theorem rcpE_total {fz : Bool} {va : Value} (ha : Dat32 va)
    (h0 : ∀ x, readEReal .f32 va = some (.ok x) → x ≠ 0) :
    ∃ v, rcpE fz va = .ok v ∧ Dat32 v := by
  obtain ⟨c, hc⟩ := ha.1
  by_cases hn : rcpVal va = none
  · have hfin : ∀ q, c ≠ .fin q := by
      intro q hq; subst hq
      obtain ⟨x, hx⟩ := readEReal_fin hc
      simp only [rcpVal, finiteVal, hx, bindRead, EReal.coe_ne_top, EReal.coe_ne_bot, or_self,
        ↓reduceIte, EReal.toReal_coe, pure, Except.pure] at hn
      cases hn
    obtain ⟨o, ho⟩ := rcpI_lane fz c hfin
    refine ⟨o.toValue .f32, ?_, dat32_toValue o⟩
    unfold rcpE
    rw [hn]
    simp [coreFloat, rcpI, ty1, floatLane, show List.range 1 = [0] from rfl, hc, ho, bind,
      Except.bind, pure, Except.pure]
  · obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hn
    unfold rcpE
    rw [hr]
    rcases readEReal_dat ha.1 with hx | ⟨x, hx⟩
    · simp [rcpVal, finiteVal, hx, bindRead] at hr
    by_cases hb : x = ⊤ ∨ x = ⊥
    · simp [rcpVal, finiteVal, hx, hb, bindRead] at hr
    have hz : x.toReal ≠ 0 := fun h => by
      rcases EReal.toReal_eq_zero_iff.mp h with h | h | h
      exacts [h0 x hx h, hb (.inl h), hb (.inr h)]
    simp only [rcpVal, finiteVal, hx, hb, bindRead, ↓reduceIte, pure, Except.pure,
      Option.some.injEq] at hr
    subst hr
    simp only [hz, ↓reduceIte]
    exact ⟨_, rfl, dat32_float _⟩

/-- **The reciprocal at 2602** does not fault and writes a datum, when its operand is not a zero
whenever it reads as an extended real. -/
theorem rcpStep_of {L : Launch} {g : Nat} {R : TState → Prop}
    (h0 : ∀ t, R t → t.pc = 2602 →
      ∀ x : EReal, readERealOpnd t .f32 (.reg 1762) = some (.ok x) → x ≠ 0) :
    Iface.RcpStep L g R := by
  intro op hop t hpc hT hR
  obtain rfl : op = _ := congrArg Instr.op (Option.some.inj (hop.symm.trans Flow.code_2602))
  obtain ⟨va, hva, hd⟩ := hT 1762 .dat32 (by decide +kernel)
  obtain ⟨hA, hD⟩ := Lib.approx_2602 (L := L) (g := g) hpc
  have hx := exec_rcpE hA hD (fz := true) (d := 1761) (OpndIs.reg hva)
  obtain ⟨v, hv, hdv⟩ := rcpE_total (fz := true) hd fun x hx => h0 t hR hpc x (by
    simpa [readERealOpnd, readReg, hva, pure, Except.pure] using hx)
  exact ⟨v, by rw [hx, hv]; rfl, hdv⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Top
