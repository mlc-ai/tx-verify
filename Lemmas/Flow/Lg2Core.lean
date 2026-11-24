-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # The approximate base-2 logarithm by Core's table on zero

A proof tool. A kernel assumption that reads `lg2.approx{.ftz}.f32` as the exact logarithm covers
positive finite operands only (tml-fa4's `lg2Exact`); on `+0` it declines and Core's rule
(THREAD-FLOAT-APPROX, `lg2Table`: `(.posZero, .inf true)`) writes `f32` negative infinity
(`coreFloat_lg2_zero`). `execLocal_lg2_core` is Core's step on any operand value, so with the
assumptions declining at the state (`execLocalRule_of_none`) a role steps the logarithm of a zero
row sum to `-inf` (`exec_lg2_zero`). The infinity then reads as `⊥` under the ideal-real
assumption (`readEReal_lit`), whose `fma` and `mul` outcomes on `⊥` are `mulEReal_bot_pos` and
`addEReal_bot_coe` (`rule_step`'s simp set). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `lg2.approx{.ftz}.f32`. -/
abbrev lg2I (fz : Bool) : FloatInstr :=
  { op := .lg2, ty := ty1 .f32, mode := .approx, ftz := fz, dsts := [], srcs := [] }

theorem execLocal_lg2_core {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { lg2I fz with dsts := [some d], srcs := [a] }) =
      (coreFloat (lg2I fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { lg2I fz with dsts := [some d], srcs := [a] } =
      FloatInstr.lane (lg2I fz) := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane (lg2I fz) [xa] with
  | none => core_float
  | some o => cases o <;> core_float

/-- A zero payload classifies as `+0`. -/
theorem classify_f32_zero : classify .f32 (.float .f32 0) = .ok (.zero false) := by
  obtain ⟨q, hq, h⟩ := classify_float_repr (fmt := .f32) (x := 0)
    ⟨0, 0, rfl, by simp⟩
  rw [h]
  have : q = 0 := by exact_mod_cast hq
  subst this
  rfl

/-- **Core's `lg2.approx.f32` of `+0` is `f32` negative infinity.** -/
theorem coreFloat_lg2_zero (fz : Bool) :
    coreFloat (lg2I fz) [.float .f32 0] = .ok (.bits 32 (BitVec.ofNat 64 0xFF800000)) := by
  simp only [coreFloat, floatLane, List.range, List.range.loop, List.mapM_cons,
    List.mapM_nil, ite_true, classify_f32_zero, bind, Except.bind, pure, Except.pure]
  cases fz <;> rfl

/-- `execLocal_lg2_core` on a state written out (the form `rule_step`'s goals have). -/
theorem execLocal_lg2_regs {pc : Nat} {R : Nat → Option Value} {cf : Option Bool} {sub : Nat}
    {acc : List Value} {f : Option Fault} {fz : Bool} {d r : Nat} {v : Value}
    (h : R r = some v) :
    execLocal L g ⟨pc, R, cf, sub, acc, f⟩
        (.float { lg2I fz with dsts := [some d], srcs := [.reg r] }) =
      (coreFloat (lg2I fz) [v]).map fun w => PTX.next (setReg ⟨pc, R, cf, sub, acc, f⟩ d w) :=
  execLocal_lg2_core (OpndIs.reg (t := ⟨pc, R, cf, sub, acc, f⟩) h)

/-- **Core's `lg2.approx.f32` of a payload that is zero** is `f32` negative infinity. -/
theorem coreFloat_lg2_eq_zero (fz : Bool) {x : ℝ} (hx : x = 0) :
    coreFloat (lg2I fz) [.float .f32 x] = .ok (.bits 32 (BitVec.ofNat 64 0xFF800000)) := by
  subst hx
  exact coreFloat_lg2_zero fz

/-- **The logarithm of a zero operand** when no assumption selects the instruction at the state:
`f32` negative infinity. -/
theorem exec_lg2_zero {t : TState} {fz : Bool} {d : Nat} {a : Opnd}
    (ha : OpndIs L g t a (.float .f32 0))
    (hN : ∀ a' ∈ A, a'.localRule L g t (.float { lg2I fz with dsts := [some d], srcs := [a] }) =
      none)
    (hS : Assumption.SegFreePc A t.pc := by seg_free) :
    execLocalA A L g t (.float { lg2I fz with dsts := [some d], srcs := [a] }) =
      .ok (PTX.next (setReg t d (.bits 32 (BitVec.ofNat 64 0xFF800000)))) := by
  rw [hS.exec, execLocalRule_of_none hN, execLocal_lg2_core ha, coreFloat_lg2_zero]
  all_goals rfl

end

end PTX.Flow
