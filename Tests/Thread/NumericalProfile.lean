-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Assumption.IdealReal
public import Core.Assumption.ApproxExact

/-! The scope of `idealReal` and `approxExact`: a scoped assumption selects only the forms it
names, an instruction outside the scope has the Core rule, and the assumptions have no premises
and no undefined behaviour of their own. -/
namespace PTX.Tests.NumericalProfile
noncomputable section

private def launch : Launch := { grid := 1, block := 1, params := fun _ => none }
/-- Exact real `add.f32` only. -/
private def idealAddF32 : Assumption :=
  Assumption.idealReal "test-ideal-add-f32" { float := [.add .f32] } "test"
/-- Only `div.approx.f32`, as an exact quotient. -/
private def approxDivF32 : Assumption :=
  Assumption.approxExact "test-approx-div-f32" [.div .f32] "test"

private def thread (x y : ℝ) : TState :=
  { regs := fun r => if r = 1 then some (.float .f32 x)
    else if r = 0 then some (.float .f32 y) else none }

/-- A floating instruction with destination register 2 and sources registers 1 and 0. -/
private def fl (op : FOp) (fmt : FloatFmt) (rnd : Option FloatRound := none)
    (mode : FMode := .ieee) : Op :=
  .float { op, ty := ⟨fmt, 1⟩, rnd, mode, dsts := [some 2], srcs := [.reg 1, .reg 0] }

-- `add.rn.f32` is a form of `idealAddF32`; `mul.rn.f32`, `add.rn.f16`, `div.approx.f32` are not.
example : Assumption.FloatForm.ofOp (fl .add .f32 (some .rn)) = some (.add .f32) := rfl
example (x y : ℝ) : (idealAddF32.localRule launch 0 (thread x y) (fl .mul .f32 (some .rn))) =
    none := by
  simp [idealAddF32, Assumption.idealReal, Assumption.FloatForm.ofOp, fl]
example (x y : ℝ) : (idealAddF32.localRule launch 0 (thread x y) (fl .add .f16 (some .rn))) =
    none := by
  simp [idealAddF32, Assumption.idealReal, Assumption.FloatForm.ofOp, fl]
example (x y : ℝ) : (idealAddF32.localRule launch 0 (thread x y)
    (fl .div .f32 none .approx)) = none := by
  simp [idealAddF32, Assumption.idealReal, Assumption.FloatForm.ofOp, fl]

-- With the arithmetic assumption alone, `div.approx.f32` has no assumption rule; the scoped
-- approximate assumption selects it and no addition.
example (x y : ℝ) : (approxDivF32.localRule launch 0 (thread x y)
    (fl .div .f32 none .approx)).isSome := by
  simp [approxDivF32, Assumption.approxExact, Assumption.ApproxForm.ofOp, fl,
    Assumption.execApproxExact, Assumption.readFinite, Assumption.readERealOpnd, thread, readReg,
    Assumption.readEReal, Assumption.bindRead, pure, Except.pure, EReal.coe_ne_top,
    EReal.coe_ne_bot]
example (x y : ℝ) : (approxDivF32.localRule launch 0 (thread x y)
    (fl .add .f32 (some .rn))) = none := by
  simp [approxDivF32, Assumption.approxExact, Assumption.ApproxForm.ofOp, fl]

example (L : Launch) (mem0 : Mem0) (X : Execution) :
    idealAddF32.wf L mem0 X ∧ ¬ idealAddF32.ub L mem0 X :=
  ⟨trivial, not_false⟩

end
end PTX.Tests.NumericalProfile
