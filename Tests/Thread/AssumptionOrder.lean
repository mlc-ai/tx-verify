-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Assumption.ApproxExact

/-! THREAD-LOCAL: kernel assumptions are consulted before the Core rule. An assumption that selects
nothing leaves the Core rule unchanged, and the floating assumptions select only the forms they
name. -/
namespace PTX.Tests.AssumptionOrder
noncomputable section

private def launch : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- An assumption with no hooks: it selects no instruction. -/
private def silent : Assumption := { name := "silent", statement := "" }

example (t : TState) (op : Op) : execLocalRule [silent] launch 0 t op = execLocal launch 0 t op :=
  execLocalRule_of_none (by simp [silent])

example (t : TState) (op : Op) : execLocalRule [] launch 0 t op = execLocal launch 0 t op :=
  execLocalRule_of_none (by simp)

/-- `idealReal` naming only `add.f32`, `approxExact` naming only `ex2.approx.f32`. -/
private def ideal : Assumption := Assumption.idealReal "t" { float := [.add .f32] } ""
private def approx : Assumption := Assumption.approxExact "t" [.ex2 .f32] ""

-- An integer instruction and the floating forms outside the scopes are not selected.
example (t : TState) : ideal.localRule launch 0 t
    (.int ⟨.add, .int .s 32, false, [some 0], [.reg 1, .reg 2]⟩) = none := rfl
example (t : TState) : approx.localRule launch 0 t
    (.int ⟨.add, .int .s 32, false, [some 0], [.reg 1, .reg 2]⟩) = none := rfl
example (t : TState) : ideal.localRule launch 0 t
    (.float { op := .mul, ty := ⟨.f32, 1⟩, rnd := some .rn
              dsts := [some 0], srcs := [.reg 1, .reg 2] }) = none := by
  simp [ideal, Assumption.idealReal, Assumption.FloatForm.ofOp]
example (t : TState) : approx.localRule launch 0 t
    (.float { op := .rcp, ty := ⟨.f32, 1⟩, mode := .approx
              dsts := [some 0], srcs := [.reg 1] }) = none := by
  simp [approx, Assumption.approxExact, Assumption.ApproxForm.ofOp]

end
end PTX.Tests.AssumptionOrder
