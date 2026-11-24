-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.MatrixExec
public import Core.Assumption.IdealReal

/-! A floating warp-level MMA element under ASM-IDEAL (DEP-WARP-MMA, `idealWarpMma`): the exact
sum of the products plus C for the element types the scope names, and no rule for others. -/
namespace PTX.Tests.MatrixIdeal
noncomputable section

private def tF16 : MmaTypes :=
  { a := .float .f16, b := .float .f16, c := .float .f32, d := .float .f32 }
private def spec : MmaSpec := { m := 16, n := 8, k := 8, types := tF16 }
private def ideal : Assumption := Assumption.idealReal "ideal" { warpMma := [tF16] } ""

-- 1 * 3 + 2 * 4 + 5 = 16.
example : mmaValue [ideal] spec [.float .f16 1, .float .f16 2] [.float .f16 3, .float .f16 4]
    (.float .f32 5) = .ok (.float .f32 16) := by
  simp [mmaValue, spec, ideal, tF16, Assumption.idealReal, Assumption.idealWarpMma,
    Assumption.idealWarpElem, valFloat, FType.fmt?]
  norm_num
  rfl

-- Element types the scope does not name keep no rule.
example : mmaValue [ideal] { spec with types := { tF16 with a := .float .bf16, b := .float .bf16 } }
    [.float .bf16 1] [.float .bf16 3] (.float .f32 5) = .error .noRule := by
  simp [mmaValue, ideal, tF16, Assumption.idealReal]
  rfl

-- `.f64` has no payload format: no rule even when the scope names it.
private def tF64 : MmaTypes :=
  { a := .float .f64, b := .float .f64, c := .float .f64, d := .float .f64 }
example : mmaValue [Assumption.idealReal "ideal" { warpMma := [tF64] } ""]
    { m := 8, n := 8, k := 4, types := tF64 } [.bits 64 0] [.bits 64 0] (.bits 64 0) =
    .error .noRule := by
  simp [mmaValue, tF64, Assumption.idealReal, Assumption.idealWarpMma, FType.fmt?]
  rfl

end

end PTX.Tests.MatrixIdeal
