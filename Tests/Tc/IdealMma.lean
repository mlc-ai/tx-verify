-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal
public import Mathlib.Tactic.NormNum

namespace PTX.Tests.IdealMma
open Assumption
noncomputable section

private def desc : TcMma.Descriptor :=
  ⟨.two, .f16 .f16 .f32, 128, 16, false, false, false, false, false⟩
private def scalar (x : ℝ) : List (Option Byte) :=
  [some (.float .f16 x, 0), some (.float .f16 x, 1)]

example (x : ℝ) : idealMmaElement (.f16 .f16 .f32) .a (scalar x) 0 0 = .ok x := by
  simp [idealMmaElement, TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, scalar, rebuild,
    Value.toBytes, Value.bytes,
    FloatFmt.bytes, Value.byteAt, valFloat, List.range_succ]
  rfl

example (x y : ℝ) : idealMmaDot desc (scalar x) (scalar y) 0 0 1 = .ok (x * y) := by
  simp [idealMmaDot, idealMmaElement, TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, scalar,
    desc, rebuild, Value.toBytes,
    Value.bytes, FloatFmt.bytes, Value.byteAt, valFloat, List.range_succ]
  rfl

example (x y : ℝ) :
    idealMmaDot { desc with negateA := true } (scalar x) (scalar y) 0 0 1 =
      .ok (-x * y) := by
  simp [idealMmaDot, idealMmaElement, TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, scalar,
    desc, rebuild, Value.toBytes,
    Value.bytes, FloatFmt.bytes, Value.byteAt, valFloat, List.range_succ]
  rfl

-- A missing operand array is rejected even with accumulation disabled.
example : execIdealMma desc false [] [] none 0 0 = .error .noRule := by
  simp [execIdealMma, desc, TcMma.Valid]
  rfl

example (old : Option Value) : idealMmaAccumulator .f32 false old = .ok 0 := rfl
example : idealMmaAccumulator .f32 true none = .error .uninitialized := rfl
example (x : ℝ) : idealMmaAccumulator .f32 true (some (.float .f32 x)) = .ok x := by
  simp [idealMmaAccumulator, valFloat]; rfl
example (x : ℝ) : idealMmaAccumulator .f32 true (some (.float .f16 x)) =
    .error .typeMismatch := rfl
example (x : ℝ) : idealMmaElement (.f16 .bf16 .f32) .a
    [some (.float .bf16 x, 0), some (.float .bf16 x, 1)] 0 0 = .ok x := by
  simp [idealMmaElement, TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, rebuild, Value.toBytes,
    Value.bytes, FloatFmt.bytes,
    Value.byteAt, valFloat, List.range_succ]
  rfl

-- Integer kinds are not floating: the profile has no rule for them.
example : execIdealMma { desc with kind := .i8 true true false } false [] [] none 0 0 =
    .error .noRule := rfl

-- The constructor's `mmaRule` covers exactly the kinds it names.
example : (idealReal "t" { mma := [.f16 .f16 .f32] } "t").mmaRule
    desc false [] [] none 0 0 = some (execIdealMma desc false [] [] none 0 0) := by
  simp [idealReal, desc]
example : (idealReal "t" { mma := [.f16 .bf16 .f32] } "t").mmaRule
    desc false [] [] none 0 0 = none := by
  simp [idealReal, desc]

-- No numerical profile is supplied implicitly by the assumption interface.
example : ({ name := "empty", statement := "empty" } : Assumption).mmaRule
    desc false [] [] none 0 0 = none := rfl

end
end PTX.Tests.IdealMma
