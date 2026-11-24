-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Lemmas.Register.RegisterFrame

/-! Integer and predicate forms of PROG-DECODE and THREAD-INT: `mul.hi` and `mul.wide` of
16-bit types (§9.7.1.3), `min`/`max` (§9.7.1.13, §9.7.1.14), predicate `and`/`or`/`xor`/`not`
(§9.7.9.1–§9.7.9.4, §9.3.2) and signed `shr` (§9.7.9.9), each in its FA4 spelling, with
rejected neighbours and execution examples. -/
namespace PTX.Tests.IntegerForms
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%p".toList, 3, 1⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5, %rs0..%rs1 = 6..7, %p0..%p2 = 8..10
private def r (n : String) : Syntax.Operand := .register n

/-! ## Decoding -/

example : Decode.op env "not.pred" [r "%p2", r "%p1"] =
    .ok (.int ⟨.not, .pred, false, [some 10], [.reg 9]⟩) := rfl
example : Decode.op env "and.pred" [r "%p2", r "%p0", r "%p1"] =
    .ok (.int ⟨.and, .pred, false, [some 10], [.reg 8, .reg 9]⟩) := rfl
example : Decode.op env "and.pred" [r "%p2", r "%p0", .literal "1"] =
    .ok (.int ⟨.and, .pred, false, [some 10], [.reg 8, .imm 1]⟩) := rfl
example : Decode.op env "or.pred" [r "%p2", r "%p0", r "%p1"] =
    .ok (.int ⟨.or, .pred, false, [some 10], [.reg 8, .reg 9]⟩) := rfl
example : Decode.op env "xor.pred" [r "%p2", r "%p0", r "%p1"] =
    .ok (.int ⟨.xor, .pred, false, [some 10], [.reg 8, .reg 9]⟩) := rfl
example : Decode.op env "not.b32" [r "%r0", r "%r1"] =
    .ok (.int ⟨.not, .int .b 32, false, [some 0], [.reg 1]⟩) := rfl
example : Decode.op env "mul.hi.u32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.int ⟨.mul .hi, .int .u 32, false, [some 0], [.reg 1, .reg 2]⟩) := rfl
example : Decode.op env "mul.hi.s64" [r "%rd0", r "%rd1", .literal "3"] =
    .ok (.int ⟨.mul .hi, .int .s 64, false, [some 4], [.reg 5, .imm 3]⟩) := rfl
example : Decode.op env "mul.wide.u16" [r "%r0", r "%rs0", .literal "8"] =
    .ok (.int ⟨.mul .wide, .int .u 16, false, [some 0], [.reg 6, .imm 8]⟩) := rfl
-- The 32-bit form keeps its earlier term (the width argument defaults to 32).
example : Decode.op env "mul.wide.u32" [r "%rd0", r "%r0", r "%r1"] =
    .ok (.int ⟨.mul .wide, .int .u 32, false, [some 4], [.reg 0, .reg 1]⟩) := rfl
example : Decode.op env "shr.s32" [r "%r0", r "%r1", .literal "31"] =
    .ok (.int ⟨.shr, .int .s 32, false, [some 0], [.reg 1, .imm 31]⟩) := rfl
example : Decode.op env "shr.u32" [r "%r0", r "%r1", .literal "7"] =
    .ok (.int ⟨.shr, .int .u 32, false, [some 0], [.reg 1, .imm 7]⟩) := rfl
example : Decode.op env "shr.b64" [r "%rd0", r "%rd1", r "%r2"] =
    .ok (.int ⟨.shr, .int .b 64, false, [some 4], [.reg 5, .reg 2]⟩) := rfl
example : Decode.op env "max.s32" [r "%r0", r "%r1", .literal "0"] =
    .ok (.int ⟨.max false, .int .s 32, false, [some 0], [.reg 1, .imm 0]⟩) := rfl
example : Decode.op env "min.u16" [r "%rs0", r "%rs1", .literal "5"] =
    .ok (.int ⟨.min false, .int .u 16, false, [some 6], [.reg 7, .imm 5]⟩) := rfl

-- Rejected: a floating literal or a non-predicate register at `.pred` (§9.7.9.1: "Allowed types
-- include predicate registers."; an integer constant is a predicate operand, §4.5.3), `not` of an
-- integer type, `mul.wide` of 64-bit types, a `mul.wide` destination that is not twice as wide,
-- `max` of a bit-size type. `max.relu` decodes with the `.relu` flag as `IntOp.max true` and clamps
-- a negative maximum to 0
-- (§9.7.1.14: "max.relu.{s8x4, s16x2, s32} clamps the result to 0 if negative.").
example : (Decode.op env "and.pred" [r "%p2", r "%p0", .literal "0f3f800000"]).isOk = false := rfl
example : (Decode.op env "and.pred" [r "%p2", r "%p0", .literal "1"]).isOk = true := rfl
example : (Decode.op env "not.pred" [r "%p2", r "%r0"]).isOk = false := rfl
example : (Decode.op env "not.u32" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "mul.wide.u64" [r "%rd0", r "%rd1", r "%rd1"]).isOk = false := rfl
example : (Decode.op env "mul.wide.u16" [r "%rd0", r "%rs0", r "%rs1"]).isOk = false := rfl
example : Decode.op env "max.relu.s32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.int ⟨.max true, .int .s 32, false, [some 0], [.reg 1, .reg 2]⟩) := rfl
example : IntInstr.rule ⟨.max true, .int .s 32, false, [some 0], [.reg 1, .reg 2]⟩ =
    some .threadInt := rfl
example : execLocal launch 0 {}
    (.int ⟨.max true, .int .s 32, false, [some 0], [.imm (-7), .imm (-3)]⟩) =
    .ok (next (setReg {} 0 (.bits 32 0))) := rfl
example : execLocal launch 0 {}
    (.int ⟨.max true, .int .s 32, false, [some 0], [.imm (-7), .imm 5]⟩) =
    .ok (next (setReg {} 0 (.bits 32 5))) := rfl
-- `.relu` on an unsigned type is outside the syntax and has no rule.
example : IntInstr.rule ⟨.max true, .int .u 32, false, [some 0], [.reg 1, .reg 2]⟩ = none := rfl
example : (Decode.op env "max.b32" [r "%r0", r "%r1", r "%r2"]).isOk = false := rfl

/-! ## Execution -/

-- `mul.hi`: the upper half of the double-width product, unsigned or two's complement.
example : execInt launch 0 {}
    ⟨.mul .hi, .int .u 32, false, [some 0], [.imm 0xFFFFFFFF, .imm 0xFFFFFFFF]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFE))) := rfl
example : execInt launch 0 {} ⟨.mul .hi, .int .s 32, false, [some 0], [.imm (-1), .imm 1]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFF))) := rfl
example : execInt launch 0 {}
    ⟨.mul .hi, .int .s 32, false, [some 0], [.imm 0x80000000, .imm 0x80000000]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0x40000000))) := rfl
example : execInt launch 0 {}
    ⟨.mul .hi, .int .u 64, false, [some 4], [.imm 0xFFFFFFFFFFFFFFFF, .imm 2]⟩ =
    .ok (next (setReg {} 4 (.bits 64 1))) := rfl

-- `mul.wide.{u,s}16`: the full 32-bit product.
example : execInt launch 0 {} ⟨.mul .wide, .int .u 16, false, [some 0], [.imm 0xFFFF, .imm 8]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0x7FFF8))) := rfl
example : execInt launch 0 {} ⟨.mul .wide, .int .s 16, false, [some 0], [.imm 0xFFFF, .imm 8]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFF8))) := rfl

-- `shr.s32` fills with the sign bit; an amount above the width is clamped to it.
example : execInt launch 0 {} ⟨.shr, .int .s 32, false, [some 0], [.imm 0x80000000, .imm 31]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFF))) := rfl
example : execInt launch 0 {} ⟨.shr, .int .s 32, false, [some 0], [.imm 0x80000100, .imm 40]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFF))) := rfl
example : execInt launch 0 {} ⟨.shr, .int .s 32, false, [some 0], [.imm 0x7FFFFF00, .imm 7]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0x00FFFFFE))) := rfl
example : execInt launch 0 {} ⟨.shr, .int .u 32, false, [some 0], [.imm 0x80000000, .imm 31]⟩ =
    .ok (next (setReg {} 0 (.bits 32 1))) := rfl

-- `max`/`min`: signed and unsigned differ.
example : execInt launch 0 {} ⟨.max false, .int .s 32, false, [some 0], [.imm (-5), .imm 0]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0))) := rfl
example : execInt launch 0 {} ⟨.max false, .int .u 32, false, [some 0], [.imm (-5), .imm 0]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFB))) := rfl
example : execInt launch 0 {} ⟨.min false, .int .s 32, false, [some 0], [.imm (-5), .imm 3]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFB))) := rfl

-- `not.b32`.
example : execInt launch 0 {} ⟨.not, .int .b 32, false, [some 0], [.imm 0x0F0F0F0F]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0xF0F0F0F0))) := rfl

-- Predicate logic reads and writes predicates.
private def preds : TState := setReg (setReg {} 8 (.pred true)) 9 (.pred false)
example : execInt launch 0 preds ⟨.not, .pred, false, [some 10], [.reg 9]⟩ =
    .ok (next (setReg preds 10 (.pred true))) := rfl
example : execInt launch 0 preds ⟨.and, .pred, false, [some 10], [.reg 8, .reg 9]⟩ =
    .ok (next (setReg preds 10 (.pred false))) := rfl
example : execInt launch 0 preds ⟨.or, .pred, false, [some 10], [.reg 8, .reg 9]⟩ =
    .ok (next (setReg preds 10 (.pred true))) := rfl
example : execInt launch 0 preds ⟨.xor, .pred, false, [some 10], [.reg 8, .reg 8]⟩ =
    .ok (next (setReg preds 10 (.pred false))) := rfl
-- A `.pred` operand that is not a predicate is a type error; an unwritten one is undefined.
example : execInt launch 0 (setReg {} 0 (.bits 32 1)) ⟨.not, .pred, false, [some 10], [.reg 0]⟩ =
    .error .typeMismatch := rfl
example : execInt launch 0 {} ⟨.and, .pred, false, [some 10], [.reg 8, .reg 9]⟩ =
    .error .uninitialized := rfl

-- The register-frame theorem covers the new forms.
example {L : Launch} {g : Nat} {t t' : TState} {d : Nat} {a : Opnd}
    (h : execLocal L g t (.int ⟨.not, .pred, false, [some d], [a]⟩) = .ok t') :
    Proof.LocalFrame (.int ⟨.not, .pred, false, [some d], [a]⟩) t t' := Proof.execLocal_frame h

end
end PTX.Tests.IntegerForms
