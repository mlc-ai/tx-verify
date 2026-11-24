-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Data movement of THREAD-MOVE: `mov` of a predicate (§9.7.10.3), `mov` that packs and unpacks
two or four elements into `.b16` to `.b128` registers (§9.7.10.4), with the sink `_` among the
destinations of an unpack, and `slct` with an `.s32` or `.f32` selector (§9.7.7.4). Every
expected value is derived from the Semantics text of the manual. The examples also check
`MoveInstr.rule`, the decoding of the forms and the dispatch of `execLocal`. -/
namespace PTX.Tests.IntOpsMove
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 4, 16⟩,
      ⟨"%q".toList, 2, 128⟩, ⟨"%p".toList, 3, 1⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5, %rs0..%rs3 = 6..9, %q0..%q1 = 10..11,
-- %p0..%p2 = 12..14
private def r (n : String) : Syntax.Operand := .register n

private def b16 : DType := .int .b 16
private def b32 : DType := .int .b 32
private def b64 : DType := .int .b 64
private def b128 : DType := .int .b 128
private def u32 : DType := .int .u 32

/-! ## mov of a predicate -/

example : Decode.op env "mov.pred" [r "%p0", r "%p1"] =
    .ok (.move ⟨.scalar, .pred, [some 12], [.reg 13]⟩) := rfl
example : MoveInstr.rule ⟨.scalar, .pred, [some 12], [.reg 13]⟩ = some .threadMove := rfl
private def withP (b : Bool) : TState := setReg {} 13 (.pred b)
example : execLocal launch 0 (withP true) (.move ⟨.scalar, .pred, [some 12], [.reg 13]⟩) =
    .ok (next (setReg (withP true) 12 (.pred true))) := rfl
example : execLocal launch 0 (withP false) (.move ⟨.scalar, .pred, [some 12], [.reg 13]⟩) =
    .ok (next (setReg (withP false) 12 (.pred false))) := rfl
-- The source of a predicate move is a predicate; a 32-bit register is a type error.
example : execLocal launch 0 (setReg {} 13 (.bits 32 1))
    (.move ⟨.scalar, .pred, [some 12], [.reg 13]⟩) = .error .typeMismatch := rfl
-- An integer constant is a predicate source: zero is false, non-zero true (§4.5.3).
example : Decode.op env "mov.pred" [r "%p0", .literal "-1"] =
    .ok (.move ⟨.scalar, .pred, [some 12], [.imm (-1)]⟩) := rfl
example : Decode.op env "mov.pred" [r "%p0", .literal "0"] =
    .ok (.move ⟨.scalar, .pred, [some 12], [.imm 0]⟩) := rfl
example : execLocal launch 0 {}
    (.move ⟨.scalar, .pred, [some 12], [.imm (-1)]⟩) =
    .ok (next (setReg {} 12 (.pred true))) := rfl
example : execLocal launch 0 {}
    (.move ⟨.scalar, .pred, [some 12], [.imm 0]⟩) =
    .ok (next (setReg {} 12 (.pred false))) := rfl
example : execLocal launch 0 {}
    (.move ⟨.scalar, .pred, [some 12], [.imm 7]⟩) =
    .ok (next (setReg {} 12 (.pred true))) := rfl
-- A floating literal is not a predicate constant.
example : (Decode.op env "mov.pred" [r "%p0", .literal "0f3f800000"]).isOk = false := rfl
example : (Decode.op env "mov.pred" [r "%p0", .literal "0f00000000"]).isOk = false := rfl
example : (Decode.op env "mov.pred" [r "%r0", .literal "0"]).isOk = false := rfl
example : execLocal launch 0 (withP true) (.move ⟨.scalar, .pred, [some 12], [.imm 0]⟩) =
    .ok (next (setReg (withP true) 12 (.pred false))) := rfl
example : execLocal launch 0 (withP false) (.move ⟨.scalar, .pred, [some 12], [.imm (-1)]⟩) =
    .ok (next (setReg (withP false) 12 (.pred true))) := rfl

/-! ## mov of one register -/

example : execLocal launch 0 (setReg {} 1 (.bits 32 0xDEADBEEF))
    (.move ⟨.scalar, b32, [some 0], [.reg 1]⟩) =
    .ok (next (setReg (setReg {} 1 (.bits 32 0xDEADBEEF)) 0 (.bits 32 0xDEADBEEF))) := rfl
example : execLocal launch 0 {} (.move ⟨.scalar, b64, [some 4], [.imm 0x123456789ABCDEF0]⟩) =
    .ok (next (setReg {} 4 (.bits 64 0x123456789ABCDEF0))) := rfl

/-! ## pack and unpack of four 16-bit elements into `.b64` -/

private def halves : TState :=
  setReg (setReg (setReg (setReg {} 6 (.bits 16 0x1111)) 7 (.bits 16 0x2222)) 8 (.bits 16 0x3333))
    9 (.bits 16 0x4444)
example : Decode.op env "mov.b64" [r "%rd0", .vector [r "%rs0", r "%rs1", r "%rs2", r "%rs3"]] =
    .ok (.move ⟨.pack, b64, [some 4], [.reg 6, .reg 7, .reg 8, .reg 9]⟩) := rfl
example : Decode.op env "mov.b64" [.vector [r "%rs0", r "%rs1", r "%rs2", r "%rs3"], r "%rd0"] =
    .ok (.move ⟨.unpack, b64, [some 6, some 7, some 8, some 9], [.reg 4]⟩) := rfl
example : MoveInstr.rule ⟨.pack, b64, [some 4], [.reg 6, .reg 7, .reg 8, .reg 9]⟩ =
    some .threadMove := rfl
example : MoveInstr.rule ⟨.unpack, b64, [some 6, some 7, some 8, some 9], [.reg 4]⟩ =
    some .threadMove := rfl
-- d = a.x | (a.y << 16) | (a.z << 32) | (a.w << 48)
example : execLocal launch 0 halves
    (.move ⟨.pack, b64, [some 4], [.reg 6, .reg 7, .reg 8, .reg 9]⟩) =
    .ok (next (setReg halves 4 (.bits 64 0x4444333322221111))) := rfl
-- { d.x, d.y, d.z, d.w } = { a[0..15], a[16..31], a[32..47], a[48..63] }
private def word64 : TState := setReg {} 4 (.bits 64 0x4444333322221111)
example : execLocal launch 0 word64
    (.move ⟨.unpack, b64, [some 6, some 7, some 8, some 9], [.reg 4]⟩) =
    .ok (next (setReg (setReg (setReg (setReg word64 6 (.bits 16 0x1111)) 7 (.bits 16 0x2222))
      8 (.bits 16 0x3333)) 9 (.bits 16 0x4444))) := rfl
-- Immediate elements pack in the same way.
example : execLocal launch 0 {}
    (.move ⟨.pack, b64, [some 4], [.imm 0x1234, .imm 0, .imm 0xFFFF, .imm 0x8000]⟩) =
    .ok (next (setReg {} 4 (.bits 64 0x8000FFFF00001234))) := rfl

/-! ## pack and unpack of four 32-bit elements into `.b128` -/

-- The value of a 128-bit register is its low and its high 64-bit half.
private def words : TState :=
  setReg (setReg (setReg (setReg {} 0 (.bits 32 0x11111111)) 1 (.bits 32 0x22222222)) 2
    (.bits 32 0x33333333)) 3 (.bits 32 0x44444444)
private def quad : Value := .pair (.bits 64 0x2222222211111111) (.bits 64 0x4444444433333333)
example : Decode.op env "mov.b128" [r "%q0", .vector [r "%r0", r "%r1", r "%r2", r "%r3"]] =
    .ok (.move ⟨.pack, b128, [some 10], [.reg 0, .reg 1, .reg 2, .reg 3]⟩) := rfl
example : Decode.op env "mov.b128" [.vector [r "%r0", r "%r1", r "%r2", r "%r3"], r "%q0"] =
    .ok (.move ⟨.unpack, b128, [some 0, some 1, some 2, some 3], [.reg 10]⟩) := rfl
example : MoveInstr.rule ⟨.pack, b128, [some 10], [.reg 0, .reg 1, .reg 2, .reg 3]⟩ =
    some .threadMove := rfl
example : MoveInstr.rule ⟨.unpack, b128, [some 0, some 1, some 2, some 3], [.reg 10]⟩ =
    some .threadMove := rfl
-- d = a.x | (a.y << 32) | (a.z << 64) | (a.w << 96)
example : execLocal launch 0 words
    (.move ⟨.pack, b128, [some 10], [.reg 0, .reg 1, .reg 2, .reg 3]⟩) =
    .ok (next (setReg words 10 quad)) := rfl
-- { d.x, d.y, d.z, d.w } = { a[0..31], a[32..63], a[64..95], a[96..127] }
private def withQuad : TState := setReg {} 10 quad
example : execLocal launch 0 withQuad
    (.move ⟨.unpack, b128, [some 0, some 1, some 2, some 3], [.reg 10]⟩) =
    .ok (next (setReg (setReg (setReg (setReg withQuad 0 (.bits 32 0x11111111)) 1
      (.bits 32 0x22222222)) 2 (.bits 32 0x33333333)) 3 (.bits 32 0x44444444))) := rfl
-- Two 64-bit elements: d = a.x | (a.y << 64), and the inverse.
private def dwords : TState := setReg (setReg {} 4 (.bits 64 0x2222222211111111)) 5
  (.bits 64 0x4444444433333333)
example : execLocal launch 0 dwords (.move ⟨.pack, b128, [some 10], [.reg 4, .reg 5]⟩) =
    .ok (next (setReg dwords 10 quad)) := rfl
example : execLocal launch 0 withQuad (.move ⟨.unpack, b128, [some 4, some 5], [.reg 10]⟩) =
    .ok (next (setReg (setReg withQuad 4 (.bits 64 0x2222222211111111)) 5
      (.bits 64 0x4444444433333333))) := rfl
-- Two 32-bit elements into `.b64`: d = a.x | (a.y << 32).
example : execLocal launch 0 words (.move ⟨.pack, b64, [some 4], [.reg 0, .reg 1]⟩) =
    .ok (next (setReg words 4 (.bits 64 0x2222222211111111))) := rfl
example : execLocal launch 0 word64 (.move ⟨.unpack, b64, [some 0, some 1], [.reg 4]⟩) =
    .ok (next (setReg (setReg word64 0 (.bits 32 0x22221111)) 1 (.bits 32 0x44443333))) := rfl

/-! ## Unpack with the sink `_` -/

-- Only the named registers change: `mov.b64 {%r1, _}, %rd0` writes the low half.
private def wide : TState := setReg {} 4 (.bits 64 0x1122334455667788)
example : Decode.op env "mov.b64" [.vector [r "%r1", .sink], r "%rd0"] =
    .ok (.move ⟨.unpack, b64, [some 1, none], [.reg 4]⟩) := rfl
example : Decode.op env "mov.b64" [.vector [.sink, r "%r1"], r "%rd0"] =
    .ok (.move ⟨.unpack, b64, [none, some 1], [.reg 4]⟩) := rfl
example : MoveInstr.rule ⟨.unpack, b64, [some 1, none], [.reg 4]⟩ = some .threadMove := rfl
example : execLocal launch 0 wide (.move ⟨.unpack, b64, [some 1, none], [.reg 4]⟩) =
    .ok (next (setReg wide 1 (.bits 32 0x55667788))) := rfl
example : execLocal launch 0 wide (.move ⟨.unpack, b64, [none, some 1], [.reg 4]⟩) =
    .ok (next (setReg wide 1 (.bits 32 0x11223344))) := rfl
-- Four elements with sinks: `mov.b64 {%rs0, _, %rs2, _}, %rd0`.
example : Decode.op env "mov.b64" [.vector [r "%rs0", .sink, r "%rs2", .sink], r "%rd0"] =
    .ok (.move ⟨.unpack, b64, [some 6, none, some 8, none], [.reg 4]⟩) := rfl
example : MoveInstr.rule ⟨.unpack, b64, [some 6, none, some 8, none], [.reg 4]⟩ =
    some .threadMove := rfl
example : execLocal launch 0 wide (.move ⟨.unpack, b64, [some 6, none, some 8, none], [.reg 4]⟩) =
    .ok (next (setReg (setReg wide 6 (.bits 16 0x7788)) 8 (.bits 16 0x3344))) := rfl
example : execLocal launch 0 wide (.move ⟨.unpack, b64, [none, some 7, none, some 9], [.reg 4]⟩) =
    .ok (next (setReg (setReg wide 7 (.bits 16 0x5566)) 9 (.bits 16 0x1122))) := rfl
-- Four 32-bit elements of a `.b128` value with sinks.
example : execLocal launch 0 withQuad
    (.move ⟨.unpack, b128, [none, some 1, none, some 3], [.reg 10]⟩) =
    .ok (next (setReg (setReg withQuad 1 (.bits 32 0x22222222)) 3 (.bits 32 0x44444444))) := rfl
-- An unpack whose destinations are all sinks writes nothing, so it has no rule; the decoder
-- rejects it too.
example : MoveInstr.rule ⟨.unpack, b64, [none, none], [.reg 4]⟩ = none := rfl
example : MoveInstr.rule ⟨.unpack, b64, [none, none, none, none], [.reg 4]⟩ = none := rfl
example : execLocal launch 0 wide (.move ⟨.unpack, b64, [none, none], [.reg 4]⟩) =
    .error .noRule := rfl
example : (Decode.op env "mov.b64" [.vector [.sink, .sink], r "%rd0"]).isOk = false := rfl
-- No rule for an element count or size outside the syntax.
example : MoveInstr.rule ⟨.unpack, b16, [some 6, some 7, some 8, some 9], [.reg 4]⟩ = none := rfl
example : MoveInstr.rule ⟨.pack, b64, [some 4], [.reg 6, .reg 7, .reg 8]⟩ = none := rfl
example : MoveInstr.rule ⟨.pack, u32, [some 4], [.reg 6, .reg 7]⟩ = none := rfl

/-! ## slct (§9.7.7.4): d = (c >= 0) ? a : b -/

private def s32 : DType := .int .s 32
private def f32 : DType := .float .f32
private def slct (ct : DType) (c : Opnd) : Exec TState :=
  execLocal launch 0 {} (.int ⟨.slct ct false, u32, false, [some 0], [.imm 11, .imm 22, c]⟩)
private def picked (v : Nat) : Exec TState := .ok (next (setReg {} 0 (.bits 32 (.ofNat 64 v))))
example : Decode.op env "slct.u32.s32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.int ⟨.slct s32 false, u32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) := rfl
example : IntInstr.rule ⟨.slct s32 false, u32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩ =
    some .threadMove := rfl
example : IntInstr.rule ⟨.slct f32 false, u32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩ =
    some .threadMove := rfl
-- `.s32` selector: 0 and positive values pick `a`, negative values pick `b`.
example : slct s32 (.imm 0) = picked 11 := rfl
example : slct s32 (.imm 5) = picked 11 := rfl
example : slct s32 (.imm 0x7FFFFFFF) = picked 11 := rfl
example : slct s32 (.imm (-1)) = picked 22 := rfl
example : slct s32 (.imm 0x80000000) = picked 22 := rfl
-- `.f32` selector, given as the `0f` patterns of the manual's comparison rules.
example : slct f32 (.f32imm 0x80000000) = picked 11 := rfl
example : slct f32 (.f32imm 0x00000000) = picked 11 := rfl
example : slct f32 (.f32imm 0x7FC00000) = picked 22 := rfl
example : slct f32 (.f32imm 0xFFC00000) = picked 22 := rfl
example : slct f32 (.f32imm 0x80000001) = picked 22 := rfl
example : slct f32 (.f32imm 0x00000001) = picked 11 := rfl
example : slct f32 (.f32imm 0x3F800000) = picked 11 := rfl
example : slct f32 (.f32imm 0xBF800000) = picked 22 := rfl
example : slct f32 (.f32imm 0x7F800000) = picked 11 := rfl
example : slct f32 (.f32imm 0xFF800000) = picked 22 := rfl
-- The selector may be a register; the selected value is copied unchanged.
example : execLocal launch 0 (setReg {} 3 (.bits 32 0x80000000))
    (.int ⟨.slct f32 false, u32, false, [some 0], [.imm 11, .imm 22, .reg 3]⟩) =
    .ok (next (setReg (setReg {} 3 (.bits 32 0x80000000)) 0 (.bits 32 11))) := rfl

-- `.ftz` (§9.7.7.4: "slct.ftz.dtype.f32 flushes subnormal values of operand c to sign-preserving
-- zero, and operand a is selected."): a negative subnormal selects `a`; normal values and NaN
-- are unchanged.
private def slctFtz (c : Opnd) : Exec TState :=
  execLocal launch 0 {} (.int ⟨.slct f32 true, u32, false, [some 0], [.imm 11, .imm 22, c]⟩)
example : Decode.op env "slct.ftz.u32.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.int ⟨.slct f32 true, u32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) := rfl
example : slctFtz (.f32imm 0x80000001) = picked 11 := rfl
example : slctFtz (.f32imm 0x807FFFFF) = picked 11 := rfl
example : slctFtz (.f32imm 0x80800000) = picked 22 := rfl
example : slctFtz (.f32imm 0xFFC00000) = picked 22 := rfl
-- `.ftz` applies only to `.f32` comparisons.
example : IntInstr.rule ⟨.slct s32 true, u32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩ = none :=
  rfl

end
end PTX.Tests.IntOpsMove
