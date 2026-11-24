-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Integer conversions of THREAD-CVT: `cvt` between integer types (§6.5.1 Table 15, §9.7.10.24)
with `.sat` and with registers wider than the types (§9.4.1 Tables 27 and 28), and `cvt.pack`
(§9.7.10.25). Every expected value is derived from the manual's text. The examples also check the
decoding (PROG-ISA-CVT), the rule of the instruction (`CvtInstr.rule`) and the dispatch of
`execLocal`. -/
namespace PTX.Tests.CvtInt
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%rc".toList, 2, 8⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5, %rs0..%rs1 = 6..7, %rc0..%rc1 = 8..9
private def r (n : String) : Syntax.Operand := .register n

private def int (k : IType) (w : Nat) : DType := .int k w

/-- `cvt.<dk><dw>.<sk><sw>` of the immediate `v` into register 0, with `.sat` when `sat` and the
destination register extension `ext`. -/
private def ex (dk : IType) (dw : Nat) (sk : IType) (sw : Nat) (v : Int) (sat : Bool := false)
    (ext : MemExt := .same) : Exec TState :=
  execLocal launch 0 {}
    (.cvt { dst := int dk dw, src := int sk sw, sat, d := 0, ext, srcs := [.imm v] })

/-- The outcome in which register 0 receives the `w`-bit value `v`. -/
private def out (w : Nat) (v : Nat) : Exec TState :=
  .ok (next (setReg {} 0 (.bits w (.ofNat 64 v))))

/-! ## Chop, sign extension and zero extension (§6.5.1 Table 15) -/

-- `cvt.s32.s8` sign-extends; the source is the low 8 bits of its operand (Table 27: chop).
example : ex .s 32 .s 8 0x80 = out 32 0xFFFFFF80 := rfl
example : ex .s 32 .s 8 0x7F = out 32 0x7F := rfl
example : ex .s 32 .s 8 0x1FF = out 32 0xFFFFFFFF := rfl
-- The extension follows the source type: `cvt.u32.s8` sign-extends, `cvt.s32.u8` zero-extends.
example : ex .u 32 .s 8 0xFF = out 32 0xFFFFFFFF := rfl
example : ex .s 32 .u 8 0xFF = out 32 0xFF := rfl
example : ex .s 64 .s 32 (-2) = out 64 0xFFFFFFFFFFFFFFFE := rfl
example : ex .u 64 .u 32 0xFFFFFFFF = out 64 0xFFFFFFFF := rfl
-- Narrowing chops: `cvt.s16.u32` keeps the low 16 bits.
example : ex .s 16 .u 32 0x12348765 = out 16 0x8765 := rfl
example : ex .u 8 .s 64 (-1) = out 8 0xFF := rfl
-- Same size: no conversion (`cvt.u32.s32`).
example : ex .u 32 .s 32 (-1) = out 32 0xFFFFFFFF := rfl

/-! ## A destination register wider than the type (Table 15 note 1, Table 28) -/

-- `cvt.s8.s32` into a 16-bit register chops to 8 bits and sign-extends to 16.
example : ex .s 8 .s 32 0x180 (ext := .sign 16) = out 16 0xFF80 := rfl
example : ex .s 8 .s 32 0x17F (ext := .sign 16) = out 16 0x7F := rfl
-- `cvt.u8.s32` into a 16-bit register zero-extends; `cvt.s16.u32` into 32 bits sign-extends.
example : ex .u 8 .s 32 (-1) (ext := .zero 16) = out 16 0xFF := rfl
example : ex .s 16 .u 32 0x18000 (ext := .sign 32) = out 32 0xFFFF8000 := rfl

/-! ## `.sat` (§9.7.10.24: "limits the result to MININT..MAXINT for the size of the operation") -/

example : ex .s 8 .s 32 300 (sat := true) (ext := .sign 16) = out 16 0x7F := rfl
example : ex .s 8 .s 32 (-300) (sat := true) (ext := .sign 16) = out 16 0xFF80 := rfl
example : ex .u 8 .s 32 (-5) (sat := true) (ext := .zero 16) = out 16 0 := rfl
example : ex .u 32 .s 32 (-1) (sat := true) = out 32 0 := rfl
example : ex .s 32 .u 32 0xFFFFFFFF (sat := true) = out 32 0x7FFFFFFF := rfl
example : ex .u 16 .u 32 0x10000 (sat := true) = out 16 0xFFFF := rfl
example : ex .u 16 .u 32 0xFFFF (sat := true) = out 16 0xFFFF := rfl
example : ex .s 64 .u 64 0xFFFFFFFFFFFFFFFF (sat := true) = out 64 0x7FFFFFFFFFFFFFFF := rfl
example : ex .u 64 .s 64 (-7) (sat := true) = out 64 0 := rfl

/-! ## Registers -/

-- An unsigned conversion reads the low bits of a wider register and keeps the form of the result
-- that proofs about it use.
example (x : BitVec 64) :
    execLocal launch 0 (setReg {} 6 (.bits 16 x))
      (.cvt { dst := int .u 32, src := int .u 16, d := 0, srcs := [.reg 6] }) =
    .ok (next (setReg (setReg {} 6 (.bits 16 x)) 0 (.bits 32 (truncBits 32 (truncBits 16 x))))) :=
  rfl
-- A signed source in a 32-bit register.
example : execLocal launch 0 (setReg {} 1 (.bits 32 0x1234_5680))
      (.cvt { dst := int .s 32, src := int .s 8, d := 0, srcs := [.reg 1] }) =
    .ok (next (setReg (setReg {} 1 (.bits 32 0x1234_5680)) 0 (.bits 32 0xFFFFFF80))) := rfl
-- An unsigned conversion keeps a symbolic shared pointer; a signed one has no rule.
example : execLocal launch 0 (setReg {} 4 (.ptr 64 false (.shared 0 0) 16))
      (.cvt { dst := int .u 32, src := int .u 64, d := 0, srcs := [.reg 4] }) =
    .ok (next (setReg (setReg {} 4 (.ptr 64 false (.shared 0 0) 16)) 0
      (.ptr 32 false (.shared 0 0) 16))) := rfl
example : execLocal launch 0 (setReg {} 4 (.ptr 64 false (.shared 0 0) 16))
      (.cvt { dst := int .s 32, src := int .s 64, d := 0, srcs := [.reg 4] }) = .error .noRule :=
  rfl

/-! ## `cvt.pack` (§9.7.10.25) -/

/-- `cvt.pack.sat.<k><w>.s32{.b32}` of immediates into register 0. -/
private def pk (k : IType) (w : Nat) (srcs : List Int) : Exec TState :=
  execLocal launch 0 {} (.cvt {
    dst := int k w, src := int .s 32, sat := true, pack := true, d := 0, srcs := srcs.map .imm })

-- `b` in the low half, `a` in the high half, each clamped to `.s16`.
example : pk .s 16 [40000, -40000] = out 32 0x7FFF8000 := rfl
example : pk .u 16 [-1, 70000] = out 32 0x0000FFFF := rfl
-- `cvt.pack.sat.u8.s32.b32`: the low 16 bits of `c` above the two bytes.
example : pk .u 8 [300, -1, 0x1234] = out 32 0x1234FF00 := rfl
example : pk .s 8 [-200, 5, 0] = out 32 0x8005 := rfl
-- `u4` and `s2`: the low 24 or 28 bits of `c` above `2 size` bits.
example : pk .u 4 [7, 20, 0xABCDEF12] = out 32 0xCDEF127F := rfl
example : pk .s 2 [-3, 1, 0] = out 32 9 := rfl

/-! ## Rules -/

example : CvtInstr.rule {
    dst := int .s 8, src := int .s 32, sat := true, d := 0, ext := .sign 16, srcs := [.imm 0] } =
    some .threadCvt := rfl
example : CvtInstr.rule { dst := int .u 32, src := int .u 64, d := 0, srcs := [.imm 0] } =
    some .threadCvt := rfl
example : CvtInstr.rule {
    dst := int .u 8, src := int .s 32, sat := true, pack := true, d := 0,
    srcs := [.imm 0, .imm 0, .imm 0] } = some .threadCvt := rfl
-- An integer conversion with a rounding modifier is no `cvt` form; it has no rule.
example : CvtInstr.rule {
    dst := int .s 32, src := int .s 8, rnd := some .rn, d := 0, srcs := [.imm 0] } = none := rfl
example : execLocal launch 0 {} (.cvt {
    dst := int .s 32, src := int .s 8, rnd := some .rn, d := 0, srcs := [.imm 0] }) =
    .error .noRule := rfl

/-! ## Decoding (§9.4.1 Tables 27 and 28) -/

example : Decode.op env "cvt.s32.s8" [r "%r0", r "%r1"] =
    .ok (.cvt { dst := int .s 32, src := int .s 8, d := 0, srcs := [.reg 1] }) := rfl
example : Decode.op env "cvt.s32.s8" [r "%r0", r "%rc1"] =
    .ok (.cvt { dst := int .s 32, src := int .s 8, d := 0, srcs := [.reg 9] }) := rfl
example : Decode.op env "cvt.s8.s32" [r "%rs0", r "%r0"] =
    .ok (.cvt { dst := int .s 8, src := int .s 32, d := 6, ext := .sign 16, srcs := [.reg 0] }) :=
  rfl
example : Decode.op env "cvt.u8.s32" [r "%rc0", r "%r0"] =
    .ok (.cvt { dst := int .u 8, src := int .s 32, d := 8, srcs := [.reg 0] }) := rfl
example : Decode.op env "cvt.sat.u16.s64" [r "%r0", r "%rd1"] =
    .ok (.cvt {
      dst := int .u 16, src := int .s 64, sat := true, d := 0, ext := .zero 32,
      srcs := [.reg 5] }) := rfl
example : Decode.op env "cvt.u32.u16" [r "%r0", r "%tid.x"] =
    .ok (.cvt { dst := int .u 32, src := int .u 16, d := 0, srcs := [.sreg ⟨.tid, some .x⟩] }) :=
  rfl
example : Decode.op env "cvt.pack.sat.u8.s32.b32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.cvt {
      dst := int .u 8, src := int .s 32, sat := true, pack := true, d := 0,
      srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
-- Rejected: a register narrower than its type, and a `.bf16` operand in a wider register.
example : (Decode.op env "cvt.u32.u16" [r "%rs0", r "%rs1"]).isOk = false := rfl
example : (Decode.op env "cvt.s64.s32" [r "%rd0", r "%rs1"]).isOk = false := rfl
example : (Decode.op env "cvt.f32.bf16" [r "%r0", r "%r1"]).isOk = false := rfl
-- `.sat` where the destination range contains the source range is not a `cvt` form.
example : (Decode.op env "cvt.sat.s32.s8" [r "%r0", r "%r1"]).isOk = false := rfl

end
end PTX.Tests.CvtInt
