-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode
public import Lemmas.Register.RegisterFrame

namespace PTX.Tests.ScalarOps
noncomputable section

def launch : Launch := { grid := 1, block := 32, params := fun _ => none, sharedBase := 0,
                         clusterSize := 1 }
def env : Decode.Env := { classes := [
  ⟨"d".toList, 0, 32⟩, ⟨"x".toList, 0, 32⟩, ⟨"q".toList, 0, 64⟩,
  ⟨"h".toList, 0, 16⟩, ⟨"p".toList, 0, 1⟩], labels := [], params := [] }

example : Decode.op env "xor.b32" [.register "d", .register "x", .literal "1"] =
    .ok (.int ⟨.xor, .int .b 32, false, [some 0], [.reg 1, .imm 1]⟩) := rfl
example : Decode.op env "cvt.u64.u32" [.register "q", .register "x"] =
    .ok (.cvt { dst := .int .u 64, src := .int .u 32, d := 2, srcs := [.reg 1] }) := rfl
example : Decode.op env "cvt.u32.u64" [.register "d", .register "q"] =
    .ok (.cvt { dst := .int .u 32, src := .int .u 64, d := 0, srcs := [.reg 2] }) := rfl
example : Decode.op env "selp.b32"
    [.register "d", .literal "1", .literal "0", .register "p"] =
    .ok (.int ⟨.selp, .int .b 32, false, [some 0], [.imm 1, .imm 0, .reg 4]⟩) := rfl

#guard !(Decode.op env "xor.u32" [.register "d", .register "x", .literal "1"]).toBool
#guard !(Decode.op env "selp.f16"
  [.register "h", .register "h", .register "h", .register "p"]).toBool
-- `cvt.sat` decodes with its flag, and THREAD-CVT clamps the source to the destination range.
example : Decode.op env "cvt.sat.u32.u64" [.register "d", .register "q"] =
    .ok (.cvt { dst := .int .u 32, src := .int .u 64, sat := true, d := 0, srcs := [.reg 2] }) :=
  rfl
example : CvtInstr.rule
    { dst := .int .u 32, src := .int .u 64, sat := true, d := 0, srcs := [.reg 2] } =
    some .threadCvt := rfl
example : execLocal launch 0 {} (.cvt {
      dst := .int .u 32, src := .int .u 64, sat := true, d := 0, srcs := [.imm 0x100000000] }) =
    .ok (next (setReg {} 0 (.bits 32 0xFFFFFFFF))) := rfl
#guard !(Decode.op env "selp.b32"
  [.register "d", .literal "1", .literal "0", .register "x"]).toBool

-- The phase bit flips in both directions, and XOR preserves the other bits.
example : execInt launch 0 {} ⟨.xor, .int .b 32, false, [some 0], [.imm 0, .imm 1]⟩ =
    .ok (next (setReg {} 0 (.bits 32 1))) := rfl
example : execInt launch 0 {} ⟨.xor, .int .b 32, false, [some 0], [.imm 1, .imm 1]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0))) := rfl
example : execInt launch 0 {} ⟨.xor, .int .b 32, false, [some 0], [.imm 0x81234567, .imm 1]⟩ =
    .ok (next (setReg {} 0 (.bits 32 0x81234566))) := rfl

-- Widening is unsigned: the source high bit is not a sign bit.
example : execLocal launch 0 {}
    (.cvt { dst := .int .u 64, src := .int .u 32, d := 2, srcs := [.imm 0xFFFFFFFF] }) =
    .ok (next (setReg {} 2 (.bits 64 0xFFFFFFFF))) := rfl
example : execLocal launch 0 {}
    (.cvt { dst := .int .u 32, src := .int .u 64, d := 0, srcs := [.imm 0xFEDCBA9876543210] }) =
    .ok (next (setReg {} 0 (.bits 32 0x76543210))) := rfl
example : execLocal launch 0 {}
    (.cvt { dst := .int .u 16, src := .int .u 32, d := 3, srcs := [.imm 0x12345678] }) =
    .ok (next (setReg {} 3 (.bits 16 0x5678))) := rfl

example (t : TState) :
    execMove launch 0 (setReg t 4 (.pred true))
      (.int ⟨.selp, .int .b 32, false, [some 0], [.imm 7, .imm 9, .reg 4]⟩) =
    .ok (next (setReg (setReg t 4 (.pred true)) 0 (.bits 32 7))) := by
  simp [execMove, readReg, readValue, readBits, setReg, Value.bytes]
  rfl
example (t : TState) :
    execMove launch 0 (setReg t 4 (.pred false))
      (.int ⟨.selp, .int .b 32, false, [some 0], [.imm 7, .imm 9, .reg 4]⟩) =
    .ok (next (setReg (setReg t 4 (.pred false)) 0 (.bits 32 9))) := by
  simp [execMove, readReg, readValue, readBits, setReg, Value.bytes]
  rfl

-- General register-frame theorem covers every successful new instruction too.
example {L : Launch} {g : Nat} {t t' : TState} {w : Nat} {d p : Nat} {a b : Opnd}
    (h : execLocal L g t (.int ⟨.selp, .int .b w, false, [some d], [a, b, .reg p]⟩) = .ok t') :
    Proof.LocalFrame (.int ⟨.selp, .int .b w, false, [some d], [a, b, .reg p]⟩) t t' :=
  Proof.execLocal_frame h

end
end PTX.Tests.ScalarOps
