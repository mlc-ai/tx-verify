-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! The integer instructions `clmad` (§9.7.1.5), `dp4a` (§9.7.1.24), `dp2a` (§9.7.1.25) and the
extended-precision instructions `add.cc`, `addc`, `sub.cc`, `subc`, `mad.cc` and `madc` (§9.7.2)
of THREAD-INT, with the carry flag `CC.CF` of THREAD-STATE. Every expected value is derived from
the Semantics text of the manual. The examples also check decoding and the rule of each form. -/
namespace PTX.Tests.IntExtended
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩], labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5
private def r (n : String) : Syntax.Operand := .register n

private def u32 : DType := .int .u 32
private def s32 : DType := .int .s 32
private def b32 : DType := .int .b 32
private def u64 : DType := .int .u 64

/-- Run a one-destination instruction (register 0) with the given sources on the state `t`. -/
private def exAt (t : TState) (op : IntOp) (ty : DType) (srcs : List Opnd) : Exec TState :=
  execInt launch 0 t ⟨op, ty, false, [some 0], srcs⟩

/-- The same on the empty state. -/
private def ex (op : IntOp) (ty : DType) (srcs : List Opnd) : Exec TState := exAt {} op ty srcs

/-- The outcome in which register 0 of `t` receives the `w`-bit value `v`. -/
private def outAt (t : TState) (w v : Nat) : Exec TState :=
  .ok (next (setReg t 0 (.bits w (.ofNat 64 v))))

/-- The outcome in which register 0 receives `v` and the carry flag becomes `c`. -/
private def outCf (t : TState) (w v : Nat) (c : Bool) : Exec TState :=
  .ok (next { setReg t 0 (.bits w (.ofNat 64 v)) with cf := some c })

private def withCf (c : Bool) : TState := { cf := some c }

/-! ## dp4a and dp2a (§9.7.1.24, §9.7.1.25) -/

-- Unsigned bytes 1, 2, 3, 4 times 1, plus `c`.
example : ex (.dp4a .u .u) b32 [.imm 0x01020304, .imm 0x01010101, .imm 10] = outAt {} 32 20 :=
  rfl
-- Signed bytes: -1 * 127.
example : ex (.dp4a .s .s) b32 [.imm 0xFF000000, .imm 0x7F000000, .imm 0] =
    outAt {} 32 0xFFFFFF81 := rfl
-- `.atype` unsigned (255), `.btype` signed (-1): `c` has type `.s32`.
example : ex (.dp4a .u .s) b32 [.imm 0xFF000000, .imm 0xFF000000, .imm 0] =
    outAt {} 32 0xFFFFFF01 := rfl
-- The largest unsigned products wrap with `c = 0xFFFFFFFF`: 4 * 255 * 255 - 1.
example : ex (.dp4a .u .u) b32 [.imm 0xFFFFFFFF, .imm 0xFFFFFFFF, .imm 0xFFFFFFFF] =
    outAt {} 32 260099 := rfl
-- `dp2a.lo` uses bytes 0 and 1 of `b`, `dp2a.hi` bytes 2 and 3.
example : ex (.dp2a false .u .u) b32 [.imm 0x00020003, .imm 0x04030201, .imm 0] = outAt {} 32 7 :=
  rfl
example : ex (.dp2a true .u .u) b32 [.imm 0x00020003, .imm 0x04030201, .imm 0] = outAt {} 32 17 :=
  rfl
-- Signed half-words 1 and -1 with signed bytes 2 and -1.
example : ex (.dp2a false .s .s) b32 [.imm 0xFFFF0001, .imm 0x0000FF02, .imm 0] = outAt {} 32 3 :=
  rfl

/-! ## clmad (§9.7.1.5) -/

-- `0b11 ⊗ 0b11 = 0b101`, then `^ c`.
example : ex (.clmad false) u64 [.imm 3, .imm 3, .imm 0] = outAt {} 64 5 := rfl
example : ex (.clmad false) u64 [.imm 3, .imm 3, .imm 1] = outAt {} 64 4 := rfl
-- `2^63 ⊗ 2 = 2^64`: the high half is 1 and the low half 0.
example : ex (.clmad true) u64 [.imm (2 ^ 63), .imm 2, .imm 0] = outAt {} 64 1 := rfl
example : ex (.clmad false) u64 [.imm (2 ^ 63), .imm 2, .imm 0] = outAt {} 64 0 := rfl

/-! ## The carry chain (§9.7.2) -/

-- `add.cc` writes the carry-out; it is the same for signed and unsigned types.
example : ex (.addCarry false true) u32 [.imm 0xFFFFFFFF, .imm 1] = outCf {} 32 0 true := rfl
example : ex (.addCarry false true) s32 [.imm 0xFFFFFFFF, .imm 1] = outCf {} 32 0 true := rfl
example : ex (.addCarry false true) u32 [.imm 1, .imm 2] = outCf {} 32 3 false := rfl
example : ex (.addCarry false true) u64 [.imm (2 ^ 64 - 1), .imm 1] = outCf {} 64 0 true := rfl
-- `addc` adds `CC.CF` and leaves it without `.cc`; `addc.cc` writes the new carry.
example : exAt (withCf true) (.addCarry true false) u32 [.imm 1, .imm 2] =
    outAt (withCf true) 32 4 := rfl
example : exAt (withCf true) (.addCarry true true) u32 [.imm 0xFFFFFFFF, .imm 0] =
    outCf (withCf true) 32 0 true := rfl
-- `sub.cc` writes the borrow-out; `subc` subtracts `b + CC.CF`.
example : ex (.subCarry false true) u32 [.imm 0, .imm 1] = outCf {} 32 0xFFFFFFFF true := rfl
example : exAt (withCf true) (.subCarry true true) u32 [.imm 5, .imm 3] =
    outCf (withCf true) 32 1 false := rfl
example : exAt (withCf true) (.subCarry true true) u32 [.imm 4, .imm 4] =
    outCf (withCf true) 32 0xFFFFFFFF true := rfl
-- `mad.lo.cc`: `(0xFFFFFFFF * 2)<31..0> + 3 = 0x1_00000001`.
example : ex (.madCarry false false true) u32 [.imm 0xFFFFFFFF, .imm 2, .imm 3] =
    outCf {} 32 1 true := rfl
-- `madc.hi`: `(0xFFFFFFFF * 2)<63..32> + 0 + CC.CF`.
example : exAt (withCf true) (.madCarry true true false) u32 [.imm 0xFFFFFFFF, .imm 2, .imm 0] =
    outAt (withCf true) 32 2 := rfl
-- `mad.hi.cc.s32` of `-1 * 1`: the high half is all ones, and adding 1 carries out.
example : ex (.madCarry true false true) s32 [.imm (-1), .imm 1, .imm 1] = outCf {} 32 0 true :=
  rfl

-- The manual's 64-bit addition from two 32-bit halves: `add.cc` then `addc`.
example :
    (ex (.addCarry false true) u32 [.imm 0xFFFFFFFF, .imm 1] >>= fun t =>
      execInt launch 0 t ⟨.addCarry true false, u32, false, [some 1], [.imm 0, .imm 0]⟩) =
    .ok (next (setReg (next { setReg {} 0 (.bits 32 (.ofNat 64 0)) with cf := some true }) 1
      (.bits 32 (.ofNat 64 1)))) := rfl

-- Rejected: reading `CC.CF` before an instruction has written it has no rule.
example : ex (.addCarry true false) u32 [.imm 1, .imm 2] = .error .noRule := rfl
example : ex (.subCarry true true) u32 [.imm 1, .imm 2] = .error .noRule := rfl
example : ex (.madCarry false true false) u32 [.imm 1, .imm 2, .imm 3] = .error .noRule := rfl

/-! ## Decoding and rules -/

example : Decode.op env "add.cc.u32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.int ⟨.addCarry false true, u32, false, [some 0], [.reg 1, .reg 2]⟩) := rfl
example : Decode.op env "addc.u32" [r "%r3", .literal "0", .literal "0"] =
    .ok (.int ⟨.addCarry true false, u32, false, [some 3], [.imm 0, .imm 0]⟩) := rfl
example : Decode.op env "subc.cc.s64" [r "%rd0", r "%rd1", r "%rd0"] =
    .ok (.int ⟨.subCarry true true, .int .s 64, false, [some 4], [.reg 5, .reg 4]⟩) := rfl
example : Decode.op env "madc.hi.cc.u32" [r "%r2", r "%r0", r "%r1", r "%r2"] =
    .ok (.int ⟨.madCarry true true true, u32, false, [some 2], [.reg 0, .reg 1, .reg 2]⟩) := rfl
example : Decode.op env "mad.lo.cc.u32" [r "%r2", r "%r0", r "%r1", r "%r2"] =
    .ok (.int ⟨.madCarry false false true, u32, false, [some 2], [.reg 0, .reg 1, .reg 2]⟩) :=
  rfl
example : Decode.op env "dp4a.u32.s32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.int ⟨.dp4a .u .s, b32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) := rfl
example : Decode.op env "dp2a.hi.s32.u32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.int ⟨.dp2a true .s .u, b32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) := rfl
example : Decode.op env "clmad.hi.u64" [r "%rd0", r "%rd1", r "%rd0", r "%rd1"] =
    .ok (.int ⟨.clmad true, u64, false, [some 4], [.reg 5, .reg 4, .reg 5]⟩) := rfl

example : (IntInstr.rule ⟨.addCarry true true, u32, false, [some 0], [.reg 1, .reg 2]⟩) =
    some .threadInt := rfl
example : (IntInstr.rule ⟨.dp4a .u .s, b32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) =
    some .threadInt := rfl
example : (IntInstr.rule ⟨.clmad false, u64, false, [some 4], [.reg 5, .reg 4, .reg 5]⟩) =
    some .threadInt := rfl
-- Rejected: `.sat` on a carry instruction has no rule; `mad.cc` without `.hi` or `.lo`, and
-- `.u16` carry instructions, are not recognized.
example : (IntInstr.rule ⟨.addCarry false true, u32, true, [some 0], [.reg 1, .reg 2]⟩) = none :=
  rfl
example : (Decode.op env "mad.cc.u32" [r "%r2", r "%r0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "addc.u16" [r "%r2", r "%r0", r "%r1"]).isOk = false := rfl

-- `execLocal` dispatches through the rule.
example : execLocal launch 0 {} (.int ⟨.addCarry false true, u32, false, [some 0],
    [.imm 0xFFFFFFFF, .imm 1]⟩) = outCf {} 32 0 true := rfl

end
end PTX.Tests.IntExtended
