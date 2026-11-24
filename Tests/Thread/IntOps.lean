-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Integer, bit, logic and comparison instructions of THREAD-INT: `add`, `sub`, `min`, `max`,
`mad`, `mul24`, `mad24`, `sad`, `div`, `rem`, `abs` (§9.7.1.1–§9.7.1.11, §9.7.1.13, §9.7.1.14),
`popc`, `clz`, `bfind`, `fns`, `brev`, `bfe`, `bfi`, `szext`, `bmsk` (§9.7.1.15–§9.7.1.23),
`cnot`, `lop3`, `shf` (§9.7.9.5–§9.7.9.7), `prmt` (§9.7.10.7), `setp` (§9.7.7.2) and `set`
(§9.7.7.1). Every expected value is derived from the Semantics text of the manual. The examples
also check the rule of the instruction (`IntInstr.rule`), its decoding and the dispatch of
`execLocal`. -/
namespace PTX.Tests.IntOps
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%p".toList, 3, 1⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5, %rs0..%rs1 = 6..7, %p0..%p2 = 8..10
private def r (n : String) : Syntax.Operand := .register n

private def u32 : DType := .int .u 32
private def s32 : DType := .int .s 32
private def b32 : DType := .int .b 32
private def s64 : DType := .int .s 64
private def u64 : DType := .int .u 64
private def b64 : DType := .int .b 64

/-- Run a one-destination instruction (register 0) with the given sources on the empty state. -/
private def ex (op : IntOp) (ty : DType) (srcs : List Opnd) : Exec TState :=
  execInt launch 0 {} ⟨op, ty, false, [some 0], srcs⟩

/-- The same with `.sat`. -/
private def exSat (op : IntOp) (ty : DType) (srcs : List Opnd) : Exec TState :=
  execInt launch 0 {} ⟨op, ty, true, [some 0], srcs⟩

/-- The outcome in which register 0 receives the `w`-bit value `v`. -/
private def out (w : Nat) (v : Nat) : Exec TState :=
  .ok (next (setReg {} 0 (.bits w (.ofNat 64 v))))

/-! ## add and sub with `.sat` and packed lanes (§9.7.1.1, §9.7.1.2) -/

-- `add.sat.s32` clamps to MAXINT and to MININT.
example : exSat .add s32 [.imm 0x7FFFFFFF, .imm 1] = out 32 0x7FFFFFFF := rfl
example : exSat .add s32 [.imm 0x80000000, .imm (-1)] = out 32 0x80000000 := rfl
example : exSat .add s32 [.imm 5, .imm (-7)] = out 32 0xFFFFFFFE := rfl
example : exSat .add u32 [.imm 0xFFFFFFFF, .imm 1] = out 32 0xFFFFFFFF := rfl
-- `sub.sat.s32`.
example : exSat .sub s32 [.imm 0x80000000, .imm 1] = out 32 0x80000000 := rfl
example : exSat .sub s32 [.imm 0x7FFFFFFF, .imm (-1)] = out 32 0x7FFFFFFF := rfl
example : exSat .sub s32 [.imm 3, .imm 5] = out 32 0xFFFFFFFE := rfl
-- `add.u16x2` and `add.s16x2` add per half word and do not carry between the lanes.
example : ex .add (.packed (.int .u 16) 2) [.imm 0x0001FFFF, .imm 0x00010001] = out 32 0x00020000 :=
  rfl
example : ex .add (.packed (.int .s 16) 2) [.imm 0x0001FFFF, .imm 0x00010001] = out 32 0x00020000 :=
  rfl
example : ex .add (.packed (.int .s 16) 2) [.imm 0x00017FFF, .imm 0x00010001] = out 32 0x00028000 :=
  rfl
-- `.sat` clamps each half word to its own range.
example : exSat .add (.packed (.int .s 16) 2) [.imm 0x80007FFF, .imm 0xFFFF0001] =
    out 32 0x80007FFF := rfl
example : exSat .add (.packed (.int .u 8) 4) [.imm 0x00FF00FF, .imm 0x00010001] =
    out 32 0x00FF00FF := rfl
example : ex .add (.packed (.int .u 8) 4) [.imm 0x00FF00FF, .imm 0x00010001] = out 32 0 := rfl
example : ex .sub (.packed (.int .u 8) 4) [.imm 0x00000100, .imm 0x00000001] = out 32 0x000001FF :=
  rfl

/-! ## min and max (§9.7.1.13, §9.7.1.14) -/

example : ex (.min false) (.packed (.int .u 16) 2) [.imm 0x0001FFFF, .imm 0x00020000] =
    out 32 0x00010000 := rfl
example : ex (.max false) (.packed (.int .u 16) 2) [.imm 0x0001FFFF, .imm 0x00020000] =
    out 32 0x0002FFFF := rfl
example : ex (.min false) (.packed (.int .s 16) 2) [.imm 0x0001FFFF, .imm 0x00020000] =
    out 32 0x0001FFFF := rfl
-- `min.relu.s32` clamps a negative result to 0.
example : ex (.min true) s32 [.imm (-5), .imm 3] = out 32 0 := rfl
example : ex (.min true) s32 [.imm 5, .imm 3] = out 32 3 := rfl
-- `max.relu.s16x2`: the lane maxima are 3 and -2; the negative lane becomes 0.
example : ex (.max true) (.packed (.int .s 16) 2) [.imm 0xFFFE0003, .imm 0xFFFD0001] =
    out 32 0x00000003 := rfl
example : ex (.max true) s32 [.imm (-5), .imm (-9)] = out 32 0 := rfl

/-! ## mad, mul24, mad24, sad (§9.7.1.4, §9.7.1.6–§9.7.1.8) -/

-- `mad.hi.u32`: the product is 0xFFFFFFFE00000001, its upper half 0xFFFFFFFE, plus 5 wraps to 3.
example : ex (.mad .hi) u32 [.imm 0xFFFFFFFF, .imm 0xFFFFFFFF, .imm 5] = out 32 3 := rfl
-- `mad.hi.sat.s32` clamps the sum of the upper half and `c`.
example : exSat (.mad .hi) s32 [.imm 0x7FFFFFFF, .imm 0x7FFFFFFF, .imm 0x7FFFFFFF] =
    out 32 0x7FFFFFFF := rfl
example : exSat (.mad .hi) s32 [.imm 0x80000000, .imm 0x7FFFFFFF, .imm 0x80000000] =
    out 32 0x80000000 := rfl
example : exSat (.mad .hi) s32 [.imm 0x7FFFFFFF, .imm 0x7FFFFFFF, .imm 1] = out 32 0x40000000 :=
  rfl
-- `mad.wide`: the product of two 16-bit values plus a 32-bit `c`, and of two 32-bit values.
example : ex (.mad .wide) (.int .s 16) [.imm 0xFFFF, .imm 3, .imm 0] = out 32 0xFFFFFFFD := rfl
example : ex (.mad .wide) (.int .s 16) [.imm 0xFFFF, .imm 3, .imm 16] = out 32 13 := rfl
example : ex (.mad .wide) (.int .u 16) [.imm 0xFFFF, .imm 0xFFFF, .imm 1] = out 32 0xFFFE0002 := rfl
example : ex (.mad .wide) u32 [.imm 0xFFFFFFFF, .imm 0xFFFFFFFF, .imm 1] =
    out 64 0xFFFFFFFE00000002 := rfl
-- `mul24`: the 48-bit product 0xFFFFFE000001 of two 24-bit values.
example : ex (.mul24 false) u32 [.imm 0xFFFFFF, .imm 0xFFFFFF] = out 32 0xFE000001 := rfl
example : ex (.mul24 true) u32 [.imm 0xFFFFFF, .imm 0xFFFFFF] = out 32 0xFFFFFE00 := rfl
-- A signed 24-bit operand is sign-extended: -1 * 2 = -2, whose bits 47..16 are all ones.
example : ex (.mul24 false) s32 [.imm (-1), .imm 2] = out 32 0xFFFFFFFE := rfl
example : ex (.mul24 true) s32 [.imm (-1), .imm 2] = out 32 0xFFFFFFFF := rfl
example : ex (.mul24 true) s32 [.imm 0x7FFFFF, .imm 0x7FFFFF] = out 32 0x3FFFFF00 := rfl
-- An operand that is not a 24-bit value has no rule.
example : ex (.mul24 false) u32 [.imm 0x1000000, .imm 1] = .error .noRule := rfl
example : ex (.mul24 false) s32 [.imm 0x800000, .imm 1] = .error .noRule := rfl
example : ex (.mul24 true) s32 [.imm 0x1000000, .imm 1] = .error .noRule := rfl
-- `mad24`: the low or high half of the product plus `c`; `.sat` on the high half of `.s32`.
example : ex (.mad24 false) u32 [.imm 0xFFFFFF, .imm 0xFFFFFF, .imm 2] = out 32 0xFE000003 := rfl
example : ex (.mad24 true) u32 [.imm 0xFFFFFF, .imm 0xFFFFFF, .imm 2] = out 32 0xFFFFFE02 := rfl
example : exSat (.mad24 true) s32 [.imm 0x7FFFFF, .imm 0x7FFFFF, .imm 0x7FFFFFFF] =
    out 32 0x7FFFFFFF := rfl
example : exSat (.mad24 true) s32 [.imm 0xFF800000, .imm 0x7FFFFF, .imm 0x80000000] =
    out 32 0x80000000 := rfl
example : exSat (.mad24 true) s32 [.imm 0x7FFFFF, .imm 0x7FFFFF, .imm 1] = out 32 0x3FFFFF01 :=
  rfl
-- `sad`: c + |a - b|, in the signed or unsigned order.
example : ex .sad s32 [.imm (-5), .imm 3, .imm 10] = out 32 18 := rfl
example : ex .sad s32 [.imm 3, .imm (-5), .imm 10] = out 32 18 := rfl
example : ex .sad u32 [.imm 3, .imm 0xFFFFFFF0, .imm 1] = out 32 0xFFFFFFEE := rfl
example : ex .sad u32 [.imm 0xFFFFFFF0, .imm 3, .imm 1] = out 32 0xFFFFFFEE := rfl

/-! ## div, rem, abs (§9.7.1.9–§9.7.1.11) -/

example : ex .div u32 [.imm 7, .imm 2] = out 32 3 := rfl
example : ex .div u32 [.imm 0xFFFFFFFF, .imm 2] = out 32 0x7FFFFFFF := rfl
example : ex .div s32 [.imm 7, .imm 2] = out 32 3 := rfl
-- An exact negative quotient is -8 / 2 = -4; an inexact one rounds in a machine-dependent way.
example : ex .div s32 [.imm (-8), .imm 2] = out 32 0xFFFFFFFC := rfl
example : ex .div s32 [.imm 8, .imm (-2)] = out 32 0xFFFFFFFC := rfl
example : ex .div s32 [.imm (-7), .imm 2] = .error .noRule := rfl
example : ex .div s32 [.imm 7, .imm (-2)] = .error .noRule := rfl
-- Division by zero is unspecified, and MININT / -1 does not fit the type.
example : ex .div u32 [.imm 7, .imm 0] = .error .noRule := rfl
example : ex .div s32 [.imm 7, .imm 0] = .error .noRule := rfl
example : ex .div s32 [.imm 0x80000000, .imm (-1)] = .error .noRule := rfl
example : ex .rem u32 [.imm 7, .imm 3] = out 32 1 := rfl
example : ex .rem u32 [.imm 0xFFFFFFFF, .imm 0x10] = out 32 15 := rfl
example : ex .rem s32 [.imm 7, .imm 3] = out 32 1 := rfl
-- The remainder of negative operands depends on the machine.
example : ex .rem s32 [.imm (-7), .imm 3] = .error .noRule := rfl
example : ex .rem s32 [.imm 7, .imm (-3)] = .error .noRule := rfl
example : ex .rem u32 [.imm 7, .imm 0] = .error .noRule := rfl
example : ex .rem s32 [.imm 7, .imm 0] = .error .noRule := rfl
example : ex .abs s32 [.imm (-5)] = out 32 5 := rfl
example : ex .abs s32 [.imm 5] = out 32 5 := rfl
-- |MININT| is 2^31, whose low 32 bits are MININT.
example : ex .abs s32 [.imm 0x80000000] = out 32 0x80000000 := rfl

/-! ## popc, clz, bfind, fns, brev (§9.7.1.15–§9.7.1.19) -/

example : ex .popc b32 [.imm 0xF0F0F0F0] = out 32 16 := rfl
example : ex .popc b32 [.imm 0] = out 32 0 := rfl
example : ex .popc b64 [.imm 0xFFFFFFFFFFFFFFFF] = out 32 64 := rfl
example : ex .clz b32 [.imm 0] = out 32 32 := rfl
example : ex .clz b32 [.imm 1] = out 32 31 := rfl
example : ex .clz b32 [.imm 0x80000000] = out 32 0 := rfl
example : ex .clz b64 [.imm 0] = out 32 64 := rfl
example : ex .clz b64 [.imm 1] = out 32 63 := rfl
example : ex .clz b64 [.imm 0x100000000] = out 32 31 := rfl
example : ex (.bfind false) u32 [.imm 0] = out 32 0xFFFFFFFF := rfl
example : ex (.bfind false) u32 [.imm 0x00010000] = out 32 16 := rfl
example : ex (.bfind false) u32 [.imm 0x80000000] = out 32 31 := rfl
example : ex (.bfind false) u64 [.imm 0x100000000] = out 32 32 := rfl
-- A negative signed input is searched for its most significant 0 bit.
example : ex (.bfind false) s32 [.imm (-1)] = out 32 0xFFFFFFFF := rfl
example : ex (.bfind false) s32 [.imm 0x80000000] = out 32 30 := rfl
example : ex (.bfind false) s32 [.imm 0x7FFFFFFF] = out 32 30 := rfl
example : ex (.bfind false) s32 [.imm 0] = out 32 0xFFFFFFFF := rfl
-- `.shiftamt` returns the shift that moves the found bit to the msb.
example : ex (.bfind true) u32 [.imm 0x00010000] = out 32 15 := rfl
example : ex (.bfind true) u32 [.imm 0] = out 32 0xFFFFFFFF := rfl
example : ex (.bfind true) s32 [.imm 0x80000000] = out 32 1 := rfl
-- The four examples of the manual for `fns.b32` with the mask 0xaaaaaaaa.
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm 1] = out 32 3 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm (-1)] = out 32 3 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 2, .imm 1] = out 32 3 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 2, .imm (-1)] = out 32 1 := rfl
-- Offset 0 tests the bit `base`; a missing bit gives 0xffffffff; base above 31 is undefined.
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm 0] = out 32 3 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 2, .imm 0] = out 32 0xFFFFFFFF := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm 15] = out 32 31 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm 16] = out 32 0xFFFFFFFF := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm (-2)] = out 32 1 := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 3, .imm (-3)] = out 32 0xFFFFFFFF := rfl
example : ex .fns b32 [.imm 0xAAAAAAAA, .imm 32, .imm 1] = .error .badValue := rfl
example : ex .brev b32 [.imm 1] = out 32 0x80000000 := rfl
example : ex .brev b32 [.imm 0x12345678] = out 32 0x1E6A2C48 := rfl
example : ex .brev b64 [.imm 1] = out 64 0x8000000000000000 := rfl

/-! ## bfe, bfi, szext, bmsk (§9.7.1.20–§9.7.1.23) -/

example : ex .bfe u32 [.imm 0xABCDEF12, .imm 8, .imm 8] = out 32 0xEF := rfl
example : ex .bfe u32 [.imm 0xABCDEF12, .imm 8, .imm 0] = out 32 0 := rfl
example : ex .bfe s32 [.imm 0xABCDEF12, .imm 8, .imm 0] = out 32 0 := rfl
-- The field 0xf is negative as a 4-bit signed field, so the result is padded with ones.
example : ex .bfe s32 [.imm 0xF0, .imm 4, .imm 4] = out 32 0xFFFFFFFF := rfl
example : ex .bfe u32 [.imm 0xF0, .imm 4, .imm 4] = out 32 0xF := rfl
-- A field that extends past the msb takes the sign from the msb of `a`.
example : ex .bfe s32 [.imm 0x80000000, .imm 28, .imm 8] = out 32 0xFFFFFFF8 := rfl
example : ex .bfe s32 [.imm 0x7FFFFFFF, .imm 28, .imm 8] = out 32 0x7 := rfl
-- A start beyond the msb fills the result with the replicated sign bit.
example : ex .bfe s32 [.imm 0x80000000, .imm 40, .imm 4] = out 32 0xFFFFFFFF := rfl
example : ex .bfe s32 [.imm 0x7FFFFFFF, .imm 40, .imm 4] = out 32 0 := rfl
example : ex .bfe u32 [.imm 0xFFFFFFFF, .imm 40, .imm 4] = out 32 0 := rfl
-- `pos` and `len` are taken modulo 256.
example : ex .bfe u32 [.imm 0xABCDEF12, .imm 0x108, .imm 0x108] = out 32 0xEF := rfl
example : ex .bfe u64 [.imm 0xFEDCBA9876543210, .imm 32, .imm 16] = out 64 0xBA98 := rfl
example : ex .bfe s64 [.imm 0x8000000000000000, .imm 60, .imm 8] =
    out 64 0xFFFFFFFFFFFFFFF8 := rfl
example : ex .bfi b32 [.imm 0xA, .imm 0xFFFFFFFF, .imm 4, .imm 4] = out 32 0xFFFFFFAF := rfl
example : ex .bfi b32 [.imm 0xA, .imm 0, .imm 4, .imm 4] = out 32 0xA0 := rfl
-- A length of 0, or a start beyond the msb, gives `b`.
example : ex .bfi b32 [.imm 0xA, .imm 0x12345678, .imm 4, .imm 0] = out 32 0x12345678 := rfl
example : ex .bfi b32 [.imm 0xA, .imm 0x12345678, .imm 32, .imm 4] = out 32 0x12345678 := rfl
example : ex .bfi b32 [.imm 0xA, .imm 0x12345678, .imm 40, .imm 4] = out 32 0x12345678 := rfl
-- A field that extends past the msb keeps only the bits that fit.
example : ex .bfi b32 [.imm 0xFF, .imm 0, .imm 28, .imm 8] = out 32 0xF0000000 := rfl
example : ex .bfi b64 [.imm 0xFF, .imm 0, .imm 60, .imm 8] = out 64 0xF000000000000000 := rfl
example : ex .bfi b64 [.imm 0xFF, .imm 0, .imm 32, .imm 8] = out 64 0xFF00000000 := rfl
-- `szext`: sign- or zero-extend the low N bits.
example : ex (.szext true) s32 [.imm 0xFF, .imm 8] = out 32 0xFFFFFFFF := rfl
example : ex (.szext true) s32 [.imm 0x7F, .imm 8] = out 32 0x7F := rfl
example : ex (.szext true) s32 [.imm 0x1FF, .imm 8] = out 32 0xFFFFFFFF := rfl
example : ex (.szext true) u32 [.imm 0x1FF, .imm 8] = out 32 0xFF := rfl
example : ex (.szext false) u32 [.imm 0xFFFFFFFF, .imm 0] = out 32 0 := rfl
example : ex (.szext true) s32 [.imm 0xFFFFFFFF, .imm 0] = out 32 0 := rfl
-- N of 32 or more: `.clamp` returns `a`, `.wrap` uses N modulo 32.
example : ex (.szext true) s32 [.imm 0x12345678, .imm 32] = out 32 0x12345678 := rfl
example : ex (.szext true) s32 [.imm 0x80, .imm 40] = out 32 0x80 := rfl
example : ex (.szext false) s32 [.imm 0x80, .imm 40] = out 32 0xFFFFFF80 := rfl
example : ex (.szext false) s32 [.imm 0x12345678, .imm 32] = out 32 0 := rfl
-- `bmsk`: the manual's example has `a` = 1 and `b` = 2, mask 0x6.
example : ex (.bmsk false) b32 [.imm 1, .imm 2] = out 32 0x6 := rfl
example : ex (.bmsk true) b32 [.imm 1, .imm 2] = out 32 0x6 := rfl
example : ex (.bmsk true) b32 [.imm 32, .imm 2] = out 32 0 := rfl
example : ex (.bmsk true) b32 [.imm 33, .imm 2] = out 32 0 := rfl
example : ex (.bmsk false) b32 [.imm 33, .imm 2] = out 32 0x6 := rfl
-- Width 32 in `.clamp` mode reaches the msb; width 32 in `.wrap` mode is 0.
example : ex (.bmsk true) b32 [.imm 0, .imm 32] = out 32 0xFFFFFFFF := rfl
example : ex (.bmsk true) b32 [.imm 4, .imm 32] = out 32 0xFFFFFFF0 := rfl
example : ex (.bmsk false) b32 [.imm 0, .imm 32] = out 32 0 := rfl
example : ex (.bmsk true) b32 [.imm 3, .imm 0] = out 32 0 := rfl
-- A mask that runs past bit 31 is cut at the msb.
example : ex (.bmsk false) b32 [.imm 30, .imm 4] = out 32 0xC0000000 := rfl
example : ex (.bmsk false) b32 [.imm 31, .imm 1] = out 32 0x80000000 := rfl

/-! ## cnot, lop3, shf, prmt (§9.7.9.5–§9.7.9.7, §9.7.10.7) -/

example : ex .cnot b32 [.imm 0] = out 32 1 := rfl
example : ex .cnot b32 [.imm 5] = out 32 0 := rfl
example : ex .cnot b32 [.imm 0x80000000] = out 32 0 := rfl
-- `immLut` 0x80 is a & b & c, and 0x1A is (a & b | c) ^ a.
example : ex (.lop3 0x80 none) b32 [.imm 0xFF00FF00, .imm 0xF0F0F0F0, .imm 0xFFFF0000] =
    out 32 0xF0000000 := rfl
example : ex (.lop3 0x1A none) b32 [.imm 0xFF00FF00, .imm 0x0FF00FF0, .imm 0x00FFFF00] =
    out 32 0xF0FF0000 := rfl
example : ex (.lop3 0x1A none) b32 [.imm 0xF0, .imm 0xCC, .imm 0xAA] = out 32 0x1A := rfl
example : ex (.lop3 0xFE none) b32 [.imm 0xF0, .imm 0xCC, .imm 0xAA] = out 32 0xFE := rfl
example : ex (.lop3 0x40 none) b32 [.imm 0xF0, .imm 0xCC, .imm 0xAA] = out 32 0x40 := rfl
example : ex (.lop3 0 none) b32 [.imm 0xF0, .imm 0xCC, .imm 0xAA] = out 32 0 := rfl
example : ex (.lop3 0xFF none) b32 [.imm 0, .imm 0, .imm 0] = out 32 0xFFFFFFFF := rfl

-- The `d|p` form: `p = (d != 0) BoolOp q`.
private def pq (q : Bool) : TState := setReg {} 10 (.pred q)
example : execInt launch 0 (pq false) ⟨.lop3 0x80 (some .or), b32, false, [some 0, some 9],
      [.imm 0xFF00FF00, .imm 0xF0F0F0F0, .imm 0xFFFF0000, .reg 10]⟩ =
    .ok (next (setReg (setReg (pq false) 0 (.bits 32 0xF0000000)) 9 (.pred true))) := rfl
example : execInt launch 0 (pq false) ⟨.lop3 0x80 (some .and), b32, false, [some 0, some 9],
      [.imm 0xFF00FF00, .imm 0xF0F0F0F0, .imm 0xFFFF0000, .reg 10]⟩ =
    .ok (next (setReg (setReg (pq false) 0 (.bits 32 0xF0000000)) 9 (.pred false))) := rfl
example : execInt launch 0 (pq true) ⟨.lop3 0x80 (some .or), b32, false, [some 0, some 9],
      [.imm 0, .imm 0, .imm 0, .reg 10]⟩ =
    .ok (next (setReg (setReg (pq true) 0 (.bits 32 0)) 9 (.pred true))) := rfl
example : execInt launch 0 (pq false) ⟨.lop3 0x80 (some .or), b32, false, [some 0, some 9],
      [.imm 0, .imm 0, .imm 0, .reg 10]⟩ =
    .ok (next (setReg (setReg (pq false) 0 (.bits 32 0)) 9 (.pred false))) := rfl
-- The sink in place of `d` leaves every register but `p` alone.
example : execInt launch 0 (pq true) ⟨.lop3 0x80 (some .and), b32, false, [none, some 9],
      [.imm 0xFF00FF00, .imm 0xF0F0F0F0, .imm 0xFFFF0000, .reg 10]⟩ =
    .ok (next (setReg (pq true) 9 (.pred true))) := rfl
example : execInt launch 0 (pq false) ⟨.lop3 0x80 (some .and), b32, false, [none, some 9],
      [.imm 0xFF00FF00, .imm 0xF0F0F0F0, .imm 0xFFFF0000, .reg 10]⟩ =
    .ok (next (setReg (pq false) 9 (.pred false))) := rfl
example : execInt launch 0 (pq true) ⟨.lop3 0x80 (some .and), b32, false, [none, some 9],
      [.imm 0, .imm 0, .imm 0, .reg 10]⟩ =
    .ok (next (setReg (pq true) 9 (.pred false))) := rfl

-- `shf` on the 64-bit value b:a with a = 0x89abcdef and b = 0x01234567.
private def shf (left clamp : Bool) (n : Int) : Exec TState :=
  ex (.shf left clamp) b32 [.imm 0x89ABCDEF, .imm 0x01234567, .imm n]
example : shf true false 0 = out 32 0x01234567 := rfl
example : shf true false 8 = out 32 0x23456789 := rfl
example : shf true false 32 = out 32 0x01234567 := rfl
example : shf true false 40 = out 32 0x23456789 := rfl
example : shf true true 0 = out 32 0x01234567 := rfl
example : shf true true 8 = out 32 0x23456789 := rfl
example : shf true true 32 = out 32 0x89ABCDEF := rfl
example : shf true true 40 = out 32 0x89ABCDEF := rfl
example : shf false true 0 = out 32 0x89ABCDEF := rfl
example : shf false true 8 = out 32 0x6789ABCD := rfl
example : shf false true 32 = out 32 0x01234567 := rfl
example : shf false true 40 = out 32 0x01234567 := rfl
example : shf false false 0 = out 32 0x89ABCDEF := rfl
example : shf false false 8 = out 32 0x6789ABCD := rfl
example : shf false false 32 = out 32 0x89ABCDEF := rfl
example : shf false false 40 = out 32 0x6789ABCD := rfl
-- A rotate has `a` = `b`.
example : ex (.shf true false) b32 [.imm 0x80000001, .imm 0x80000001, .imm 1] = out 32 3 := rfl

-- `prmt` with the bytes of a = 0x33221100 and b = 0x77665544 numbered 0 to 7 as 00 to 77.
private def prmt (m : Option PrmtMode) (c : Int) : Exec TState :=
  ex (.prmt m) b32 [.imm 0x33221100, .imm 0x77665544, .imm c]
example : prmt none 0x3210 = out 32 0x33221100 := rfl
example : prmt none 0x7654 = out 32 0x77665544 := rfl
example : prmt none 0x4567 = out 32 0x44556677 := rfl
-- Generic mode with the sign replication of the selector msb, a = 0x8000ff7f.
example : ex (.prmt none) b32 [.imm 0x8000FF7F, .imm 0, .imm 0x3AB9] = out 32 0x8000FFFF := rfl
example : ex (.prmt none) b32 [.imm 0x8000FF7F, .imm 0, .imm 0x8] = out 32 0x7F7F7F00 := rfl
example : ex (.prmt none) b32 [.imm 0x8000FF7F, .imm 0, .imm 0xBBBB] = out 32 0xFFFFFFFF := rfl
example : ex (.prmt none) b32 [.imm 0x8000FF7F, .imm 0, .imm 0xAAAA] = out 32 0 := rfl
-- The specialised modes use the two lowest bits of `c` only.
example : prmt (some .f4e) 1 = out 32 0x44332211 := rfl
example : prmt (some .f4e) 0x15 = out 32 0x44332211 := rfl
example : prmt (some .f4e) 0 = out 32 0x33221100 := rfl
example : prmt (some .f4e) 3 = out 32 0x66554433 := rfl
example : prmt (some .b4e) 0 = out 32 0x55667700 := rfl
example : prmt (some .b4e) 3 = out 32 0x00112233 := rfl
example : prmt (some .rc8) 2 = out 32 0x22222222 := rfl
example : prmt (some .ecl) 2 = out 32 0x33222222 := rfl
example : prmt (some .ecl) 1 = out 32 0x33221111 := rfl
example : prmt (some .ecr) 1 = out 32 0x11111100 := rfl
example : prmt (some .ecr) 2 = out 32 0x22221100 := rfl
example : prmt (some .rc16) 0 = out 32 0x11001100 := rfl
example : prmt (some .rc16) 1 = out 32 0x33223322 := rfl

/-! ## setp and set (§9.7.7.2, §9.7.7.1) -/

private def pred (b : Bool) : Exec TState := .ok (next (setReg {} 8 (.pred b)))
private def setp (c : Cmp) (ty : DType) (a b : Int) : Exec TState :=
  execInt launch 0 {} ⟨.setp c none, ty, false, [some 8], [.imm a, .imm b]⟩
-- The unsigned operators order 0xffffffff above 1.
example : setp .lo u32 1 2 = pred true := rfl
example : setp .lo u32 0xFFFFFFFF 1 = pred false := rfl
example : setp .ls u32 2 2 = pred true := rfl
example : setp .ls u32 3 2 = pred false := rfl
example : setp .hi u32 0xFFFFFFFF 1 = pred true := rfl
example : setp .hi u32 2 2 = pred false := rfl
example : setp .hs u32 2 2 = pred true := rfl
example : setp .hs u32 1 2 = pred false := rfl
example : setp .lt s32 (-1) 1 = pred true := rfl
example : setp .lt u32 (-1) 1 = pred false := rfl
example : setp .ge s32 (-1) 1 = pred false := rfl
example : setp .eq b32 0xFFFFFFFF 0xFFFFFFFF = pred true := rfl
example : setp .ne b64 0xFFFFFFFF00000000 0 = pred true := rfl
-- `setp.lt.and.s32 p, a, b, c` with one destination.
private def withC (c : Bool) : TState := setReg {} 10 (.pred c)
example : execInt launch 0 (withC true) ⟨.setp .lt (some .and), s32, false, [some 8],
      [.imm (-1), .imm 0, .reg 10]⟩ = .ok (next (setReg (withC true) 8 (.pred true))) := rfl
example : execInt launch 0 (withC false) ⟨.setp .lt (some .and), s32, false, [some 8],
      [.imm (-1), .imm 0, .reg 10]⟩ = .ok (next (setReg (withC false) 8 (.pred false))) := rfl
example : execInt launch 0 (withC true) ⟨.setp .lt (some .and), s32, false, [some 8],
      [.imm 1, .imm 0, .reg 10]⟩ = .ok (next (setReg (withC true) 8 (.pred false))) := rfl
example : execInt launch 0 (withC false) ⟨.setp .lt (some .or), s32, false, [some 8],
      [.imm 1, .imm 0, .reg 10]⟩ = .ok (next (setReg (withC false) 8 (.pred false))) := rfl
example : execInt launch 0 (withC false) ⟨.setp .lt (some .or), s32, false, [some 8],
      [.imm 0, .imm 1, .reg 10]⟩ = .ok (next (setReg (withC false) 8 (.pred true))) := rfl
-- `setp.lt.s32 p|q`: `q` is the complement of `p`.
example : execInt launch 0 {} ⟨.setp .lt none, s32, false, [some 8, some 9], [.imm 1, .imm 2]⟩ =
    .ok (next (setReg (setReg {} 8 (.pred true)) 9 (.pred false))) := rfl
example : execInt launch 0 {} ⟨.setp .lt none, s32, false, [some 8, some 9], [.imm 2, .imm 1]⟩ =
    .ok (next (setReg (setReg {} 8 (.pred false)) 9 (.pred true))) := rfl
-- With the sink in place of one destination only the other one is written.
example : execInt launch 0 {} ⟨.setp .lt none, s32, false, [none, some 9], [.imm 1, .imm 2]⟩ =
    .ok (next (setReg {} 9 (.pred false))) := rfl
example : execInt launch 0 {} ⟨.setp .lt none, s32, false, [some 8, none], [.imm 1, .imm 2]⟩ =
    .ok (next (setReg {} 8 (.pred true))) := rfl
-- `setp.eq.xor.u32 p|q` with a = b: t = 1, p = t xor c, q = !t xor c.
example : execInt launch 0 (withC true) ⟨.setp .eq (some .xor), u32, false, [some 8, some 9],
      [.imm 4, .imm 4, .reg 10]⟩ =
    .ok (next (setReg (setReg (withC true) 8 (.pred false)) 9 (.pred true))) := rfl
example : execInt launch 0 (withC false) ⟨.setp .eq (some .xor), u32, false, [some 8, some 9],
      [.imm 4, .imm 4, .reg 10]⟩ =
    .ok (next (setReg (setReg (withC false) 8 (.pred true)) 9 (.pred false))) := rfl
example : execInt launch 0 (withC true) ⟨.setp .lt (some .and), s32, false, [some 8, some 9],
      [.imm 1, .imm 2, .reg 10]⟩ =
    .ok (next (setReg (setReg (withC true) 8 (.pred true)) 9 (.pred false))) := rfl
example : execInt launch 0 (withC true) ⟨.setp .lt (some .or), s32, false, [some 8, some 9],
      [.imm 2, .imm 1, .reg 10]⟩ =
    .ok (next (setReg (setReg (withC true) 8 (.pred true)) 9 (.pred true))) := rfl

-- `set.lt.u32.s32 d, a, b`: the source type is `.s32`, the destination type `.u32`.
private def setU (c : Cmp) (bop : Option BoolOp) (dst sty : DType) (srcs : List Opnd) :
    Exec TState := execInt launch 0 (withC true) ⟨.set c bop dst, sty, false, [some 0], srcs⟩
private def outC (w v : Nat) : Exec TState :=
  .ok (next (setReg (withC true) 0 (.bits w (.ofNat 64 v))))
example : setU .lt none u32 s32 [.imm (-1), .imm 0] = outC 32 0xFFFFFFFF := rfl
example : setU .lt none u32 s32 [.imm 0, .imm (-1)] = outC 32 0 := rfl
example : setU .lt none s32 u32 [.imm (-1), .imm 0] = outC 32 0 := rfl
-- `set.eq.f32.u32` writes 1.0f for a true comparison.
example : setU .eq none (.float .f32) u32 [.imm 7, .imm 7] = outC 32 0x3F800000 := rfl
example : setU .eq none (.float .f32) u32 [.imm 7, .imm 8] = outC 32 0 := rfl
-- `set.lt.and.s32.u32 d, a, b, c` with a predicate source.
example : setU .lt (some .and) s32 u32 [.imm 1, .imm 2, .reg 10] = outC 32 0xFFFFFFFF := rfl
example : execInt launch 0 (withC false) ⟨.set .lt (some .and) s32, u32, false, [some 0],
      [.imm 1, .imm 2, .reg 10]⟩ = .ok (next (setReg (withC false) 0 (.bits 32 0))) := rfl
example : execInt launch 0 (withC false) ⟨.set .lt (some .or) s32, u32, false, [some 0],
      [.imm 3, .imm 2, .reg 10]⟩ = .ok (next (setReg (withC false) 0 (.bits 32 0))) := rfl
example : setU .lt (some .xor) s32 u32 [.imm 1, .imm 2, .reg 10] = outC 32 0 := rfl
-- Packed `set`: 0xffff or 0x0000 per half word, 0xff or 0x00 per byte.
example : setU .lt none b32 (.packed (.int .s 16) 2) [.imm 0x0001FFFF, .imm 0] =
    outC 32 0x0000FFFF := rfl
example : setU .lt none b32 (.packed (.int .u 16) 2) [.imm 0x0001FFFF, .imm 0x00020000] =
    outC 32 0xFFFF0000 := rfl
example : setU .lt none b32 (.packed (.int .s 16) 2) [.imm 0x0001FFFF, .imm 0x00020000] =
    outC 32 0xFFFFFFFF := rfl
example : setU .hi none b32 (.packed (.int .u 8) 4) [.imm 0x01FF0280, .imm 0x02008080] =
    outC 32 0x00FF0000 := rfl
example : setU .lt none b32 (.packed (.int .s 8) 4) [.imm 0x01FF0280, .imm 0x02008080] =
    outC 32 0xFFFF0000 := rfl

/-! ## Rules of the new forms -/

example : IntInstr.rule ⟨.add, s32, true, [some 0], [.imm 1, .imm 2]⟩ = some .threadInt := rfl
example : IntInstr.rule ⟨.add, .packed (.int .u 16) 2, false, [some 0], [.imm 1, .imm 2]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.mad .hi, s32, true, [some 0], [.imm 1, .imm 2, .imm 3]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.mul24 true, u32, false, [some 0], [.imm 1, .imm 2]⟩ = some .threadInt :=
  rfl
example : IntInstr.rule ⟨.div, s32, false, [some 0], [.imm 8, .imm 2]⟩ = some .threadInt := rfl
example : IntInstr.rule ⟨.fns, b32, false, [some 0], [.imm 1, .imm 2, .imm 3]⟩ = some .threadInt :=
  rfl
example : IntInstr.rule ⟨.prmt (some .rc8), b32, false, [some 0], [.imm 1, .imm 2, .imm 3]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.lop3 0x3F (some .and), b32, false, [none, some 9],
    [.imm 1, .imm 2, .imm 3, .reg 10]⟩ = some .threadInt := rfl
example : IntInstr.rule ⟨.setp .lt none, s32, false, [some 8, some 9], [.imm 1, .imm 2]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.setp .lt none, s32, false, [none, some 9], [.imm 1, .imm 2]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.set .eq none (.float .f32), u32, false, [some 0], [.imm 1, .imm 2]⟩ =
    some .threadInt := rfl
example : IntInstr.rule ⟨.set .lt none b32, .packed (.int .s 16) 2, false, [some 0],
    [.imm 1, .imm 2]⟩ = some .threadInt := rfl
-- No rule: `setp` with the same register twice, `max.relu.u32`, `add.sat.u64` (`dp4a` and
-- `clmad` have rules, tested in `Tests/Thread/IntExtended.lean`).
example : IntInstr.rule ⟨.setp .lt none, s32, false, [some 8, some 8], [.imm 1, .imm 2]⟩ = none :=
  rfl
example : IntInstr.rule ⟨.setp .lt none, s32, false, [none, none], [.imm 1, .imm 2]⟩ = none := rfl
example : IntInstr.rule ⟨.max true, u32, false, [some 0], [.imm 1, .imm 2]⟩ = none := rfl
example : IntInstr.rule ⟨.add, u64, true, [some 0], [.imm 1, .imm 2]⟩ = none := rfl
example : IntInstr.rule ⟨.lop3 0x1FF none, b32, false, [some 0], [.imm 1, .imm 2, .imm 3]⟩ =
    none := rfl
example : IntInstr.rule ⟨.fns, s32, false, [some 0], [.imm 1, .imm 2, .imm 3]⟩ = none := rfl
-- `execLocal` dispatches through the rule: a form without one has `noRule`.
example : execLocal launch 0 {} (.int ⟨.div, s32, false, [some 0], [.imm (-8), .imm 2]⟩) =
    out 32 0xFFFFFFFC := rfl
example : execLocal launch 0 {} (.int ⟨.add, u64, true, [some 0], [.imm 1, .imm 2]⟩) =
    .error .noRule := rfl

/-! ## Decoding -/

example : Decode.op env "lop3.and.b32" [.pair [.sink, r "%p1"], r "%r0", r "%r1", r "%r2",
      .literal "0x3f", r "%p2"] =
    .ok (.int ⟨.lop3 0x3F (some .and), b32, false, [none, some 9],
      [.reg 0, .reg 1, .reg 2, .reg 10]⟩) := rfl
example : Decode.op env "lop3.or.b32" [.pair [r "%r0", r "%p1"], r "%r0", r "%r1", r "%r2",
      .literal "0x3f", r "%p2"] =
    .ok (.int ⟨.lop3 0x3F (some .or), b32, false, [some 0, some 9],
      [.reg 0, .reg 1, .reg 2, .reg 10]⟩) := rfl
example : Decode.op env "lop3.b32" [r "%r3", r "%r0", r "%r1", r "%r2", .literal "0x80"] =
    .ok (.int ⟨.lop3 0x80 none, b32, false, [some 3], [.reg 0, .reg 1, .reg 2]⟩) := rfl
example : Decode.op env "setp.lt.s32" [.pair [r "%p0", r "%p1"], r "%r0", r "%r1"] =
    .ok (.int ⟨.setp .lt none, s32, false, [some 8, some 9], [.reg 0, .reg 1]⟩) := rfl
example : Decode.op env "setp.lt.and.s32" [r "%p0", r "%r0", r "%r1", r "%p2"] =
    .ok (.int ⟨.setp .lt (some .and), s32, false, [some 8], [.reg 0, .reg 1, .reg 10]⟩) := rfl
example : Decode.op env "setp.eq.xor.u32" [.pair [r "%p0", r "%p1"], r "%r0", r "%r1", r "%p2"] =
    .ok (.int ⟨.setp .eq (some .xor), u32, false, [some 8, some 9],
      [.reg 0, .reg 1, .reg 10]⟩) := rfl
example : Decode.op env "set.lt.and.u32.s32" [r "%r0", r "%r0", r "%r1", r "%p2"] =
    .ok (.int ⟨.set .lt (some .and) u32, s32, false, [some 0], [.reg 0, .reg 1, .reg 10]⟩) := rfl
example : Decode.op env "set.lt.s16x2" [r "%r0", r "%r0", r "%r1"] =
    .ok (.int ⟨.set .lt none b32, .packed (.int .s 16) 2, false, [some 0], [.reg 0, .reg 1]⟩) := rfl
example : Decode.op env "fns.b32" [r "%r0", r "%r0", r "%r1", .literal "-1"] =
    .ok (.int ⟨.fns, b32, false, [some 0], [.reg 0, .reg 1, .imm (-1)]⟩) := rfl
example : Decode.op env "add.sat.s32" [r "%r0", r "%r0", r "%r1"] =
    .ok (.int ⟨.add, s32, true, [some 0], [.reg 0, .reg 1]⟩) := rfl
example : Decode.op env "mad.wide.u32" [r "%rd0", r "%r0", r "%r1", r "%rd1"] =
    .ok (.int ⟨.mad .wide, u32, false, [some 4], [.reg 0, .reg 1, .reg 5]⟩) := rfl
example : Decode.op env "prmt.b32.f4e" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.int ⟨.prmt (some .f4e), b32, false, [some 0], [.reg 1, .reg 2, .reg 3]⟩) := rfl
-- Rejected: `immLut` above 255. A `setp` with `p|p` decodes and has no rule.
example : (Decode.op env "lop3.b32" [r "%r3", r "%r0", r "%r1", r "%r2", .literal "0x1ff"]).isOk =
    false := rfl
example : (Decode.op env "lop3.b32" [r "%r3", r "%r0", r "%r1", r "%r2", .literal "-1"]).isOk =
    false := rfl
example : Decode.op env "setp.lt.s32" [.pair [r "%p0", r "%p0"], r "%r0", r "%r1"] =
    .ok (.int ⟨.setp .lt none, s32, false, [some 8, some 8], [.reg 0, .reg 1]⟩) := rfl
-- The sink may replace one destination of `p|q` (§9.7.7.2); both sinks are rejected.
example : Decode.op env "setp.lt.s32" [.pair [r "%p0", .sink], r "%r0", r "%r1"] =
    .ok (.int ⟨.setp .lt none, s32, false, [some 8, none], [.reg 0, .reg 1]⟩) := rfl
example : Decode.op env "setp.lt.and.s32" [.pair [.sink, r "%p1"], r "%r0", r "%r1", r "%p2"] =
    .ok (.int ⟨.setp .lt (some .and), s32, false, [none, some 9], [.reg 0, .reg 1, .reg 10]⟩) :=
  rfl
example : (Decode.op env "setp.lt.s32" [.pair [.sink, .sink], r "%r0", r "%r1"]).isOk = false :=
  rfl

end
end PTX.Tests.IntOps
