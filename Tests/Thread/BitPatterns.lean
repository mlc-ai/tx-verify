-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Lemmas.Tcgen05.FloatBits

/-!
# Registers hold bit patterns (THREAD-BITS, THREAD-REG, THREAD-NUM, THREAD-BYTES)

Integer instructions read the bits of every data value, whatever its type; floating
instructions decode bits; `0f` constants keep their exact pattern.
-/

namespace PTX.Tests.BitPatterns
open PTX PTX.Proof
noncomputable section

/-- Exact real `add.f32`, the only form these tests execute. -/
def idealAddF32 : Assumption := Assumption.idealReal "test-ideal-add-f32" { float := [.add .f32] }
  "test"

def launch : Launch := { grid := 1, block := 1, params := fun _ => none }

/-- `mov.b32 %r0, 0f80000000` keeps the pattern of `-0.0`. -/
theorem mov_neg_zero :
    execLocal launch 0 {} (.move ⟨.scalar, .int .b 32, [some 0], [.f32imm 0x80000000]⟩) =
    .ok (next (setReg {} 0 (.bits 32 0x80000000))) := rfl

/-- `and.b32 %r1, %r0, 0x80000000` then reads its sign bit, ... -/
theorem and_neg_zero : execLocal launch 0 (setReg {} 0 (.bits 32 0x80000000))
    (.int ⟨.and, .int .b 32, false, [some 1], [.reg 0, .imm 0x80000000]⟩) =
    .ok (next (setReg (setReg {} 0 (.bits 32 0x80000000)) 1 (.bits 32 0x80000000))) := rfl

/-- ... while a floating instruction reads it as the number `0`. -/
theorem neg_zero_value : valFloat .f32 (.bits 32 0x80000000) = .ok 0 := by
  simp [valFloat, bitsAsFloat, classify, Value.bitPattern, Value.bytes, FloatFmt.bytes,
    FloatFmt.layout, Layout.decode, Layout.width, Layout.fieldVal, FVal.finite, bind, Except.bind,
    pure, Except.pure]

/-- A signed field magnitude encodes as that field (`Lemmas/Tcgen05/FloatBits.lean`). -/
theorem enc {fmt : FloatFmt} {F : Nat} {x : ℝ} (neg : Bool) (hF : F ≤ fmt.maxField)
    (hneg : neg = true → 0 < F)
    (hx : (if neg then -1 else 1) * (fmt.magnitude F : ℝ) = x) :
    fmt.encode x = (if neg then 2 ^ (fmt.expBits + fmt.mantBits) else 0) + F :=
  hx ▸ encode_magnitude fmt neg hF hneg

theorem f32_three_halves : FloatFmt.f32.encode (3 / 2) = 0x3FC00000 := by
  have h := enc (fmt := .f32) (F := 0x3FC00000) (x := 3 / 2) false (by decide) (by simp)
    (by norm_num [FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.expBits,
      FloatFmt.layout])
  simpa using h

theorem f32_one : FloatFmt.f32.encode 1 = 0x3F800000 := by
  have h := enc (fmt := .f32) (F := 0x3F800000) (x := 1) false (by decide) (by simp)
    (by norm_num [FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.expBits,
      FloatFmt.layout])
  simpa using h

theorem f16_one : FloatFmt.f16.encode 1 = 0x3C00 := by
  have h := enc (fmt := .f16) (F := 0x3C00) (x := 1) false (by decide) (by simp)
    (by norm_num [FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.expBits,
      FloatFmt.layout])
  simpa using h

theorem f16_neg_two : FloatFmt.f16.encode (-2) = 0xC000 := by
  have h := enc (fmt := .f16) (F := 0x4000) (x := -2) true (by decide) (by simp)
    (by norm_num [FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.expBits,
      FloatFmt.layout])
  simpa [FloatFmt.expBits, FloatFmt.mantBits, FloatFmt.layout] using h

/-- `%r1` holds `0f3F000000` (`0.5`); `add.f32 %r2, %r1, 0f3F800000` under `idealAddF32`. -/
def tAdd : TState := setReg {} 1 (.bits 32 0x3F000000)

theorem fadd_bits : execLocalA [idealAddF32] launch 0 tAdd
    (.float ({ op := .add, ty := ⟨.f32, 1⟩, dsts := [some 2],
               srcs := [.reg 1, .f32imm 0x3F800000] } : FloatInstr)) =
    .ok (next (setReg tAdd 2 (.float .f32 (3 / 2)))) := by
  simp [execLocalA, execLocalRule, idealAddF32, Assumption.idealReal, Assumption.execIdealFloat,
    Assumption.FloatForm.ofOp, Assumption.bindRead, Assumption.readERealOpnd, Assumption.readEReal,
    Assumption.readEReal.ofDatum, Assumption.addEReal, Assumption.erealValue, readReg, tAdd, setReg,
    classify, Value.bitPattern, Value.bytes, FloatFmt.bytes, FloatFmt.layout, Layout.decode,
    Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias, FVal.toValue, Layout.infPattern,
    Option.map, pure, Except.pure, - EReal.coe_one, - EReal.coe_mul, ← EReal.coe_add,
    EReal.toReal_coe]
  norm_num

/-- The sum is representable: `and.b32` and `mov.b32` read its IEEE pattern `0x3FC00000`. -/
theorem fadd_result_and : execLocal launch 0 (setReg {} 2 (.float .f32 (3 / 2)))
    (.int ⟨.and, .int .b 32, false, [some 3], [.reg 2, .imm 0xFFFFFFFF]⟩) =
    .ok (next (setReg (setReg {} 2 (.float .f32 (3 / 2))) 3 (.bits 32 0x3FC00000))) := by
  have hr : IntInstr.rule ⟨.and, .int .b 32, false, [some 3], [.reg 2, .imm 0xFFFFFFFF]⟩ =
      some .threadInt := rfl
  simp [execLocal, Op.rule, hr, DType.width, execInt, readBits,
    readReg, setReg,
    Value.bitPattern,
    f32_three_halves, truncBits, bind, Except.bind, pure, Except.pure]

theorem fadd_result_mov_bits :
    readBits launch 0 (setReg {} 2 (.float .f32 (3 / 2))) 32 (.reg 2) = .ok 0x3FC00000 := by
  simp [readBits, readReg, setReg, Value.bitPattern, f32_three_halves, truncBits, bind,
    Except.bind, pure, Except.pure]

/-- A stored `f32` loaded by `ld.b32`: the whole value, whose bits an integer instruction reads. -/
theorem ld_b32_of_f32 : (do
    let v ← rebuild 3 ((Value.float .f32 (3 / 2)).toBytes.map some)
    readBits launch 0 (setReg {} 0 v) 32 (.reg 0)) = .ok 0x3FC00000 := by
  simp [rebuild, Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ, Value.byteAt,
    readBits, readReg, setReg, Value.bitPattern, f32_three_halves, truncBits, bind, Except.bind,
    pure, Except.pure]

/-- `ld.b16` of the upper half of a stored `f32`: the high 16 bits of its pattern. -/
theorem ld_b16_high_of_f32 : (do
    let v ← rebuild 3 (((Value.float .f32 (3 / 2)).toBytes.drop 2).map some)
    readBits launch 0 (setReg {} 0 v) 16 (.reg 0)) = .ok 0x3FC0 := by
  simp [rebuild, rebuild.halves, rebuildBits, littleEndianBits, byteBits, intByte,
    Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ, Value.byteAt,
    readBits, readReg, setReg, Value.bitPattern, f32_three_halves, truncBits, bind, Except.bind,
    Option.bind, pure, Except.pure]

/-- A packed `f16x2` pair read as `.b32`: low half first. -/
theorem f16x2_as_b32 :
    readBits launch 0 (setReg {} 0 (.pair (.float .f16 1) (.float .f16 (-2)))) 32 (.reg 0) =
      .ok 0xC0003C00 := by
  simp [readBits, readReg, setReg, Value.bitPattern, Value.bytes, FloatFmt.bytes, f16_one,
    f16_neg_two, truncBits, bind, Except.bind, pure, Except.pure]

/-- `mov.b32` copies the pair unchanged, so its pattern is unchanged. -/
theorem f16x2_mov : execLocal launch 0 (setReg {} 0 (.pair (.float .f16 1) (.float .f16 (-2))))
    (.move ⟨.scalar, .int .b 32, [some 1], [.reg 0]⟩) =
    .ok (next (setReg (setReg {} 0 (.pair (.float .f16 1) (.float .f16 (-2)))) 1
      (.pair (.float .f16 1) (.float .f16 (-2))))) := by
  simp [execLocal, Op.rule, MoveInstr.rule, DType.width, execMove, readValue, readReg, setReg,
    Value.bytes,
    FloatFmt.bytes, bind, Except.bind, pure, Except.pure]

/-- A floating instruction of another format reads the same bits: the `f16` payload `1.0`
read as `bf16` is the pattern `0x3C00`, the number `2^-7`. -/
theorem f16_as_bf16 : valFloat .bf16 (.float .f16 1) = .ok (1 / 128) := by
  simp [valFloat, bitsAsFloat, classify, f16_one, Value.bitPattern, Value.bytes, FloatFmt.bytes,
    FloatFmt.layout, Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias,
    FVal.finite, bind, Except.bind, pure, Except.pure]
  norm_num

end
end PTX.Tests.BitPatterns
