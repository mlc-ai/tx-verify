-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Lemmas.Tcgen05.TcMmaOperands
public import Lemmas.Tcgen05.TcMmaResultLayout
public import Lemmas.Tcgen05.TcMmaValue
public import Assumption.IdealReal
public import Lemmas.Tcgen05.FloatBits
public import Mathlib.Tactic

/-! `tcgen05.mma{.ws}.cta_group::{1,2}.kind::tf32`: decoding, operand geometry (eight 4-byte
elements per 32-byte row), result cells and the ideal-real value with FP32 inputs truncated to
TF32 (EXT-TCTF32, `Tools/probes/tcgen05_ws_ts_tf32.ptx`). -/
namespace PTX.Tests.TcMmaTf32
open TcMma Assumption
noncomputable section

/-! ## Decoding -/

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 40, 32⟩, ⟨"rd".toList, 10, 64⟩, ⟨"p".toList, 5, 1⟩], labels := [],
      params := [] }
example : Decode.op env "tcgen05.mma.cta_group::2.kind::tf32"
    [.address [.register "r0"], .register "rd0", .register "rd1", .register "r1",
      .vector (List.replicate 8 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .two false .tf32 0 (.smem (.reg 40)) (.reg 41) (.reg 1)
      (List.replicate 8 (.reg 3)) (.reg 50)) := rfl
example : Decode.op env "tcgen05.mma.cta_group::1.kind::tf32"
    [.address [.register "r0"], .address [.register "r2"], .register "rd1", .register "r1",
      .vector (List.replicate 4 (.register "r3")), .register "p0"] =
    .ok (.tcMma <| .dense .one false .tf32 0 (.tmem 2 0) (.reg 41) (.reg 1)
      (List.replicate 4 (.reg 3)) (.reg 50)) := rfl

/-! ## Instruction descriptors: A/B type 2 (TF32), D type 1 (F32) -/

private def tf (group : CtaGroup) (m n : Nat) (ws : Bool) : Descriptor :=
  ⟨group, .tf32, m, n, false, false, false, false, ws⟩
-- The probe's descriptor (`.ws`, M = 128, N = 64) and the dense shapes of kind::f16.
example : decode .one true .tf32 135268624 = some (tf .one 128 64 true) := by decide
example : decode .one false .tf32 134351120 = some (tf .one 128 8 false) := by decide
example : decode .one false .tf32 67242256 = some (tf .one 64 8 false) := by decide
example : decode .two false .tf32 268699920 = some (tf .two 256 16 false) := by decide
-- Negation is retained.
example : decode .one false .tf32 (134351120 + 2 ^ 13) =
    some { tf .one 128 8 false with negateA := true } := by decide
-- §9.7.18.10.1: "For .kind::tf32, the transpose operations on matrices A and B are supported
-- only with 128B swizzling mode with 32B swizzle-atomicity." The swizzle belongs to the shared
-- descriptor: the instruction descriptor decodes, the pairing is checked by the operand address.
example : decode .one false .tf32 (134351120 + 2 ^ 16) =
    some { tf .one 128 8 false with transposeB := true } := by decide
example : decode .one false .tf32 (134351120 + 2 ^ 15) =
    some { tf .one 128 8 false with transposeA := true } := by decide
-- D must be F32, A and B both TF32, no saturation.
example : decode .one false .tf32 (134351120 - 16) = none := by decide
example : decode .one false .tf32 (134351120 - 256) = none := by decide
example : decode .one false .tf32 (134351120 - 2048) = none := by decide
example : decode .one false .tf32 (134351120 + 8) = none := by decide
-- The same type fields under kind::f16 or kind::i8 are not TF32.
example : decode .one false .f16 134351120 = none ∧ decode .one false .i8 134351120 = none := by
  decide
-- kind::f16's shapes: N a multiple of 8 (16 for cta_group::2), M = 32 only with `.ws`.
example : decode .two false .tf32 (268699920 - 2 ^ 17) = none := by decide
example : ¬ Valid (tf .one 32 64 false) ∧ Valid (tf .one 32 64 true) := by decide

/-! ## Transposed operands: only the 128B swizzle with 32B atomicity (Table 65) -/

section Transposed
private def mnA : Descriptor := { tf .one 128 8 false with transposeA := true }
private def mnB : Descriptor := { tf .one 128 8 false with transposeB := true }
private def sw (s : TcShared.Swizzle) (start : Nat := 0) : TcShared.Descriptor :=
  ⟨start, 4096, 512, 0, false, false, s⟩
private def loc (d : Descriptor) (s : TcShared.Swizzle) (op : Operand) (row k : Nat) :
    Option Nat := do
  let o : OperandSpec := ⟨d, sw s, sw s, 3, 3, none, {}⟩
  (o.byteLoc op (row * 32 + k * 4)).map (·.addr)
-- A is M-major: byte of (m, k) is 4 m + 128 k in the 8x4-element atom, 32-byte chunks XORed
-- with the 128-byte row number modulo 4.
example : loc mnA .b128x32 .a 0 0 = some 0 := by decide
example : loc mnA .b128x32 .a 1 0 = some 4 := by decide
example : loc mnA .b128x32 .a 8 0 = some 32 := by decide
example : loc mnA .b128x32 .a 0 1 = some 160 := by decide
example : loc mnA .b128x32 .a 8 1 = some 128 := by decide
example : loc mnA .b128x32 .a 0 2 = some 320 := by decide
example : loc mnA .b128x32 .a 0 3 = some 480 := by decide
-- The stride field separates K groups of four, the leading field M/N atoms of 32 elements.
example : loc mnA .b128x32 .a 0 4 = some 512 := by decide
example : loc mnA .b128x32 .a 32 0 = some 4096 := by decide
-- B is N-major with the same layout.
example : loc mnB .b128x32 .b 4 1 = some 176 := by decide
-- Every other swizzle is rejected for a transposed tf32 operand.
example : [TcShared.Swizzle.none, .b32, .b64, .b128].all
    (fun s => (loc mnA s .a 0 0).isNone && (loc mnB s .b 0 0).isNone) = true := by decide
-- Non-transposed (K-major) operands have no 32B-atomicity atom.
example : loc (tf .one 128 8 false) .b128x32 .a 0 0 = none := by decide
example : Valid mnA ∧ Valid mnB := by decide
end Transposed

/-! ## Operand geometry: eight 4-byte elements per 32-byte row -/

example : Kind.width .tf32 = 4 ∧ Kind.k .tf32 = 8 := ⟨rfl, rfl⟩
example : Operand.bytes .a (tf .one 128 8 false) = 128 * 32 ∧
    Operand.bytes .b (tf .one 128 8 false) = 8 * 32 := by decide
private def k8 : TcShared.Descriptor := ⟨0, 128, 256, 0, false, false, .none⟩
private def spec (d : Descriptor) : OperandSpec := ⟨d, k8, k8, 3, 3, none, {}⟩
-- K-major, no swizzle: element (i, k) byte b is the probe layout's byte 4k + b of row i:
-- 16 (i % 8) + 256 (i / 8) + (4k + b) % 16 + 128 ((4k + b) / 16).
example : (spec (tf .one 128 8 false)).byteLoc .a (4 * 0 + 0) = some ⟨.shared, 3, 0⟩ := by decide
example : (spec (tf .one 128 8 false)).byteLoc .a (4 * 3 + 2) = some ⟨.shared, 3, 14⟩ := by decide
example : (spec (tf .one 128 8 false)).byteLoc .a (4 * 4) = some ⟨.shared, 3, 128⟩ := by decide
example : (spec (tf .one 128 8 false)).byteLoc .a (32 * 9 + 4 * 7 + 3) =
    some ⟨.shared, 3, 16 * 1 + 256 * 1 + 15 + 128⟩ := by decide
example : (spec (tf .one 128 8 false)).byteLoc .b (32 * 7 + 4 * 5 + 1) =
    some ⟨.shared, 3, 16 * 7 + 5 + 128⟩ := by decide
-- A in Tensor Memory: row q's eight elements fill eight 32-bit columns of lane q.
private def ts : OperandSpec := { spec (tf .one 128 64 true) with aTmem := some 64 }
example : ∀ k < 8, ∀ b < 4, aCell ts (32 * 9 + 4 * k + b) = some (⟨3, 9, 64 + k⟩, b) := by decide
-- Results: one F32 word per element, Layout D.
example : resultCell (spec (tf .one 128 8 false)) 40 127 7 = some ⟨3, 127, 47⟩ := by decide

/-! ## Values: FP32 containers truncated to TF32 -/

private theorem f32_one : f32Value 0x3F800000 = some 1 := by
  norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
    FloatFmt.expBits,
    FloatFmt.bias, FloatFmt.layout]
private theorem f32_m : f32Value 0xBF80E000 = some (-(1 + 7 / 1024)) := by
  norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
    FloatFmt.expBits,
    FloatFmt.bias, FloatFmt.layout]
/-- A 4-byte value whose bit pattern `u`, with the low 13 mantissa bits cleared, encodes `q`. -/
private theorem tf32_of {v : Value} {u : Nat} {q : ℚ} (hv : v.bitPattern = some u)
    (hb : v.bytes = 4) (hq : f32Value ((u &&& 0xFFFFE000) % 2 ^ 64) = some q) :
    tf32Value v = .ok q := by
  have hq' : FloatFmt.f32.decode ((u &&& 0xFFFFE000) % 2 ^ 64) = some q := hq
  simp only [tf32Value, hv, hb, ↓reduceIte]
  rw [bitsAsFloat_eq (v := .bits 32 (BitVec.ofNat 64 (u &&& 0xFFFFE000))) (by simp)]
  simp only [Value.bitPattern, Value.bytes, FloatFmt.bytes, BitVec.toNat_ofNat]
  rw [hq']
  rfl
-- 1 + 2^-11 + 2^-12 has no TF32 bits below 1: it is 1.
example : tf32Value (.bits 32 (BitVec.ofNat 64 0x3F801800)) = .ok 1 := by
  have hm : (0x3F801800 &&& 0xFFFFE000) % 2 ^ 64 = 0x3F800000 := by decide
  have h := tf32_of (v := .bits 32 (BitVec.ofNat 64 0x3F801800)) (u := 0x3F801800) rfl rfl
    (by rw [hm]; exact f32_one)
  rw [h]; norm_num
-- Truncation is toward zero for negative values too (not round-to-nearest).
example : tf32Value (.bits 32 (BitVec.ofNat 64 0xBF80F000)) = .ok (-(1 + 7 / 1024)) := by
  have hm : (0xBF80F000 &&& 0xFFFFE000) % 2 ^ 64 = 0xBF80E000 := by decide
  have h := tf32_of (v := .bits 32 (BitVec.ofNat 64 0xBF80F000)) (u := 0xBF80F000) rfl rfl
    (by rw [hm]; exact f32_m)
  rw [h]; congr 1; push_cast; ring
-- The kept bits are exactly the top 19.
example : (BitVec.ofNat 64 (0x40490000 + 0x1FFF) &&& 0xFFFFE000).toNat = 0x40490000 ∧
    (BitVec.ofNat 64 (0x40490000 + 0x1000) &&& 0xFFFFE000).toNat = 0x40490000 ∧
    (BitVec.ofNat 64 (0x40490000 + 0x2000) &&& 0xFFFFE000).toNat = 0x40492000 := by decide
-- An FP32 payload is read through its IEEE pattern (THREAD-BITS): `1.0` is `0x3F800000`.
example : tf32Value (.float .f32 1) = .ok 1 := by
  have he : FloatFmt.f32.encode 1 = 0x3F800000 := by
    have h := Proof.encode_magnitude .f32 (F := 0x3F800000) false (by decide) (by simp)
    have hm : (FloatFmt.f32.magnitude 0x3F800000 : ℝ) = 1 := by
      norm_num [FloatFmt.magnitude_eq, FloatFmt.mantBits, FloatFmt.bias, FloatFmt.expBits,
        FloatFmt.layout]
    simpa [hm] using h
  have hm : (0x3F800000 &&& 0xFFFFE000) % 2 ^ 64 = 0x3F800000 := by decide
  have h := tf32_of (v := .float .f32 1) (u := 0x3F800000) (by simp [Value.bitPattern, he]) rfl
    (by rw [hm]; exact f32_one)
  rw [h]; norm_num
-- A container of another width has no TF32 value.
example : tf32Value (.bits 16 0) = .error .typeMismatch := rfl

/-! ## The profile -/

-- Without an assumption kind::tf32 has no value; the scoped ideal-real one supplies it, and
-- only for the kinds it names.
private def idealTf32 : Assumption := idealReal "test-ideal-tf32" { mma := [.tf32] } "test"
private def idealF16 : Assumption := idealReal "test-ideal-f16" { mma := [.f16 .f16 .f32] } "test"

example (a b : List (Option Byte)) (old : Option Value) :
    eval [] (tf .one 128 8 false) false a b old 0 0 = .error .noRule := rfl
example (a b : List (Option Byte)) (old : Option Value) :
    eval [idealTf32] (tf .one 128 8 false) false a b old 0 0 =
      execIdealMma (tf .one 128 8 false) false a b old 0 0 := rfl
example (a b : List (Option Byte)) (old : Option Value) :
    eval [idealF16] (tf .one 128 8 false) false a b old 0 0 = .error .noRule := rfl
-- Operand arrays of the wrong length have no rule.
example (a b : List (Option Byte)) (ha : a.length = 7) (acc : Bool) (old : Option Value) :
    execIdealMma (tf .one 128 8 false) acc a b old 0 0 = .error .noRule := by
  simp [execIdealMma, ha, Operand.bytes, Operand.rows, Operand.extent, tf, Kind.k, Kind.width,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
-- `.ws` with M < 128 reads A row `operandRow` (the output's lane), as for the other kinds.
example : operandRow (tf .one 64 64 true) 5 40 = 69 := by decide

/-- A 4-byte operand element holding the FP32 pattern `u`. -/
private def w (u : Nat) : List (Option Byte) :=
  (List.range 4).map fun k => some (.bits 32 (BitVec.ofNat 64 u), k)
private theorem elem (o : Operand) (u v : Nat) (hu : u < 2 ^ 64)
    (hm : (u &&& 0xFFFFE000) % 2 ^ 64 = v)
    {q : ℚ} (hq : f32Value v = some q) : idealMmaElement .tf32 o (w u) 0 0 = .ok q := by
  have ht := tf32_of (v := .bits 32 (BitVec.ofNat 64 u)) (u := u)
    (by simp [Value.bitPattern, Nat.mod_eq_of_lt (show u < 18446744073709551616 by simpa using hu)])
    rfl (by rw [hm]; exact hq)
  simp [idealMmaElement, elementBytes, Kind.k, Kind.width, w, rebuild, Value.toBytes, Value.bytes,
    Value.byteAt, List.range_succ,
    ht, bind, Except.bind, pure, Except.pure]
-- One contraction step: truncated A (1 + 2^-11 + 2^-12 → 1) times B (1).
example : idealMmaDot (tf .one 128 8 false) (w 0x3F801800) (w 0x3F800000) 0 0 1 = .ok 1 := by
  have ha := elem .a 0x3F801800 0x3F800000 (by decide) (by decide) f32_one
  have hb := elem .b 0x3F800000 0x3F800000 (by decide) (by decide) f32_one
  simp only [Rat.cast_one] at ha hb
  simp [idealMmaDot, ha, hb, tf, bind, Except.bind, pure, Except.pure]
-- Negating A negates the product of the truncated values.
example : idealMmaDot { tf .one 128 8 false with negateA := true } (w 0xBF80F000) (w 0x3F800000)
    0 0 1 = .ok (1 + 7 / 1024) := by
  have ha := elem .a 0xBF80F000 0xBF80E000 (by decide) (by decide) f32_m
  have hb := elem .b 0x3F800000 0x3F800000 (by decide) (by decide) f32_one
  simp only [Rat.cast_one] at hb
  simp [idealMmaDot, ha, hb, tf, bind, Except.bind, pure, Except.pure]

end
end PTX.Tests.TcMmaTf32
