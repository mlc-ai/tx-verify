-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Conversions of THREAD-CVT added with the `.f64` payload format, the 4-, 6- and 8-bit formats
without a payload format, and wider registers for floating operands (§9.7.10.24, §9.4.1 Tables 27
and 28): exact widening to `.f64`, integer rounding at `.f64` and from `.f64` to an integer,
integers of at most 32 bits to `.f64`, the unscaled widening of `.e2m1x2`, `.e2m3x2`, `.e3m2x2`,
`.ue5m3x2` and `.s2f6x2`, and floating operands in wider registers. Every expected value is
derived from the manual's text and the readings EXT-NARROW-FLOAT and EXT-UE8M0. The examples also
check the rule (`CvtInstr.rule`), the conversions that have none, and the decoding. -/
namespace PTX.Tests.CvtWide
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%rc".toList, 2, 8⟩],
    labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd1 = 4..5, %rs0..%rs1 = 6..7, %rc0..%rc1 = 8..9
private def r (n : String) : Syntax.Operand := .register n

private def f (t : FType) : DType := .float t
private def x2 (t : FType) : DType := .packed (.float t) 2

/-- Run conversion `c` on a state whose register 1 holds `v`. -/
private def run (c : CvtInstr) (v : Value) : Exec TState :=
  execLocal launch 0 (setReg {} 1 v) (.cvt c)

/-- The outcome in which register 0 receives `w` after register 1 held `v`. -/
private def out (v w : Value) : Exec TState := .ok (next (setReg (setReg {} 1 v) 0 w))

/-- A conversion with destination register 0, the extension `ext` of a wider destination, and
source register 1. -/
private def cv (dst src : DType) (rnd : Option CvtRnd := none)
    (ftz sat relu satfinite : Bool := false) (ext : MemExt := .same) : CvtInstr :=
  { dst, src, rnd, ftz, sat, relu, satfinite, d := 0, ext, srcs := [.reg 1] }

/-- A conversion whose rule is THREAD-CVT runs `execCvt`. -/
private theorem go {c : CvtInstr} {t : TState} (h : c.rule = some .threadCvt) :
    execLocal launch 0 t (.cvt c) = execCvt launch 0 t c := by
  simp only [execLocal, Op.rule, h]

/-- MAX_NORM of `.f64` is above every number of these tests. -/
private theorem f64_max_not_lt {q : ℚ} (hq : q ≤ 2 ^ 64) :
    ¬ ((9007199254740991 : ℚ) * 2 ^ 971 < q) := by
  have h1 : (2 : ℚ) ^ 64 ≤ 2 ^ 971 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h2 : (2 : ℚ) ^ 971 ≤ 9007199254740991 * 2 ^ 971 :=
    le_mul_of_one_le_left (by positivity) (by norm_num)
  exact not_lt.mpr (hq.trans (h1.trans h2))

/-- Evaluate a conversion with a rule: dispatch (the rule by `rfl`), the conversion by its
definitions, the arithmetic, and the rounding instances given as lemmas. -/
syntax "cvt_eval" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| cvt_eval $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (
      simp only [run, out, cv, f, x2]
      rw [go rfl]
      dsimp only [execCvt, FType.fmt?]
      norm_num [readCvtFloat, lowValue, lowBitsValue, readReg, readValue, readBits, setReg,
        Function.update_self, classify, Value.bitPattern, Value.bytes, FloatFmt.bytes,
        FloatFmt.layout, FType.layout?, Layout.decode, Layout.width, Layout.fieldVal,
        Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal, Layout.minNormal,
        Layout.maxNorm, Layout.topField, FVal.toValue, Layout.signPattern, Layout.infPattern,
        cvtFloatDst, CvtRnd.roundInt, CvtRnd.mode?, cvtIntOf, FVal.sat, reluFVal, pzoFVal,
        cvtFinish, widenElem, roundIntElem, cvtElem, packedElems, splitValue, FType.fmt?,
        cvtScales, cvtPack, cvtSpecial, cvtNum, cvtRound, satMaxNorm, FVal.ofRat, truncBits, intOf,
        toSigned,
        intSat, intBits, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Int.floor_eq_iff, Int.ceil_eq_iff, f64_max_not_lt, $ls,*]
      try rfl))

/-- `round` of a value of a binary layout, the field `F` (THREAD-FLOAT-ROUND). -/
macro "rexact" F:term : tactic => `(tactic| (rw [Layout.round_exact (F := $F)] <;>
  norm_num [RoundMode.applies, Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias,
    abs_of_pos, abs_of_neg]))

/-! ## Widening to `.f64` -/

-- `cvt.f64.f32`: 1.5 is kept; the `.f32` pattern of `-0` gives the `.f64` pattern of `-0`.
example : run (cv (f .f64) (f .f32)) (.bits 32 0x3FC00000) =
    out (.bits 32 0x3FC00000) (.float .f64 (3 / 2)) := by cvt_eval
example : run (cv (f .f64) (f .f32)) (.bits 32 0x80000000) =
    out (.bits 32 0x80000000) (.bits 64 0x8000000000000000) := by cvt_eval
-- The smallest `.f32` subnormal `0x00000001` (2^-149) is kept; `.ftz` flushes it to `+0`.
example : run (cv (f .f64) (f .f32)) (.bits 32 1) =
    out (.bits 32 1) (.float .f64 ((2 : ℝ) ^ (-149 : ℤ))) := by cvt_eval
example : run (cv (f .f64) (f .f32) (ftz := true)) (.bits 32 1) =
    out (.bits 32 1) (.float .f64 0) := by cvt_eval
-- `cvt.f64.f16`: `0x7BFF` is the largest `.f16` value, 65504.
example : run (cv (f .f64) (f .f16)) (.bits 16 0x7BFF) =
    out (.bits 16 0x7BFF) (.float .f64 65504) := by cvt_eval
-- `cvt.f64.bf16`: `0xBFC0` is -1.5.
example : run (cv (f .f64) (f .bf16)) (.bits 16 0xBFC0) =
    out (.bits 16 0xBFC0) (.float .f64 (-3 / 2)) := by cvt_eval
-- `cvt.sat.f64.f32` clamps to [0.0, 1.0] (".sat ... Applies to .f16 , .f32 , and .f64 types.").
example : run (cv (f .f64) (f .f32) (sat := true)) (.bits 32 0x40000000) =
    out (.bits 32 0x40000000) (.float .f64 1) := by cvt_eval
-- A NaN `.f32` source gives the opaque `.f64` NaN, and `+0` under `.sat`.
example : run (cv (f .f64) (f .f32)) (.bits 32 0x7FC00000) =
    out (.bits 32 0x7FC00000) (.nan .f64) := by cvt_eval
example : run (cv (f .f64) (f .f32) (sat := true)) (.bits 32 0x7FC00000) =
    out (.bits 32 0x7FC00000) (.float .f64 0) := by cvt_eval

/-! ## `.f64` with integer rounding -/

-- `cvt.f64.f64` copies the number; `cvt.rni.f64.f64` rounds ties to even.
example : run (cv (f .f64) (f .f64)) (.bits 64 0xC000000000000000) =
    out (.bits 64 0xC000000000000000) (.float .f64 (-2)) := by cvt_eval
example : run (cv (f .f64) (f .f64) (rnd := some .rni)) (.bits 64 0x4004000000000000) =
    out (.bits 64 0x4004000000000000) (.float .f64 2) := by cvt_eval
-- `cvt.rzi.f64.f64` of -0.25 is `-0`; the `.f64` bit pattern of 1.0 is `0x3FF0000000000000`.
example : run (cv (f .f64) (f .f64) (rnd := some .rzi)) (.bits 64 0xBFD0000000000000) =
    out (.bits 64 0xBFD0000000000000) (.bits 64 0x8000000000000000) := by cvt_eval
example : run (cv (f .f64) (f .f64) (rnd := some .rpi)) (.bits 64 0x3FF0000000000000) =
    out (.bits 64 0x3FF0000000000000) (.float .f64 1) := by cvt_eval
-- An `.f64` NaN (`0x7FF8000000000000`) gives the opaque NaN, and an infinity
-- (`0x7FF0000000000000`) converted to `.s32` is clamped to MAXINT.
example : run (cv (f .f64) (f .f64) (rnd := some .rni)) (.bits 64 0x7FF8000000000000) =
    out (.bits 64 0x7FF8000000000000) (.nan .f64) := by cvt_eval
example : run (cv (.int .s 32) (f .f64) (rnd := some .rzi)) (.bits 64 0x7FF0000000000000) =
    out (.bits 64 0x7FF0000000000000) (.bits 32 0x7FFFFFFF) := by cvt_eval

/-! ## `.f64` to an integer -/

-- `cvt.rzi.s32.f64` of -2.7 is -2; `cvt.rmi.s64.f64` of -2.5 is -3.
example : run (cv (.int .s 32) (f .f64) (rnd := some .rzi)) (.bits 64 0xC00599999999999A) =
    out (.bits 64 0xC00599999999999A) (.bits 32 0xFFFFFFFE) := by cvt_eval
example : run (cv (.int .s 64) (f .f64) (rnd := some .rmi)) (.bits 64 0xC004000000000000) =
    out (.bits 64 0xC004000000000000) (.bits 64 0xFFFFFFFFFFFFFFFD) := by cvt_eval
-- The result is clamped to the destination range: 2^40 to `.u32` is MAXINT.
example : run (cv (.int .u 32) (f .f64) (rnd := some .rni)) (.bits 64 0x4270000000000000) =
    out (.bits 64 0x4270000000000000) (.bits 32 0xFFFFFFFF) := by cvt_eval

/-! ## Integers to `.f64` -/

-- `cvt.rn.f64.s32` of MININT and `cvt.rz.f64.u32` of MAXINT are exact.
private theorem f64_minint {x : ℝ} (hx : x = -2147483648) :
    (Layout.binary 11 52 true .ieee).round .rn .inf x false = some (.fin (-2147483648)) := by
  subst hx; rexact 0x41E0000000000000
private theorem f64_maxu {x : ℝ} (hx : x = 4294967295) :
    (Layout.binary 11 52 true .ieee).round .rz .inf x false = some (.fin 4294967295) := by
  subst hx; rexact 0x41EFFFFFFFE00000
private theorem f64_m1 {x : ℝ} (hx : x = -1) :
    (Layout.binary 11 52 true .ieee).round .rm .inf x false = some (.fin (-1)) := by
  subst hx; rexact 0x3FF0000000000000
private theorem f64_7 {x : ℝ} (hx : x = 7) :
    (Layout.binary 11 52 true .ieee).round .rp .satfinite x false = some (.fin 7) := by
  subst hx; rexact 0x401C000000000000
example : run (cv (f .f64) (.int .s 32) (rnd := some .rn)) (.bits 32 0x80000000) =
    out (.bits 32 0x80000000) (.float .f64 (-2147483648)) := by cvt_eval [f64_minint]
example : run (cv (f .f64) (.int .u 32) (rnd := some .rz)) (.bits 32 0xFFFFFFFF) =
    out (.bits 32 0xFFFFFFFF) (.float .f64 4294967295) := by cvt_eval [f64_maxu]
example : run (cv (f .f64) (.int .s 8) (rnd := some .rm)) (.bits 32 0xFF) =
    out (.bits 32 0xFF) (.float .f64 (-1)) := by cvt_eval [f64_m1]
example : run (cv (f .f64) (.int .u 16) (rnd := some .rp) (sat := true)) (.bits 16 7) =
    out (.bits 16 7) (.float .f64 1) := by cvt_eval [f64_7]

/-! ## Wider registers for floating operands (Tables 27 and 28) -/

-- An `.f16` source in a 32-bit register is its low 16 bits: `0x3C00` is 1.
example : run (cv (f .f32) (f .f16) (ftz := true)) (.bits 32 0xABCD3C00) =
    out (.bits 32 0xABCD3C00) (.float .f32 1) := by cvt_eval
-- An `.f32` source in a 64-bit register holding a pair is its low half.
example : run (cv (f .f64) (f .f32)) (.pair (.bits 32 0x3FC00000) (.bits 32 0x40E00000)) =
    out (.pair (.bits 32 0x3FC00000) (.bits 32 0x40E00000)) (.float .f64 (3 / 2)) := by cvt_eval
-- An `.f16` source of a float-to-integer conversion in a 64-bit register.
example : run (cv (.int .s 32) (f .f16) (rnd := some .rni)) (.bits 64 0xFFFFFFFFFFFFC000) =
    out (.bits 64 0xFFFFFFFFFFFFC000) (.bits 32 0xFFFFFFFE) := by cvt_eval
-- A wider destination receives the result zero-extended.
example : run (cv (f .f32) (f .f32) (rnd := some .rni) (ext := .zero 64)) (.bits 32 0x40200000) =
    out (.bits 32 0x40200000) (.pair (.float .f32 2) (.bits 32 0)) := by cvt_eval
private theorem f16_255 {x : ℝ} (hx : x = 255) :
    (Layout.binary 5 10 true .ieee).round .rn .inf x false = some (.fin 255) := by
  subst hx; rexact 0x5BF8
example : run (cv (f .f16) (.int .u 8) (rnd := some .rn) (ext := .zero 32)) (.bits 16 0xFF) =
    out (.bits 16 0xFF) (.pair (.float .f16 255) (.bits 16 0)) := by cvt_eval [f16_255]
example : run (cv (f .f32) (f .f16) (ftz := true) (ext := .zero 64)) (.bits 16 0x8000) =
    out (.bits 16 0x8000) (.pair (.bits 32 0x80000000) (.bits 32 0)) := by cvt_eval
-- A `.bf16` source must have its width.
example : run (cv (f .f32) (f .bf16)) (.bits 32 0x3FC0) = .error .typeMismatch := by cvt_eval

/-! ## `.e2m1x2` (EXT-NARROW-FLOAT): two 4-bit elements of a `.b8` source -/

-- `0xF2`: the low element `0x2` is 1, the high element `0xF` is -6, the largest magnitude.
example : run (cv (x2 .f16) (x2 .e2m1) (rnd := some .rn)) (.bits 8 0xF2) =
    out (.bits 8 0xF2) (.pair (.float .f16 1) (.float .f16 (-6))) := by cvt_eval
-- `0x81`: the subnormal `0x1` is 0.5, and `0x8` is `-0`.
example : run (cv (x2 .bf16) (x2 .e2m1) (rnd := some .rn)) (.bits 8 0x81) =
    out (.bits 8 0x81) (.pair (.float .bf16 (1 / 2)) (.bits 16 0x8000)) := by cvt_eval
-- `.relu` clamps -6 to 0; a negative zero under `.relu` has no rule.
example : run (cv (x2 .f16) (x2 .e2m1) (rnd := some .rn) (relu := true)) (.bits 8 0xF2) =
    out (.bits 8 0xF2) (.pair (.float .f16 1) (.float .f16 0)) := by cvt_eval
example : run (cv (x2 .f16) (x2 .e2m1) (rnd := some .rn) (relu := true)) (.bits 8 0x82) =
    .error .noRule := by cvt_eval
-- The source must be 8 bits wide.
example : run (cv (x2 .f16) (x2 .e2m1) (rnd := some .rn)) (.bits 16 0x0022) =
    .error .typeMismatch := by cvt_eval

/-! ## `.e2m3x2` and `.e3m2x2` (EXT-NARROW-FLOAT): 6-bit elements in the bytes of a `.b16` -/

-- `.e2m3`: `0x07` is the subnormal 7/8, `0x3F` is -7.5, the largest magnitude.
example : run (cv (x2 .f16) (x2 .e2m3) (rnd := some .rn)) (.bits 16 0x3F07) =
    out (.bits 16 0x3F07) (.pair (.float .f16 (7 / 8)) (.float .f16 (-15 / 2))) := by cvt_eval
-- An element whose two most significant bits are not zero has no rule.
example : run (cv (x2 .bf16) (x2 .e2m3) (rnd := some .rn)) (.bits 16 0x0040) =
    .error .noRule := by cvt_eval
-- `.e3m2`: `0x01` is the subnormal 1/16; `0x3F` is -28, which `.relu` clamps to 0.
example : run (cv (x2 .bf16) (x2 .e3m2) (rnd := some .rn) (relu := true)) (.bits 16 0x3F01) =
    out (.bits 16 0x3F01) (.pair (.float .bf16 (1 / 16)) (.float .bf16 0)) := by cvt_eval
example : run (cv (x2 .f16) (x2 .e3m2) (rnd := some .rn)) (.bits 16 0x1F20) =
    out (.bits 16 0x1F20) (.pair (.bits 16 0x8000) (.float .f16 28)) := by cvt_eval

/-! ## `.ue5m3x2` (EXT-NARROW-FLOAT) -/

-- `0x01` is 2^-17, `0xFE` is 114688, the largest finite value.
example : run (cv (x2 .bf16) (x2 .ue5m3) (rnd := some .rn)) (.bits 16 0xFE01) =
    out (.bits 16 0xFE01) (.pair (.float .bf16 ((2 : ℝ) ^ (-17 : ℤ))) (.float .bf16 114688)) := by
  cvt_eval
-- `0x78` is 1; `0x77` is 0.9375.
example : run (cv (x2 .f16) (x2 .ue5m3) (rnd := some .rn)) (.bits 16 0x7778) =
    out (.bits 16 0x7778) (.pair (.float .f16 1) (.float .f16 (15 / 16))) := by cvt_eval
-- `0xF8` (2^16) overflows `.f16` and has no rule; `0xFF` is NaN, which widens to the opaque NaN.
example : run (cv (x2 .f16) (x2 .ue5m3) (rnd := some .rn)) (.bits 16 0xF878) =
    .error .noRule := by cvt_eval
example : run (cv (x2 .bf16) (x2 .ue5m3) (rnd := some .rn)) (.bits 16 0xFF78) =
    out (.bits 16 0xFF78) (.pair (.float .bf16 1) (.nan .bf16)) := by cvt_eval

/-! ## `.s2f6x2` (§5.2.4) -/

-- "Positive max representation = 01.111111 = 127 * 2^(-6) = 1.984375 Negative max
-- representation = 10.000000 = -128 * 2^(-6) = -2.0"; `.satfinite` does not change them.
example : run (cv (x2 .bf16) (x2 .s2f6) (rnd := some .rn)) (.bits 16 0x807F) =
    out (.bits 16 0x807F) (.pair (.float .bf16 (127 / 64)) (.float .bf16 (-2))) := by cvt_eval
example : run (cv (x2 .bf16) (x2 .s2f6) (rnd := some .rn) (satfinite := true)) (.bits 16 0x807F) =
    out (.bits 16 0x807F) (.pair (.float .bf16 (127 / 64)) (.float .bf16 (-2))) := by cvt_eval
example : run (cv (x2 .bf16) (x2 .s2f6) (rnd := some .rn) (relu := true)) (.bits 16 0xC001) =
    out (.bits 16 0xC001) (.pair (.float .bf16 (1 / 64)) (.float .bf16 0)) := by cvt_eval

/-! ## Rules -/

-- Narrowing from `.f64`, integers of 64 bits to `.f64`, a scale factor, `.rs` and narrowing to
-- the formats without a payload format have rules (Tests/Thread/CvtRound.lean).
example : CvtInstr.rule (cv (f .f32) (f .f64) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f64) (.int .s 64) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f64) (.int .u 64) (rnd := some .rz)) = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .bf16, src := x2 .e2m1, rnd := some .rn, scaled := true, d := 0,
    srcs := [.reg 1, .reg 2] } = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .f16, src := f .f32, rnd := some .rs, relu := false, d := 0,
    srcs := [.reg 1, .reg 2, .reg 3] } = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .e2m1, src := f .f32, rnd := some .rn, satfinite := true, d := 0,
    srcs := [.reg 1, .reg 2] } = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .ue5m3, src := x2 .bf16, rnd := some .rn, d := 0, srcs := [.reg 1] } =
    some .threadCvt := rfl
-- A scaled widening to `.f16x2` has none: the syntax gives the scale factor to `.bf16x2` only.
example : CvtInstr.rule {
    dst := x2 .f16, src := x2 .e2m1, rnd := some .rn, scaled := true, d := 0,
    srcs := [.reg 1, .reg 2] } = none := rfl
example : CvtInstr.rule (cv (f .f64) (f .f32)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f64) (f .f64) (rnd := some .rni)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (.int .u 64) (f .f64) (rnd := some .rpi)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f64) (.int .u 32) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (x2 .f16) (x2 .e2m1) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (x2 .bf16) (x2 .s2f6) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f32) (f .f32) (rnd := some .rni) (ext := .zero 64)) =
    some .threadCvt := rfl

/-! ## Decoding -/

-- Wider floating registers: an `.f32` source in a 64-bit register, an `.f32` destination in a
-- 64-bit register (zero-extended), an `.f16` destination in a 32-bit register.
example : Decode.op env "cvt.f64.f32" [r "%rd0", r "%rd1"] =
    .ok (.cvt { dst := f .f64, src := f .f32, d := 4, srcs := [.reg 5] }) := rfl
example : Decode.op env "cvt.rni.f32.f32" [r "%rd0", r "%r1"] =
    .ok (.cvt {
      dst := f .f32, src := f .f32, rnd := some .rni, d := 4, ext := .zero 64,
      srcs := [.reg 1] }) := rfl
example : Decode.op env "cvt.rn.f16.s32" [r "%r0", r "%r1"] =
    .ok (.cvt {
      dst := f .f16, src := .int .s 32, rnd := some .rn, d := 0, ext := .zero 32,
      srcs := [.reg 1] }) := rfl
example : Decode.op env "cvt.rn.f16x2.e2m1x2" [r "%r0", r "%rc1"] =
    .ok (.cvt { dst := x2 .f16, src := x2 .e2m1, rnd := some .rn, d := 0, srcs := [.reg 9] }) :=
  rfl
-- Rejected: a narrowing without a rounding modifier, a wider `.bf16` source or destination, an
-- `.e2m1x2` source that is not `.b8`, and an `.f64` destination in a 32-bit register.
example : (Decode.op env "cvt.f32.f64" [r "%r0", r "%rd1"]).isOk = false := rfl
example : (Decode.op env "cvt.f32.bf16" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "cvt.rn.bf16.f32" [r "%r0", r "%r1"]).isOk = false := rfl
example : (Decode.op env "cvt.rn.f16x2.e2m1x2" [r "%r0", r "%rs1"]).isOk = false := rfl
example : (Decode.op env "cvt.f64.f32" [r "%r0", r "%r1"]).isOk = false := rfl

end
end PTX.Tests.CvtWide
