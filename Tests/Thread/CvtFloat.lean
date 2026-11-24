-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Floating conversions of THREAD-CVT (§9.7.10.24): exact widening, `.ftz`, `.sat`, integer
rounding to an integral value or to an integer, integer-to-floating conversions and the widening
of packed 8-bit elements, with the sign of zero kept and NaN and infinity inputs. Every expected
value is derived from the manual's text. The examples also check the rule (`CvtInstr.rule`) and
the conversions that have none; Tests/Thread/CvtRound.lean has the conversions that round. -/
namespace PTX.Tests.CvtFloat
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩], labels := [],
      params := [] }
private def r (n : String) : Syntax.Operand := .register n

private def f (t : FType) : DType := .float t
private def x2 (t : FType) : DType := .packed (.float t) 2

/-- Run conversion `c` on a state whose register 1 holds `v`. -/
private def run (c : CvtInstr) (v : Value) : Exec TState :=
  execLocal launch 0 (setReg {} 1 v) (.cvt c)

/-- The outcome in which register 0 receives `w` after register 1 held `v`. -/
private def out (v w : Value) : Exec TState := .ok (next (setReg (setReg {} 1 v) 0 w))

/-- A conversion with destination register 0 and source register 1. -/
private def cv (dst src : DType) (rnd : Option CvtRnd := none) (ftz sat relu : Bool := false) :
    CvtInstr :=
  { dst, src, rnd, ftz, sat, relu, d := 0, srcs := [.reg 1] }

/-- A conversion whose rule is THREAD-CVT runs `execCvt`. -/
private theorem go {c : CvtInstr} {t : TState} (h : c.rule = some .threadCvt) :
    execLocal launch 0 t (.cvt c) = execCvt launch 0 t c := by
  simp only [execLocal, Op.rule, h]

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
        MonadExceptOf.throw, Int.floor_eq_iff, Int.ceil_eq_iff, $ls,*]
      try rfl))

/-- `round` of a value of a binary layout, the field `F` (THREAD-FLOAT-ROUND). -/
macro "rexact" F:term : tactic => `(tactic| (rw [Layout.round_exact (F := $F)] <;>
  norm_num [RoundMode.applies, Layout.topField, Layout.fieldVal, Layout.magnitude, Layout.bias,
    abs_of_pos, abs_of_neg]))

/-! ## Widening without rounding -/

-- `cvt.f32.bf16`: `0x3FC0` is 1.5; the bf16 pattern of `-0` gives the f32 pattern of `-0`.
example : run (cv (f .f32) (f .bf16)) (.bits 16 0x3FC0) =
    out (.bits 16 0x3FC0) (.float .f32 (3 / 2)) := by cvt_eval
example : run (cv (f .f32) (f .bf16)) (.bits 16 0x8000) =
    out (.bits 16 0x8000) (.bits 32 0x80000000) := by cvt_eval
-- "For cvt.f32.bf16 , NaN input yields unspecified NaN": the opaque NaN.
example : run (cv (f .f32) (f .bf16)) (.bits 16 0x7FC0) =
    out (.bits 16 0x7FC0) (.nan .f32) := by cvt_eval
-- `cvt.ftz.f32.bf16` flushes the subnormal result to a zero of its sign.
example : run (cv (f .f32) (f .bf16) (ftz := true)) (.bits 16 0x0001) =
    out (.bits 16 0x0001) (.float .f32 0) := by cvt_eval
example : run (cv (f .f32) (f .bf16) (ftz := true)) (.bits 16 0x8001) =
    out (.bits 16 0x8001) (.bits 32 0x80000000) := by cvt_eval
-- Without `.ftz` the bf16 subnormal `0x0001` (2^-133) is kept.
example : run (cv (f .f32) (f .bf16)) (.bits 16 0x0001) =
    out (.bits 16 0x0001) (.float .f32 ((2 : ℝ) ^ (-133 : ℤ))) := by cvt_eval
-- `cvt.sat.f32.f16` clamps to [0.0, 1.0] (`0x4000` is 2.0, `0xBC00` is -1.0); a negative zero
-- has no rule.
example : run (cv (f .f32) (f .f16) (sat := true)) (.bits 16 0x4000) =
    out (.bits 16 0x4000) (.float .f32 1) := by cvt_eval
example : run (cv (f .f32) (f .f16) (sat := true)) (.bits 16 0xBC00) =
    out (.bits 16 0xBC00) (.float .f32 0) := by cvt_eval
example : run (cv (f .f32) (f .f16) (sat := true)) (.bits 16 0x8000) = .error .noRule := by
  cvt_eval
-- `cvt.f16.f16` and `cvt.f32.f32` copy the number (`0xC000` is -2.0).
example : run (cv (f .f16) (f .f16)) (.bits 16 0xC000) =
    out (.bits 16 0xC000) (.float .f16 (-2)) := by cvt_eval
-- `cvt.f16.f16` and `cvt.bf16.bf16` convert into no smaller range and keep an infinity of
-- either sign (`0x7C00`, `0xFC00` in `.f16`; `0x7F80`, `0xFF80` in `.bf16`).
example : run (cv (f .f16) (f .f16)) (.bits 16 0x7C00) =
    out (.bits 16 0x7C00) (.bits 16 0x7C00) := by cvt_eval
example : run (cv (f .f16) (f .f16)) (.bits 16 0xFC00) =
    out (.bits 16 0xFC00) (.bits 16 0xFC00) := by cvt_eval
example : run (cv (f .bf16) (f .bf16)) (.bits 16 0x7F80) =
    out (.bits 16 0x7F80) (.bits 16 0x7F80) := by cvt_eval
example : run (cv (f .bf16) (f .bf16)) (.bits 16 0xFF80) =
    out (.bits 16 0xFF80) (.bits 16 0xFF80) := by cvt_eval
-- Under `.sat` the clamp to [0.0, 1.0] decides the identity conversion of an infinity:
-- `cvt.sat.f16.f16` gives 1.0 for `+inf` and `+0` for `-inf`.
example : run (cv (f .f16) (f .f16) (sat := true)) (.bits 16 0x7C00) =
    out (.bits 16 0x7C00) (.float .f16 1) := by cvt_eval
example : run (cv (f .f16) (f .f16) (sat := true)) (.bits 16 0xFC00) =
    out (.bits 16 0xFC00) (.float .f16 0) := by cvt_eval
-- The special values of a conversion whose packed source has the destination type as its
-- element type: an infinity stays itself, as for `cvt.f16.f16`; from `.f32` it has no rule.
example : cvtSpecial (cv (x2 .f16) (x2 .f16)) .f16 (.binary 5 10 true .ieee)
    (fun _ => throw .noRule) (.inf true) = pure (.inf true) := by
  simp [cvtSpecial, cv, x2]
example : cvtSpecial (cv (x2 .f16) (f .f32)) .f16 (.binary 5 10 true .ieee)
    (fun _ => throw .noRule) (.inf true) = throw .noRule := by
  simp [cvtSpecial, cv, x2, f]
-- `cvt.f32.f16` without qualifiers widens exactly.
example : run (cv (f .f32) (f .f16)) (.bits 16 0x3C00) =
    out (.bits 16 0x3C00) (.float .f32 1) := by cvt_eval

/-! ## Integer rounding -/

-- `cvt.rni.f32.f32`: ties to even; a negative number rounded to zero gives `-0`.
example : run (cv (f .f32) (f .f32) (rnd := some .rni)) (.bits 32 0x40200000) =
    out (.bits 32 0x40200000) (.float .f32 2) := by cvt_eval
example : run (cv (f .f32) (f .f32) (rnd := some .rni)) (.bits 32 0x40600000) =
    out (.bits 32 0x40600000) (.float .f32 4) := by cvt_eval
example : run (cv (f .f32) (f .f32) (rnd := some .rzi)) (.bits 32 0xBE800000) =
    out (.bits 32 0xBE800000) (.bits 32 0x80000000) := by cvt_eval
-- `cvt.rni.s32.f32` of -2.5, `cvt.rzi.s32.f32` of about -2.7, `cvt.rmi.s32.f32` of about -2.2,
-- `cvt.rpi.s32.f32` of about 2.2.
example : run (cv (.int .s 32) (f .f32) (rnd := some .rni)) (.bits 32 0xC0200000) =
    out (.bits 32 0xC0200000) (.bits 32 0xFFFFFFFE) := by cvt_eval
example : run (cv (.int .s 32) (f .f32) (rnd := some .rzi)) (.bits 32 0xC02CCCCD) =
    out (.bits 32 0xC02CCCCD) (.bits 32 0xFFFFFFFE) := by cvt_eval
example : run (cv (.int .s 32) (f .f32) (rnd := some .rmi)) (.bits 32 0xC00CCCCD) =
    out (.bits 32 0xC00CCCCD) (.bits 32 0xFFFFFFFD) := by cvt_eval
example : run (cv (.int .s 32) (f .f32) (rnd := some .rpi)) (.bits 32 0x400CCCCD) =
    out (.bits 32 0x400CCCCD) (.bits 32 3) := by cvt_eval
-- The result is clamped to the destination range (`0x7B53` is the `.f16` 60000).
example : run (cv (.int .u 32) (f .f32) (rnd := some .rzi)) (.bits 32 0xC0A00000) =
    out (.bits 32 0xC0A00000) (.bits 32 0) := by cvt_eval
example : run (cv (.int .s 16) (f .f16) (rnd := some .rni)) (.bits 16 0x7B53) =
    out (.bits 16 0x7B53) (.bits 16 0x7FFF) := by cvt_eval
-- `.ftz` flushes an `.f32` subnormal input first: `.rpi` of 2^-149 is 1 without it, 0 with it.
example : run (cv (.int .s 32) (f .f32) (rnd := some .rpi)) (.bits 32 1) =
    out (.bits 32 1) (.bits 32 1) := by cvt_eval
example : run (cv (.int .s 32) (f .f32) (rnd := some .rpi) (ftz := true)) (.bits 32 1) =
    out (.bits 32 1) (.bits 32 0) := by cvt_eval

/-! ## Integer to floating -/

private theorem f32_m3 {x : ℝ} (hx : x = -3) :
    (Layout.binary 8 23 true .ieee).round .rn .inf x false = some (.fin (-3)) := by
  subst hx; rexact 0x40400000
private theorem f16_255 {x : ℝ} (hx : x = 255) :
    (Layout.binary 5 10 true .ieee).round .rz .inf x false = some (.fin 255) := by
  subst hx; rexact 0x5BF8
private theorem f32_7 {x : ℝ} (hx : x = 7) :
    (Layout.binary 8 23 true .ieee).round .rn .satfinite x false = some (.fin 7) := by
  subst hx; rexact 0x40E00000
example : run (cv (f .f32) (.int .s 16) (rnd := some .rn)) (.bits 16 0xFFFD) =
    out (.bits 16 0xFFFD) (.float .f32 (-3)) := by cvt_eval [f32_m3]
example : run (cv (f .f16) (.int .u 8) (rnd := some .rz)) (.bits 16 0xFF) =
    out (.bits 16 0xFF) (.float .f16 255) := by cvt_eval [f16_255]
example : run (cv (f .f32) (.int .u 16) (rnd := some .rn) (sat := true)) (.bits 16 7) =
    out (.bits 16 7) (.float .f32 1) := by cvt_eval [f32_7]

/-! ## Packed 8-bit elements -/

-- `cvt.rn.f16x2.e4m3x2`: the low byte `0x38` (1) to the low half, `0xB8` (-1) to the high half.
example : run (cv (x2 .f16) (x2 .e4m3) (rnd := some .rn)) (.bits 16 0xB838) =
    out (.bits 16 0xB838) (.pair (.float .f16 1) (.float .f16 (-1))) := by cvt_eval
-- `.relu` clamps the negative element to 0; `0x80` is `-0`, kept as a bit pattern.
example : run (cv (x2 .f16) (x2 .e4m3) (rnd := some .rn) (relu := true)) (.bits 16 0xB838) =
    out (.bits 16 0xB838) (.pair (.float .f16 1) (.float .f16 0)) := by cvt_eval
example : run (cv (x2 .bf16) (x2 .e4m3) (rnd := some .rn)) (.bits 16 0x8038) =
    out (.bits 16 0x8038) (.pair (.float .bf16 1) (.bits 16 0x8000)) := by cvt_eval
-- `e5m2`: `0x7C` is `+inf` and `0xFC` is `-inf`. An infinite element converted to `.f16` or
-- `.bf16` has no rule without `.satfinite`: §6.5.1 gives "~131,000" for `.f16`, which is no `.f16`
-- value, and names no `.bf16` value, and the model declines the infinity of IEEE 754 (§9.7.3).
-- Under `.satfinite` it gives the MAX_NORM of its sign (§9.7.10.24). The `e4m3` NaN `0x7F` widens
-- to the opaque NaN.
example : run (cv (x2 .f16) (x2 .e5m2) (rnd := some .rn)) (.bits 16 0x7C3C) = .error .noRule := by
  cvt_eval
example : run (cv (x2 .f16) (x2 .e5m2) (rnd := some .rn)) (.bits 16 0x3CFC) = .error .noRule := by
  cvt_eval
example : run (cv (x2 .bf16) (x2 .e5m2) (rnd := some .rn)) (.bits 16 0x7C3C) =
    .error .noRule := by cvt_eval
example : run (cv (x2 .bf16) (x2 .e5m2) (rnd := some .rn)) (.bits 16 0x3CFC) =
    .error .noRule := by cvt_eval
example : run { cv (x2 .f16) (x2 .e5m2) (rnd := some .rn) with satfinite := true }
    (.bits 16 0xFC7C) =
    out (.bits 16 0xFC7C) (.pair (.float .f16 65504) (.float .f16 (-65504))) := by cvt_eval
example : run { cv (x2 .bf16) (x2 .e5m2) (rnd := some .rn) with satfinite := true }
    (.bits 16 0xFC7C) =
    out (.bits 16 0xFC7C)
      (.pair (.float .bf16 (255 * 2 ^ 120)) (.float .bf16 (-(255 * 2 ^ 120)))) := by cvt_eval
example : run (cv (x2 .f16) (x2 .e4m3) (rnd := some .rn)) (.bits 16 0x7F38) =
    out (.bits 16 0x7F38) (.pair (.float .f16 1) (.nan .f16)) := by cvt_eval
-- `cvt.rn.bf16x2.ue8m0x2` (EXT-UE8M0): `0x7F` is 1, `0x80` is 2; `0xFF` is NaN, `0` has no rule.
example : run (cv (x2 .bf16) (x2 .ue8m0) (rnd := some .rn)) (.bits 16 0x807F) =
    out (.bits 16 0x807F) (.pair (.float .bf16 1) (.float .bf16 2)) := by cvt_eval
example : run (cv (x2 .bf16) (x2 .ue8m0) (rnd := some .rn)) (.bits 16 0xFF7F) =
    out (.bits 16 0xFF7F) (.pair (.float .bf16 1) (.nan .bf16)) := by cvt_eval
example : run (cv (x2 .bf16) (x2 .ue8m0) (rnd := some .rn)) (.bits 16 0x007F) =
    .error .noRule := by cvt_eval

/-! ## Conversions without a rule -/

-- `.tf32`, `.rs` to a four-element format, and `.s2f6x2` from `.bf16x2`.
example : CvtInstr.rule (cv (f .tf32) (f .f32) (rnd := some .rna)) = none := rfl
example : CvtInstr.rule {
    dst := .packed (.float .e2m1) 4, src := f .f32, rnd := some .rs, satfinite := true, d := 0,
    srcs := [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5] } = none := rfl
example : CvtInstr.rule {
    dst := x2 .s2f6, src := x2 .bf16, rnd := some .rn, satfinite := true, d := 0,
    srcs := [.reg 1] } = none := rfl
-- Rules exist for the forms above, and for the rounding conversions (Tests/Thread/CvtRound.lean).
example : CvtInstr.rule (cv (f .f32) (f .f16)) = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .f16, src := f .f32, rnd := some .rn, d := 0, srcs := [.reg 1, .reg 2] } =
    some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f16) (f .f32) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f32) (.int .s 32) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f16) (.int .u 16) (rnd := some .rn)) = some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .bf16, src := f .f32, rnd := some .rs, d := 0, srcs := [.reg 1, .reg 2, .reg 3] } =
    some .threadCvt := rfl
example : CvtInstr.rule {
    dst := x2 .bf16, src := x2 .e4m3, rnd := some .rn, scaled := true, d := 0,
    srcs := [.reg 1, .reg 2] } = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f32) (f .bf16)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (f .f32) (f .f16) (ftz := true)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (.int .s 32) (f .f32) (rnd := some .rni)) = some .threadCvt := rfl
example : CvtInstr.rule (cv (x2 .bf16) (x2 .ue8m0) (rnd := some .rn)) = some .threadCvt := rfl

/-! ## Decoding -/

example : Decode.op env "cvt.rn.bf16x2.e4m3x2" [r "%r0", r "%rs1"] =
    .ok (.cvt { dst := x2 .bf16, src := x2 .e4m3, rnd := some .rn, d := 0, srcs := [.reg 7] }) :=
  rfl
example : Decode.op env "cvt.rzi.s32.f32" [r "%r0", r "%r1"] =
    .ok (.cvt { dst := .int .s 32, src := f .f32, rnd := some .rzi, d := 0, srcs := [.reg 1] }) :=
  rfl
-- An integer destination of a floating source may be a wider register.
example : Decode.op env "cvt.rzi.s16.f32" [r "%r0", r "%r1"] =
    .ok (.cvt {
      dst := .int .s 16, src := f .f32, rnd := some .rzi, d := 0, ext := .sign 32,
      srcs := [.reg 1] }) := rfl

end
end PTX.Tests.CvtFloat
