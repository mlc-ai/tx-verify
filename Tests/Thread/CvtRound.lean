-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Core.Thread.Local

/-! Conversions of THREAD-CVT that round (§9.7.10.24, THREAD-FLOAT-ROUND): narrowing between `.f64`,
`.f32`, `.f16` and `.bf16`, integer-to-floating conversions, the packed `.f16x2`, `.bf16x2`,
8-, 6- and 4-bit, `.ue8m0x2`, `.ue5m3x2` and `.s2f6x2` destinations, scale factors, `.rs` with
chosen random bits, NaN and infinity inputs, `.sat`, `.satfinite`, `.relu`, `.pzo` and `.ftz`,
and the conversions without a rule. Inputs are bit patterns; each rounding instance is proved
from the characterization lemmas of THREAD-FLOAT-ROUND. -/
namespace PTX.Tests.CvtRound
noncomputable section

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def f (t : FType) : DType := .float t
private def x2 (t : FType) : DType := .packed (.float t) 2

/-- The state whose registers `1`, `2`, … hold `vs`. -/
private def st (vs : List Value) : TState :=
  (vs.zipIdx 1).foldl (fun t p => setReg t p.2 p.1) {}

/-- The outcome in which register 0 receives `w` after the registers held `vs`. -/
private def out (vs : List Value) (w : Value) : Exec TState := .ok (next (setReg (st vs) 0 w))

/-- A conversion with destination register 0 and the sources `1`, …, `n`. -/
private def cv (dst src : DType) (rnd : Option CvtRnd) (n : Nat := 1)
    (ftz sat relu satfinite pzo scaled : Bool := false) : CvtInstr :=
  { dst, src, rnd, ftz, sat, relu, satfinite, pzo, scaled, d := 0,
    srcs := (List.range n).map fun i => .reg (i + 1) }

/-- Run conversion `c` on the state whose registers `1`, `2`, … hold `vs`. -/
private def run (c : CvtInstr) (vs : List Value) : Exec TState :=
  execLocal launch 0 (st vs) (.cvt c)

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
      simp only [st, List.zipIdx, List.zipIdx_cons, List.range, List.range.loop, List.map,
        List.foldl]
      dsimp only [execCvt, FType.fmt?]
      norm_num [readCvtFloat, lowValue, lowBitsValue, readReg, readValue, readBits, setReg,
        Function.update_self, Function.update_of_ne, classify, Value.bitPattern, Value.bytes,
        FloatFmt.bytes, FloatFmt.layout, FType.layout?, Layout.decode, Layout.width,
        Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal,
        Layout.minNormal, Layout.maxNorm, Layout.topField, FVal.toValue, Layout.signPattern,
        Layout.infPattern, cvtFloatDst, CvtRnd.roundInt, CvtRnd.mode?, cvtIntOf, FVal.sat, reluFVal,
        pzoFVal, cvtFinish, widenElem, roundIntElem, cvtElem, packedElems, splitValue, FType.fmt?,
        cvtScales, ue8m0Scale, cvtPack, cvtSpecial, cvtNum, cvtRound, satMaxNorm, scaledFlush,
        rsModes,
        FVal.ofRat, truncBits, intOf, toSigned, intSat, intBits, bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw, Int.floor_eq_iff, Int.ceil_eq_iff,
        $ls,*]
      try rfl))

/-- The simp set that evaluates the hypotheses of the rounding lemmas of THREAD-FLOAT-ROUND. -/
macro "rnum" : tactic => `(tactic| norm_num [RoundMode.applies, RoundMode.away, Layout.topField,
  Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.maxNorm, abs_of_pos, abs_of_neg])

/-- `round` of a value of a binary layout, the field `F`. -/
macro "rexact" F:term : tactic => `(tactic| (rw [Layout.round_exact (F := $F)] <;> rnum))
/-- `round` of a number between the fields `F` and `F + 1`. -/
macro "rbetween" F:term : tactic => `(tactic| (rw [Layout.round_between (F := $F)] <;> rnum))
/-- `round` of a number above MAX_NORM under `.satfinite`. -/
macro "rsat" : tactic => `(tactic| (rw [Layout.round_satfinite] <;> rnum))
/-- `round` of a number above MAX_NORM with IEEE overflow. -/
macro "rinf" : tactic => `(tactic| (rw [Layout.round_inf_ieee] <;> rnum))
/-- `Layout.encode` of a datum by the pattern that decodes to it. -/
macro "renc" : tactic => `(tactic| exact Layout.encode_decode (by norm_num [Layout.width])
  (by norm_num [Layout.decode, Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias]))

/-! ## Narrowing between `.f64`, `.f32`, `.f16` and `.bf16` -/

private theorem f16_one {x : ℝ} {ov : Overflow} (hx : x = 1) :
    (Layout.binary 5 10 true .ieee).round .rn ov x false =
    some (.fin 1) := by subst hx; rexact 0x3C00
-- `cvt.rn.f16.f32` of 1.0 is exact.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0x3F800000] =
    out [.bits 32 0x3F800000] (.float .f16 1) := by cvt_eval [f16_one]

-- `1 + 2^-11` lies at the midpoint of the `.f16` values 1 and `1 + 2^-10`.
private theorem f16_tie_rn {x : ℝ} (hx : x = (1 + 1 / 2048)) :
    (Layout.binary 5 10 true .ieee).round .rn .inf x false =
    some (.fin 1) := by subst hx; rbetween 0x3C00
private theorem f16_tie_rp {x : ℝ} (hx : x = (1 + 1 / 2048)) :
    (Layout.binary 5 10 true .ieee).round .rp .inf x false =
    some (.fin (1 + 1 / 1024)) := by subst hx; rbetween 0x3C00
private theorem f16_tie_rm {x : ℝ} (hx : x = (-(1 + 1 / 2048))) :
    (Layout.binary 5 10 true .ieee).round .rm .inf x false =
      some (.fin (-(1 + 1 / 1024))) := by
  subst hx; rbetween 0x3C00
private theorem f16_tie_rz {x : ℝ} (hx : x = (-(1 + 1 / 2048))) :
    (Layout.binary 5 10 true .ieee).round .rz .inf x false =
      some (.fin (-1)) := by
  subst hx; rbetween 0x3C00
-- `.rn` ties to the even mantissa, `.rp` rounds up, `.rm` and `.rz` on the negative number.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0x3F801000] =
    out [.bits 32 0x3F801000] (.float .f16 1) := by cvt_eval [f16_tie_rn]
example : run (cv (f .f16) (f .f32) (some .rp)) [.bits 32 0x3F801000] =
    out [.bits 32 0x3F801000] (.float .f16 (1 + 1 / 1024)) := by cvt_eval [f16_tie_rp]
example : run (cv (f .f16) (f .f32) (some .rm)) [.bits 32 0xBF801000] =
    out [.bits 32 0xBF801000] (.float .f16 (-(1 + 1 / 1024))) := by cvt_eval [f16_tie_rm]
example : run (cv (f .f16) (f .f32) (some .rz)) [.bits 32 0xBF801000] =
    out [.bits 32 0xBF801000] (.float .f16 (-1)) := by cvt_eval [f16_tie_rz]

/-! ## Overflow to `.f16` and `.bf16` (§6.5.1) -/

private theorem f16_big_rn {x : ℝ} (hx : x = 70000) :
    (Layout.binary 5 10 true .ieee).round .rn .inf x false = some (.inf false) := by
  subst hx; rinf
private theorem f16_big_sat {x : ℝ} (hx : x = 70000) :
    (Layout.binary 5 10 true .ieee).round .rn .satfinite x false = some (.fin 65504) := by
  subst hx; rsat
private theorem f16_big_rz_sat {x : ℝ} (hx : x = 70000) :
    (Layout.binary 5 10 true .ieee).round .rz .satfinite x false = some (.fin 65504) := by
  subst hx; rsat
private theorem f16_negbig_sat {x : ℝ} (hx : x = -70000) :
    (Layout.binary 5 10 true .ieee).round .rn .satfinite x false = some (.fin (-65504)) := by
  subst hx; rsat
-- `cvt.rn.f16.f32` of 70000.0 overflows `.f16`, which §6.5.1 leaves open: no rule.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0x4788B800] = .error .noRule := by
  cvt_eval [f16_big_rn]
-- `cvt.rn.sat.f16.f32` of 70000.0 is 1.0 (`0x3c00`): the clamp decides the overflow.
example : run (cv (f .f16) (f .f32) (some .rn) (sat := true)) [.bits 32 0x4788B800] =
    out [.bits 32 0x4788B800] (.float .f16 1) := by cvt_eval [f16_big_sat]
-- `.satfinite` gives the sign-preserved MAX_NORM 65504.
example : run (cv (f .f16) (f .f32) (some .rz) (satfinite := true)) [.bits 32 0x4788B800] =
    out [.bits 32 0x4788B800] (.float .f16 65504) := by cvt_eval [f16_big_rz_sat]
example : run (cv (f .f16) (f .f32) (some .rn) (satfinite := true)) [.bits 32 0xC788B800] =
    out [.bits 32 0xC788B800] (.float .f16 (-65504)) := by cvt_eval [f16_negbig_sat]

-- `0x7F7FC99E` is about 3.4e38, above the `.bf16` MAX_NORM `255 * 2^120` (`0x7f7f`).
private theorem bf16_big_rz {x : ℝ} (hx : x = 16763294 * 2 ^ 104) :
    (Layout.binary 8 7 true .ieee).round .rz .inf x false = some (.fin (255 * 2 ^ 120)) := by
  subst hx; rinf
private theorem bf16_big_rn {x : ℝ} (hx : x = 16763294 * 2 ^ 104) :
    (Layout.binary 8 7 true .ieee).round .rn .inf x false = some (.inf false) := by
  subst hx; rinf
-- `cvt.rz.bf16.f32` gives MAX_NORM, which is also §6.5.1's maximum value.
example : run (cv (f .bf16) (f .f32) (some .rz)) [.bits 32 0x7F7FC99E] =
    out [.bits 32 0x7F7FC99E] (.float .bf16 (255 * 2 ^ 120)) := by cvt_eval [bf16_big_rz]
-- `cvt.rn.bf16.f32` is above the `.rn` threshold `MAX_NORM + 2^119`: IEEE 754 gives infinity,
-- for which §6.5.1 names no `.bf16` value: no rule.
example : run (cv (f .bf16) (f .f32) (some .rn)) [.bits 32 0x7F7FC99E] = .error .noRule := by
  cvt_eval [bf16_big_rn]

/-! ## NaN and infinity inputs -/

-- A NaN gives the opaque NaN, `+0` under `.sat`, and NaN under `.satfinite` and `.relu`.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.nan .f16) := by cvt_eval
example : run (cv (f .f16) (f .f32) (some .rn) (sat := true)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.float .f16 0) := by cvt_eval
example : run (cv (f .f16) (f .f32) (some .rn) (satfinite := true)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.nan .f16) := by cvt_eval
example : run (cv (f .bf16) (f .f32) (some .rn) (relu := true)) [.bits 32 0xFFC00000] =
    out [.bits 32 0xFFC00000] (.nan .bf16) := by cvt_eval
-- An infinity converted to `.f16` or `.bf16` without `.satfinite` or `.sat` has no rule, since
-- §6.5.1 gives no `.f16` or `.bf16` value beyond the range; under `.relu` too. It is MAX_NORM
-- under `.satfinite`, and `.sat` clamps it. An `.f64` infinity narrowed to `.f32` stays itself.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0x7F800000] = .error .noRule := by
  cvt_eval
example : run (cv (f .bf16) (f .f32) (some .rn)) [.bits 32 0xFF800000] = .error .noRule := by
  cvt_eval
example : run (cv (f .f16) (f .f32) (some .rn) (relu := true)) [.bits 32 0xFF800000] =
    .error .noRule := by cvt_eval
example : run (cv (f .f16) (f .f32) (some .rn) (satfinite := true)) [.bits 32 0xFF800000] =
    out [.bits 32 0xFF800000] (.float .f16 (-65504)) := by cvt_eval
example : run (cv (f .bf16) (f .f32) (some .rn) (satfinite := true)) [.bits 32 0x7F800000] =
    out [.bits 32 0x7F800000] (.float .bf16 (255 * 2 ^ 120)) := by cvt_eval
example : run (cv (f .f16) (f .f32) (some .rn) (sat := true)) [.bits 32 0x7F800000] =
    out [.bits 32 0x7F800000] (.float .f16 1) := by cvt_eval
example : run (cv (f .f32) (f .f64) (some .rn)) [.bits 64 0xFFF0000000000000] =
    out [.bits 64 0xFFF0000000000000] (.bits 32 0xFF800000) := by cvt_eval

/-! ## `.relu`, `.pzo` and `.ftz` -/

private theorem f16_negone {x : ℝ} {ov : Overflow} (hx : x = -1) :
    (Layout.binary 5 10 true .ieee).round .rn ov x false = some (.fin (-1)) := by
  subst hx; rexact 0x3C00
-- `-2^-30` rounds to `-0` in `.f16`.
private theorem f16_tiny {x : ℝ} (hx : x = -(1 / 1073741824)) :
    (Layout.binary 5 10 true .ieee).round .rn .inf x false = some (.zero true) := by
  subst hx; rbetween 0
example : run (cv (f .f16) (f .f32) (some .rn) (relu := true)) [.bits 32 0xBF800000] =
    out [.bits 32 0xBF800000] (.float .f16 0) := by cvt_eval [f16_negone]
-- A negative number that rounds to zero keeps its sign; under `.relu` that `-0` has no rule,
-- and `.pzo` makes it `+0`.
example : run (cv (f .f16) (f .f32) (some .rn)) [.bits 32 0xB0800000] =
    out [.bits 32 0xB0800000] (.bits 16 0x8000) := by cvt_eval [f16_tiny]
example : run (cv (f .f16) (f .f32) (some .rn) (relu := true)) [.bits 32 0xB0800000] =
    .error .noRule := by cvt_eval [f16_tiny]
example : run (cv (f .f16) (f .f32) (some .rn) (pzo := true)) [.bits 32 0xB0800000] =
    out [.bits 32 0xB0800000] (.float .f16 0) := by cvt_eval [f16_tiny]
example : run (cv (f .f16) (f .f32) (some .rn) (relu := true) (pzo := true))
    [.bits 32 0xB0800000] = out [.bits 32 0xB0800000] (.float .f16 0) := by cvt_eval [f16_tiny]

-- `cvt.rn.ftz.f32.f64`: `2^-130` is an `.f32` subnormal and is flushed to `+0`; a number just
-- below `2^-126` that rounds up to it has no rule.
private theorem f32_sub {x : ℝ} (hx : x = 1 / 2 ^ 130) :
    (Layout.binary 8 23 true .ieee).round .rn .inf x false = some (.fin (1 / 2 ^ 130)) := by
  subst hx; rexact 0x80000
private theorem f32_band {x : ℝ} (hx : x = 2 ^ 30 * (1 - 1 / 2 ^ 30) / 2 ^ 156) :
    (Layout.binary 8 23 true .ieee).round .rn .inf x false = some (.fin (1 / 2 ^ 126)) := by
  subst hx; rbetween 0x7FFFFF
example : run (cv (f .f32) (f .f64) (some .rn) (ftz := true)) [.bits 64 0x37D0000000000000] =
    out [.bits 64 0x37D0000000000000] (.float .f32 0) := by cvt_eval [f32_sub]
example : run (cv (f .f32) (f .f64) (some .rn)) [.bits 64 0x37D0000000000000] =
    out [.bits 64 0x37D0000000000000] (.float .f32 (1 / 2 ^ 130)) := by cvt_eval [f32_sub]
example : run (cv (f .f32) (f .f64) (some .rn) (ftz := true)) [.bits 64 0x380FFFFFFF800000] =
    .error .noRule := by cvt_eval [f32_band]

/-! ## Integer to floating -/

-- `cvt.rn.f32.s32` of `2^24 + 1` is a tie between `2^24` (even) and `2^24 + 2`.
private theorem f32_int_rn {x : ℝ} (hx : x = 16777217) :
    (Layout.binary 8 23 true .ieee).round .rn .inf x false = some (.fin 16777216) := by
  subst hx; rbetween 0x4B800000
private theorem f32_int_rp {x : ℝ} (hx : x = 16777217) :
    (Layout.binary 8 23 true .ieee).round .rp .inf x false = some (.fin 16777218) := by
  subst hx; rbetween 0x4B800000
private theorem f16_int_big {x : ℝ} (hx : x = 70000) :
    (Layout.binary 5 10 true .ieee).round .rz .inf x false = some (.fin 65504) := by
  subst hx; rinf
private theorem f16_255 {x : ℝ} (hx : x = 255) :
    (Layout.binary 5 10 true .ieee).round .rz .inf x false = some (.fin 255) := by
  subst hx; rexact 0x5BF8
example : run (cv (f .f32) (.int .s 32) (some .rn)) [.bits 32 0x1000001] =
    out [.bits 32 0x1000001] (.float .f32 16777216) := by cvt_eval [f32_int_rn]
example : run (cv (f .f32) (.int .s 32) (some .rp)) [.bits 32 0x1000001] =
    out [.bits 32 0x1000001] (.float .f32 16777218) := by cvt_eval [f32_int_rp]
-- `cvt.rz.f16.u32` of 70000: IEEE 754 gives MAX_NORM, §6.5.1 "~131,000": no rule.
example : run (cv (f .f16) (.int .u 32) (some .rz)) [.bits 32 70000] = .error .noRule := by
  cvt_eval [f16_int_big]
example : run (cv (f .f16) (.int .u 8) (some .rz)) [.bits 16 0xFF] =
    out [.bits 16 0xFF] (.float .f16 255) := by cvt_eval [f16_255]
-- Zero is `+0`.
example : run (cv (f .f32) (.int .s 32) (some .rm)) [.bits 32 0] =
    out [.bits 32 0] (.float .f32 0) := by cvt_eval

/-! ## Floating to integer: NaN and infinity -/

-- NaN is zero unless the source is `.f64` or the destination has 64 bits, then `1 << (w - 1)`.
example : run (cv (.int .s 32) (f .f32) (some .rni)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.bits 32 0) := by cvt_eval
example : run (cv (.int .u 32) (f .f64) (some .rzi)) [.bits 64 0x7FF8000000000000] =
    out [.bits 64 0x7FF8000000000000] (.bits 32 0x80000000) := by cvt_eval
example : run (cv (.int .u 64) (f .f16) (some .rni)) [.bits 16 0x7E00] =
    out [.bits 16 0x7E00] (.bits 64 0x8000000000000000) := by cvt_eval
-- An infinity is clamped to the destination range.
example : run (cv (.int .s 32) (f .f32) (some .rni)) [.bits 32 0x7F800000] =
    out [.bits 32 0x7F800000] (.bits 32 0x7FFFFFFF) := by cvt_eval
example : run (cv (.int .s 16) (f .f32) (some .rmi)) [.bits 32 0xFF800000] =
    out [.bits 32 0xFF800000] (.bits 16 0x8000) := by cvt_eval
example : run (cv (.int .u 32) (f .f32) (some .rpi)) [.bits 32 0xFF800000] =
    out [.bits 32 0xFF800000] (.bits 32 0) := by cvt_eval

/-! ## Integral rounding and widening: NaN and infinity -/

example : run (cv (f .f32) (f .f32) (some .rni)) [.bits 32 0xFF800000] =
    out [.bits 32 0xFF800000] (.bits 32 0xFF800000) := by cvt_eval
example : run (cv (f .f32) (f .f32) (some .rni)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.nan .f32) := by cvt_eval
example : run (cv (f .f32) (f .f32) (some .rni) (sat := true)) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.float .f32 0) := by cvt_eval
example : run (cv (f .f32) (f .f16) none) [.bits 16 0x7C00] =
    out [.bits 16 0x7C00] (.bits 32 0x7F800000) := by cvt_eval
example : run (cv (f .f64) (f .f32) none) [.bits 32 0x7FC00000] =
    out [.bits 32 0x7FC00000] (.nan .f64) := by cvt_eval
example : run (cv (f .f32) (f .f16) none (sat := true)) [.bits 16 0x7C00] =
    out [.bits 16 0x7C00] (.float .f32 1) := by cvt_eval

/-! ## `.f16x2` and `.bf16x2` from two `.f32` sources -/

private theorem f16_two {x : ℝ} {ov : Overflow} (hx : x = 2) :
    (Layout.binary 5 10 true .ieee).round .rn ov x false = some (.fin 2) := by
  subst hx; rexact 0x4000
-- "d[31:16] = convert(a); d[15:0] = convert(b);": `a` = 1.0 is the upper element.
example : run (cv (x2 .f16) (f .f32) (some .rn) 2) [.bits 32 0x3F800000, .bits 32 0x40000000] =
    out [.bits 32 0x3F800000, .bits 32 0x40000000] (.pair (.float .f16 2) (.float .f16 1)) := by
  cvt_eval [f16_one, f16_two]
-- `.relu` and `.satfinite`: -1.0 is clamped to `+0` and 70000.0 saturates.
example : run (cv (x2 .f16) (f .f32) (some .rn) 2 (relu := true) (satfinite := true))
    [.bits 32 0xBF800000, .bits 32 0x4788B800] =
    out [.bits 32 0xBF800000, .bits 32 0x4788B800] (.pair (.float .f16 65504) (.float .f16 0)) := by
  cvt_eval [f16_negone, f16_big_sat]
-- Without `.satfinite` the overflow has no rule.
example : run (cv (x2 .f16) (f .f32) (some .rn) 2) [.bits 32 0x4788B800, .bits 32 0x3F800000] =
    .error .noRule := by cvt_eval [f16_big_rn, f16_one]

/-! ## Packed narrow formats from two `.f32` sources (`.satfinite`) -/

private theorem e4m3_one {x : ℝ} {ov : Overflow} (hx : x = 1) :
    (Layout.binary 4 3 true .e4m3).round .rn ov x false = some (.fin 1) := by
  subst hx; rexact 56
private theorem e4m3_mhalf {x : ℝ} {ov : Overflow} (hx : x = -(1 / 2)) :
    (Layout.binary 4 3 true .e4m3).round .rn ov x false = some (.fin (-(1 / 2))) := by
  subst hx; rexact 48
private theorem e4m3_big {x : ℝ} (hx : x = 1000) :
    (Layout.binary 4 3 true .e4m3).round .rn .satfinite x false = some (.fin 448) := by
  subst hx; rsat
-- `cvt.rn.satfinite.e4m3x2.f32 d, a, b`: `a` in the upper byte; 1000.0 saturates to 448; NaN is
-- an `.e4m3` NaN.
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x3F800000, .bits 32 0xBF000000] =
    out [.bits 32 0x3F800000, .bits 32 0xBF000000]
      (.pair (.float .e4m3 (-(1 / 2))) (.float .e4m3 1)) := by cvt_eval [e4m3_one, e4m3_mhalf]
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x447A0000, .bits 32 0x7FC00000] =
    out [.bits 32 0x447A0000, .bits 32 0x7FC00000] (.pair (.nan .e4m3) (.float .e4m3 448)) := by
  cvt_eval [e4m3_big]

private theorem e2m1_one {x : ℝ} {ov : Overflow} (hx : x = 1) :
    (Layout.binary 2 1 true .none).round .rn ov x false = some (.fin 1) := by
  subst hx; rexact 2
private theorem e2m1_msix {x : ℝ} {ov : Overflow} (hx : x = -6) :
    (Layout.binary 2 1 true .none).round .rn ov x false = some (.fin (-6)) := by
  subst hx; rexact 7
private theorem e2m1_big {x : ℝ} (hx : x = 100) :
    (Layout.binary 2 1 true .none).round .rn .satfinite x false = some (.fin 6) := by
  subst hx; rsat
private theorem enc_e2m1_one {q : ℚ} (hq : q = 1) : (Layout.binary 2 1 true .none).encode (.fin q) =
    some 2 := by subst hq; renc
private theorem enc_e2m1_msix {q : ℚ} (hq : q = -6) :
    (Layout.binary 2 1 true .none).encode (.fin q) = some 15 := by subst hq; renc
private theorem enc_e2m1_six {q : ℚ} (hq : q = 6) :
    (Layout.binary 2 1 true .none).encode (.fin q) = some 7 := by subst hq; renc
-- `.e2m1x2` is a `.b8` value, `a` in the upper four bits: 1.0 is `0x2` and -6.0 is `0xf`.
example : run (cv (x2 .e2m1) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x3F800000, .bits 32 0xC0C00000] =
    out [.bits 32 0x3F800000, .bits 32 0xC0C00000] (.bits 8 0x2F) := by
  cvt_eval [e2m1_one, e2m1_msix, enc_e2m1_one, enc_e2m1_msix]
-- A NaN gives the positive MAX_NORM `0x7`, and 100.0 saturates to 6.0 (`0x7`).
example : run (cv (x2 .e2m1) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x7FC00000, .bits 32 0x42C80000] =
    out [.bits 32 0x7FC00000, .bits 32 0x42C80000] (.bits 8 0x77) := by
  cvt_eval [e2m1_big, enc_e2m1_six]

private theorem e2m3_max {x : ℝ} {ov : Overflow} (hx : x = 15 / 2) :
    (Layout.binary 2 3 true .none).round .rn ov x false = some (.fin (15 / 2)) := by
  subst hx; rexact 31
private theorem e2m3_sub {x : ℝ} {ov : Overflow} (hx : x = 7 / 8) :
    (Layout.binary 2 3 true .none).round .rn ov x false = some (.fin (7 / 8)) := by
  subst hx; rexact 7
private theorem enc_e2m3_max {q : ℚ} (hq : q = 15 / 2) :
    (Layout.binary 2 3 true .none).encode (.fin q) = some 0x1F := by subst hq; renc
private theorem enc_e2m3_sub {q : ℚ} (hq : q = 7 / 8) :
    (Layout.binary 2 3 true .none).encode (.fin q) = some 7 := by subst hq; renc
-- `.e2m3x2`: 7.5 is `0x1f` and the subnormal 0.875 is `0x07`, each byte with two zero bits.
example : run (cv (x2 .e2m3) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x40F00000, .bits 32 0x3F600000] =
    out [.bits 32 0x40F00000, .bits 32 0x3F600000] (.bits 16 0x1F07) := by
  cvt_eval [e2m3_max, e2m3_sub, enc_e2m3_max, enc_e2m3_sub]

/-! ## `.s2f6x2` from two `.f32` sources -/

private theorem s2f6_val {x : ℝ} {k : Nat} {q : ℚ} (hk : |x| * 2 ^ 6 = k)
    (hx0 : x ≠ 0) (hm : |x| ≤ 127 / 64)
    (hv : Layout.fixedVal 6 k (decide (x < 0)) = .fin q) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin q) := by
  rw [Layout.round_fixed_exact (k := k) (by simp) hx0 hk
    (by rw [Layout.maxNorm_fixed]; norm_num; linarith [hm]), hv]
private theorem s2f6_mhalf {x : ℝ} (hx : x = -(1 / 2)) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin (-(1 / 2))) := by
  subst hx; exact s2f6_val (k := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Layout.fixedVal])
private theorem s2f6_half {x : ℝ} (hx : x = 1 / 2) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin (1 / 2)) := by
  subst hx; exact s2f6_val (k := 32) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Layout.fixedVal])
private theorem s2f6_neg_max {x : ℝ} (hx : x = -(127 / 64)) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin (-(127 / 64))) := by
  subst hx; exact s2f6_val (k := 127) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Layout.fixedVal])
private theorem s2f6_big {x : ℝ} (hx : x = 3) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin (127 / 64)) := by
  subst hx; rw [Layout.round_fixed_over (by simp) (by rw [Layout.maxNorm_fixed]; norm_num)]
  norm_num [Layout.maxNorm_fixed]
private theorem s2f6_mtwo {x : ℝ} (hx : x = -2) :
    (Layout.fixed 8 6).round .rn .satfinite x false = none := by
  subst hx; exact Layout.round_fixed_under (by rw [Layout.maxNorm_fixed]; norm_num)
private theorem enc_s2f6_mhalf {q : ℚ} (hq : q = -(1 / 2)) :
    (Layout.fixed 8 6).encode (.fin q) = some 0xE0 := by subst hq; renc
private theorem enc_s2f6_half {q : ℚ} (hq : q = 1 / 2) :
    (Layout.fixed 8 6).encode (.fin q) = some 0x20 := by subst hq; renc
private theorem enc_s2f6_max {q : ℚ} (hq : q = 127 / 64) :
    (Layout.fixed 8 6).encode (.fin q) = some 0x7F := by subst hq; renc
private theorem enc_s2f6_nmax {q : ℚ} (hq : q = -(127 / 64)) :
    (Layout.fixed 8 6).encode (.fin q) = some 0x81 := by subst hq; renc
-- `cvt.rn.satfinite.s2f6x2.f32 d, -0.5, 0.5` is `0xe020`.
example : run (cv (x2 .s2f6) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0xBF000000, .bits 32 0x3F000000] =
    out [.bits 32 0xBF000000, .bits 32 0x3F000000] (.bits 16 0xE020) := by
  cvt_eval [s2f6_mhalf, s2f6_half, enc_s2f6_mhalf, enc_s2f6_half]
-- 3.0 saturates to `0x7f`, -1.984375 is `0x81`, and NaN gives the positive MAX_NORM `0x7f`.
example : run (cv (x2 .s2f6) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x40400000, .bits 32 0xBFFE0000] =
    out [.bits 32 0x40400000, .bits 32 0xBFFE0000] (.bits 16 0x7F81) := by
  cvt_eval [s2f6_big, s2f6_neg_max, enc_s2f6_max, enc_s2f6_nmax]
example : run (cv (x2 .s2f6) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x7FC00000, .bits 32 0x3F000000] =
    out [.bits 32 0x7FC00000, .bits 32 0x3F000000] (.bits 16 0x7F20) := by
  cvt_eval [s2f6_half, enc_s2f6_max, enc_s2f6_half]
-- -2.0 is above MAX_NORM in magnitude, where "sign-preserved MAX_NORM" can be read as
-- `-1.984375` or as `-2.0`: no rule.
example : run (cv (x2 .s2f6) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0xC0000000, .bits 32 0x3F000000] = .error .noRule := by
  cvt_eval [s2f6_mtwo, s2f6_half]

/-! ## `.ue8m0x2` and `.ue5m3x2` -/

private theorem ue8m0_one {x : ℝ} {m : RoundMode} {ov : Overflow} (hm : ∀ k r, m ≠ .rs k r)
    (hx : x = 1) : (Layout.binary 8 0 false .ue8m0).round m ov x false = some (.fin 1) := by
  subst hx; cases m <;> first | exact absurd rfl (hm _ _) | rexact 127
private theorem enc_ue8m0_one {q : ℚ} (hq : q = 1) :
    (Layout.binary 8 0 false .ue8m0).encode (.fin q) = some 0x7F := by subst hq; renc
private theorem enc_ue8m0_max {q : ℚ} (hq : q = 2 ^ 127) :
    (Layout.binary 8 0 false .ue8m0).encode (.fin q) = some 0xFE := by subst hq; renc
private theorem enc_ue8m0_99 {q : ℚ} (hq : q = 2 ^ 99) :
    (Layout.binary 8 0 false .ue8m0).encode (.fin q) = some 0xE2 := by subst hq; renc
-- `0x7F61B1E6` is about 3.0e38 (`14791142 * 2^104`), above `2^127`, the largest `.ue8m0` value.
private theorem ue8m0_negbig {x : ℝ} (hx : x = -(14791142 * 2 ^ 104)) :
    (Layout.binary 8 0 false .ue8m0).round .rz .satfinite x false = some (.fin (2 ^ 127)) := by
  subst hx; rsat
private theorem ue8m0_big {x : ℝ} (hx : x = 14791142 * 2 ^ 104) :
    (Layout.binary 8 0 false .ue8m0).round .rz .inf x false = none := by
  subst hx; rw [Layout.round_inf_none] <;> rnum
-- `0x7149F2CA` is about 1e30 (`13234890 * 2^76`), between `2^99` and `2^100`.
private theorem ue8m0_e30 {x : ℝ} (hx : x = 13234890 * 2 ^ 76) :
    (Layout.binary 8 0 false .ue8m0).round .rz .inf x false = some (.fin (2 ^ 99)) := by
  subst hx; rbetween 226
private theorem ue8m0_nege30 {x : ℝ} (hx : x = -(13234890 * 2 ^ 76)) :
    (Layout.binary 8 0 false .ue8m0).round .rz .satfinite x false = none := by
  subst hx; rw [Layout.round_unsigned_below] <;> rnum
-- `cvt.rz.satfinite.ue8m0x2.f32 d, -3.0e38, 1.0` is `0xfe7f`: the positive MAX_NORM.
example : run (cv (x2 .ue8m0) (f .f32) (some .rz) 2 (satfinite := true))
    [.bits 32 0xFF61B1E6, .bits 32 0x3F800000] =
    out [.bits 32 0xFF61B1E6, .bits 32 0x3F800000] (.bits 16 0xFE7F) := by
  cvt_eval [ue8m0_negbig, ue8m0_one, enc_ue8m0_one, enc_ue8m0_max]
-- `cvt.rz.ue8m0x2.f32 d, 3.0e38, 1.0`: overflow without `.satfinite` has no rule.
example : run (cv (x2 .ue8m0) (f .f32) (some .rz) 2) [.bits 32 0x7F61B1E6, .bits 32 0x3F800000] =
    .error .noRule := by cvt_eval [ue8m0_big, ue8m0_one]
-- `cvt.rz.ue8m0x2.f32 d, 1e30, 1.0` is `0xe27f`.
example : run (cv (x2 .ue8m0) (f .f32) (some .rz) 2) [.bits 32 0x7149F2CA, .bits 32 0x3F800000] =
    out [.bits 32 0x7149F2CA, .bits 32 0x3F800000] (.bits 16 0xE27F) := by
  cvt_eval [ue8m0_e30, ue8m0_one, enc_ue8m0_one, enc_ue8m0_99]
-- `cvt.rz.satfinite.ue8m0x2.f32 d, -1e30, 1.0`: a negative input in range has no rule.
example : run (cv (x2 .ue8m0) (f .f32) (some .rz) 2 (satfinite := true))
    [.bits 32 0xF149F2CA, .bits 32 0x3F800000] = .error .noRule := by
  cvt_eval [ue8m0_nege30, ue8m0_one]
-- NaN under `.satfinite` is `0xff`; without it, and for a zero input, there is no rule.
example : run (cv (x2 .ue8m0) (f .f32) (some .rp) 2 (satfinite := true))
    [.bits 32 0x7FC00000, .bits 32 0x3F800000] =
    out [.bits 32 0x7FC00000, .bits 32 0x3F800000] (.bits 16 0xFF7F) := by
  cvt_eval [ue8m0_one, enc_ue8m0_one]
example : run (cv (x2 .ue8m0) (f .f32) (some .rp) 2) [.bits 32 0x7FC00000, .bits 32 0x3F800000] =
    .error .noRule := by cvt_eval [ue8m0_one]
example : run (cv (x2 .ue8m0) (f .f32) (some .rp) 2 (satfinite := true))
    [.bits 32 0, .bits 32 0x3F800000] = .error .noRule := by cvt_eval [ue8m0_one]

private theorem ue5m3_one {x : ℝ} {ov : Overflow} (hx : x = 1) :
    (Layout.binary 5 3 false .allOnesNaN).round .rn ov x false = some (.fin 1) := by
  subst hx; rexact 0x78
private theorem enc_ue5m3_one {q : ℚ} (hq : q = 1) :
    (Layout.binary 5 3 false .allOnesNaN).encode (.fin q) = some 0x78 := by subst hq; renc
-- `cvt.rn.satfinite.ue5m3x2.f32`: 1.0 is `0x78`, NaN is `0xff`.
example : run (cv (x2 .ue5m3) (f .f32) (some .rn) 2 (satfinite := true))
    [.bits 32 0x7FC00000, .bits 32 0x3F800000] =
    out [.bits 32 0x7FC00000, .bits 32 0x3F800000] (.bits 16 0xFF78) := by
  cvt_eval [ue5m3_one, enc_ue5m3_one]

/-! ## Narrowing an `.f16x2` or `.bf16x2` source -/

private theorem e4m3_mone {x : ℝ} {ov : Overflow} (hx : x = -1) :
    (Layout.binary 4 3 true .e4m3).round .rn ov x false = some (.fin (-1)) := by
  subst hx; rexact 56
private theorem e4m3_two {x : ℝ} {ov : Overflow} (hx : x = 2) :
    (Layout.binary 4 3 true .e4m3).round .rn ov x false = some (.fin 2) := by
  subst hx; rexact 64
-- `cvt.rn.satfinite.e4m3x2.f16x2 d, a`: the upper half of `a` (2.0) to the upper byte.
example : run (cv (x2 .e4m3) (x2 .f16) (some .rn) (satfinite := true)) [.bits 32 0x4000BC00] =
    out [.bits 32 0x4000BC00] (.pair (.float .e4m3 (-1)) (.float .e4m3 2)) := by
  cvt_eval [e4m3_mone, e4m3_two]
-- `cvt.rz.satfinite.ue8m0x2.bf16x2 d, a`: `0x3F80` is 1.0.
example : run (cv (x2 .ue8m0) (x2 .bf16) (some .rz) (satfinite := true)) [.bits 32 0x3F803F80] =
    out [.bits 32 0x3F803F80] (.bits 16 0x7F7F) := by cvt_eval [ue8m0_one, enc_ue8m0_one]

/-! ## Scale factors (EXT-UE8M0) -/

private theorem e4m3_quarter {x : ℝ} {ov : Overflow} (hx : x = 1 / 4) :
    (Layout.binary 4 3 true .e4m3).round .rn ov x false = some (.fin (1 / 4)) := by
  subst hx; rexact 40
-- `.scaled::n1::ue8m0` with the factor `0x81` (4) divides both inputs: 4.0 and 1.0 give 1.0 and
-- 0.25.
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true))
    [.bits 32 0x40800000, .bits 32 0x3F800000, .bits 8 0x81] =
    out [.bits 32 0x40800000, .bits 32 0x3F800000, .bits 8 0x81]
      (.pair (.float .e4m3 (1 / 4)) (.float .e4m3 1)) := by
  cvt_eval [e4m3_one, e4m3_quarter, ue8m0Scale_eq]
-- A subnormal input is flushed to zero first; for a negative one the sign of that zero is not
-- stated, so it has no rule unless `.pzo` makes the result `+0`.
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true))
    [.bits 32 1, .bits 32 0x3F800000, .bits 8 0x7F] =
    out [.bits 32 1, .bits 32 0x3F800000, .bits 8 0x7F]
      (.pair (.float .e4m3 1) (.float .e4m3 0)) := by cvt_eval [e4m3_one, ue8m0Scale_eq]
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true))
    [.bits 32 0x80000001, .bits 32 0x3F800000, .bits 8 0x7F] = .error .noRule := by
  cvt_eval [e4m3_one, ue8m0Scale_eq]
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 3 (satfinite := true) (pzo := true)
      (scaled := true)) [.bits 32 0x80000001, .bits 32 0x3F800000, .bits 8 0x7F] =
    out [.bits 32 0x80000001, .bits 32 0x3F800000, .bits 8 0x7F]
      (.pair (.float .e4m3 1) (.float .e4m3 0)) := by cvt_eval [e4m3_one, ue8m0Scale_eq]
-- A scale factor `0` has no value (EXT-UE8M0).
example : run (cv (x2 .e4m3) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true))
    [.bits 32 0x40800000, .bits 32 0x3F800000, .bits 8 0] = .error .noRule := by cvt_eval

private theorem s2f6_quarter {x : ℝ} (hx : x = 1 / 4) :
    (Layout.fixed 8 6).round .rn .satfinite x false = some (.fin (1 / 4)) := by
  subst hx; exact s2f6_val (k := 16) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Layout.fixedVal])
private theorem enc_s2f6_quarter {q : ℚ} (hq : q = 1 / 4) :
    (Layout.fixed 8 6).encode (.fin q) = some 0x10 := by subst hq; renc
-- `.scaled::n2::ue8m0` to `.s2f6x2`: `a / scale-factor[15:8]` (4) and `b / scale-factor[7:0]` (2).
example : run (cv (x2 .s2f6) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true))
    [.bits 32 0x3F800000, .bits 32 0x3F800000, .bits 16 0x8180] =
    out [.bits 32 0x3F800000, .bits 32 0x3F800000, .bits 16 0x8180] (.bits 16 0x1020) := by
  cvt_eval [s2f6_quarter, s2f6_half, enc_s2f6_quarter, enc_s2f6_half, ue8m0Scale_eq]

private theorem bf16_two {x : ℝ} (hx : x = 2) :
    (Layout.binary 8 7 true .ieee).round .rn .inf x false = some (.fin 2) := by
  subst hx; rexact 0x4000
private theorem bf16_huge {x : ℝ} (hx : x = 6 * 2 ^ 127) :
    (Layout.binary 8 7 true .ieee).round .rn .inf x false = some (.inf false) := by
  subst hx; rinf
-- `cvt.rn.scaled::n2::ue8m0.bf16x2.e2m1x2`: the upper element (1.0) times `0x80` (2), the lower
-- element times `0x7f` (1).
example : run (cv (x2 .bf16) (x2 .e2m1) (some .rn) 2 (scaled := true))
    [.bits 8 0x22, .bits 16 0x807F] =
    out [.bits 8 0x22, .bits 16 0x807F] (.pair (.float .bf16 1) (.float .bf16 2)) := by
  cvt_eval [bf16_two, ue8m0Scale_eq]
-- 6.0 times `2^127` overflows `.bf16` to infinity under `.rn`: no rule.
example : run (cv (x2 .bf16) (x2 .e2m1) (some .rn) 2 (scaled := true))
    [.bits 8 0x72, .bits 16 0xFE7F] = .error .noRule := by
  cvt_eval [bf16_huge, ue8m0Scale_eq]

/-! ## `.rs` with chosen random bits -/

private theorem f32_rep {x : ℝ} (n : Nat) (q : ℚ) (h : FloatFmt.f32.decode n = some q)
    (hq : (q : ℝ) = x) : FloatFmt.f32.representable x := ⟨n, q, h, hq⟩
/-- The `.f32` decoding of a pattern. -/
macro "f32dec" : tactic => `(tactic| norm_num [FloatFmt.decode, FloatFmt.layout, Layout.decode,
  Layout.width, Layout.fieldVal, Layout.magnitude, Layout.bias, FVal.num])
private theorem rep_big : FloatFmt.f32.representable 70000 :=
  f32_rep 0x4788B800 70000 (by f32dec) (by norm_num)
private theorem rep_one : FloatFmt.f32.representable 1 :=
  f32_rep 0x3F800000 1 (by f32dec) (by norm_num)
private theorem rep_tie : FloatFmt.f32.representable (2049 / 2048) :=
  f32_rep 0x3F801000 (2049 / 2048) (by f32dec) (by norm_num)
/-- The hypotheses of the rounding lemmas for `.rs` to `.f16`. -/
macro "rsnum" : tactic => `(tactic| norm_num [RoundMode.applies, Layout.topField, Layout.maxNorm,
  Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.minNormal, rep_big, rep_one, rep_tie])
private theorem f16_rs_big {x : ℝ} (hx : x = 70000) :
    (Layout.binary 5 10 true .ieee).round (.rs 13 0) .satfinite x false = some (.fin 65504) := by
  subst hx; rw [Layout.round_satfinite] <;> rsnum
private theorem f16_rs_one {x : ℝ} (hx : x = 1) :
    (Layout.binary 5 10 true .ieee).round (.rs 13 0) .satfinite x false = some (.fin 1) := by
  subst hx; rw [Layout.round_exact (F := 0x3C00)] <;> rsnum
-- `cvt.rs.satfinite.f16x2.f32 d, 70000.0, 1.0, 0` is `0x7bff3c00`.
example : run (cv (x2 .f16) (f .f32) (some .rs) 3 (satfinite := true))
    [.bits 32 0x4788B800, .bits 32 0x3F800000, .bits 32 0] =
    out [.bits 32 0x4788B800, .bits 32 0x3F800000, .bits 32 0]
      (.pair (.float .f16 1) (.float .f16 65504)) := by
  cvt_eval [f16_rs_big, f16_rs_one]
-- An `rbits` half whose three high bits are not zero has no rule for `.f16`.
example : run (cv (x2 .f16) (f .f32) (some .rs) 3)
    [.bits 32 0x3F800000, .bits 32 0x3F800000, .bits 32 0xE0000000] = .error .noRule := by
  cvt_eval

private theorem f16_rs_up {x : ℝ} (hx : x = 1 + 1 / 2048) :
    (Layout.binary 5 10 true .ieee).round (.rs 13 0x1FFF) .inf x false =
      some (.fin (1 + 1 / 1024)) := by
  subst hx; rw [Layout.round_between (F := 0x3C00), RoundMode.away_rs (D := 4096)] <;> rsnum
private theorem f16_rs_down {x : ℝ} (hx : x = 1 + 1 / 2048) :
    (Layout.binary 5 10 true .ieee).round (.rs 13 0) .inf x false = some (.fin 1) := by
  subst hx; rw [Layout.round_between (F := 0x3C00), RoundMode.away_rs (D := 4096)] <;> rsnum
-- `1 + 2^-11` to `.f16` discards the bit `2^-11`, 4096 units of `2^-13` ulps: with the random
-- bits `0x1FFF` the carry rounds away from zero to `1 + 2^-10`, with `0` toward zero to 1.0.
example : run (cv (x2 .f16) (f .f32) (some .rs) 3)
    [.bits 32 0x3F801000, .bits 32 0x3F801000, .bits 32 0x1FFF0000] =
    out [.bits 32 0x3F801000, .bits 32 0x3F801000, .bits 32 0x1FFF0000]
      (.pair (.float .f16 1) (.float .f16 (1 + 1 / 1024))) := by
  cvt_eval [f16_rs_up, f16_rs_down]

/-! ## Rules and decoding -/

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%rs".toList, 2, 16⟩,
      ⟨"%rc".toList, 2, 8⟩],
    labels := [], params := [] }
private def r (n : String) : Syntax.Operand := .register n

-- The rounding groups have a rule.
example : (cv (f .f16) (f .f32) (some .rn)).rule = some .threadCvt := rfl
example : (cv (f .f32) (f .f64) (some .rm)).rule = some .threadCvt := rfl
example : (cv (f .bf16) (f .f16) (some .rz)).rule = some .threadCvt := rfl
example : (cv (f .f32) (.int .s 32) (some .rn)).rule = some .threadCvt := rfl
example : (cv (x2 .f16) (f .f32) (some .rs) 3).rule = some .threadCvt := rfl
example : (cv (x2 .e2m1) (f .f32) (some .rn) 2 (satfinite := true)).rule = some .threadCvt := rfl
example : (cv (x2 .s2f6) (f .f32) (some .rn) 3 (satfinite := true) (scaled := true)).rule =
    some .threadCvt := rfl
example : (cv (x2 .ue8m0) (x2 .bf16) (some .rz)).rule = some .threadCvt := rfl
example : (cv (x2 .bf16) (x2 .ue5m3) (some .rn) 2 (scaled := true)).rule = some .threadCvt := rfl
-- `cvt.f32.f16` without qualifiers and `cvt.rn.f16x2.f32` have Core rules.
example : (cv (f .f32) (f .f16) none).rule = some .threadCvt := rfl
example : (cv (x2 .f16) (f .f32) (some .rn) 2).rule = some .threadCvt := rfl
-- Decode-only: `.tf32` (its layout is implementation defined), `.s2f6x2` from `.bf16x2`, and
-- `.rs` to the four-element formats.
example : (cv (f .tf32) (f .f32) (some .rna)).rule = none := rfl
example : (cv (f .tf32) (f .f32) (some .rn) (satfinite := true)).rule = none := rfl
example : (cv (x2 .s2f6) (x2 .bf16) (some .rn) (satfinite := true)).rule = none := rfl
example : CvtInstr.rule {
    dst := .packed (.float .e4m3) 4, src := f .f32, rnd := some .rs, satfinite := true, d := 0,
    srcs := [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5] } = none := rfl
-- A widening without a rounding modifier between `.f16` and `.bf16` has none.
example : (cv (f .bf16) (f .f16) none).rule = none := rfl
example : Decode.op env "cvt.rn.satfinite.s2f6x2.bf16x2" [r "%rs0", r "%r1"] =
    .ok (.cvt {
      dst := x2 .s2f6, src := x2 .bf16, rnd := some .rn, satfinite := true, d := 6,
      srcs := [.reg 1] }) := rfl
example : Decode.op env "cvt.rs.satfinite.f16x2.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (.cvt {
      dst := x2 .f16, src := f .f32, rnd := some .rs, satfinite := true, d := 0,
      srcs := [.reg 1, .reg 2, .reg 3] }) := rfl
example : Decode.op env "cvt.rn.satfinite.scaled::n1::ue8m0.e4m3x2.f32"
    [r "%rs0", r "%r1", r "%r2", r "%rc1"] =
    .ok (.cvt {
      dst := x2 .e4m3, src := f .f32, rnd := some .rn, satfinite := true, scaled := true, d := 6,
      srcs := [.reg 1, .reg 2, .reg 9] }) := rfl

end
end PTX.Tests.CvtRound
