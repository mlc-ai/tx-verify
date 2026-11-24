-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Float

/-! The special-value table of THREAD-FLOAT-IEEE (§4.4 of the floating design), evaluated on one
lane (`FloatInstr.lane`): `add`, `sub`, `mul`, `fma`, `mad`, `div`, `rcp.rn` and `sqrt.rn` with NaN,
signed zeros and infinities, the sign of an exact zero sum, `.sat`, `.relu`, `.oob`, `.ftz` on
inputs and results, the band where `.ftz` has no rule, the forms without a rounding modifier and
the mixed-precision forms. -/
namespace PTX.Tests.FloatIeee
noncomputable section

public section

/-- `ACls` equality as a Boolean decides the equality, so `simp` evaluates table lookups. -/
theorem acls_beq (a b : ACls) : (a == b) = decide (a = b) := rfl

/-- Evaluate one lane: unfold the lane's definitions, decide the finite checks, then normalize the
rational arithmetic. -/
macro "lane_eval" : tactic => `(tactic| (
  simp (config := { decide := true }) [FloatInstr.lane, FloatInstr.rule, FloatInstr.ieee,
    FloatInstr.arith, FloatInstr.compare, FloatInstr.approx, FloatInstr.approxTable?,
    FloatInstr.flushIn, FloatInstr.srcFmt, FVal.add, FVal.mul, FVal.div, FVal.toRat, FVal.isNeg,
    FVal.isNaN, FVal.negate, FVal.absV, FVal.sat, FVal.relu, FVal.lt, FVal.minMax, minMaxOp,
    FVal.copysign, FVal.signBit, FVal.withSign, FVal.subnormalIn, Cmp.evalF, FCmp.eval,
    TestProp.eval, Layout.roundVal, Layout.sqrt, Layout.flush, Layout.subnormal,
    Layout.minNormal, Layout.bias, Layout.width, FloatFmt.layout, FloatRound.mode, ACls.of,
    ARes.val, divApprox, approxF64, upperWord, upperLayout, Layout.decode, Layout.magnitude,
    rcpTable, rcpF64Table, sqrtTable, rsqrtTable, rsqrtF64Table, sinTable, cosTable, lg2Table,
    ex2Table, tanhTable, ex2Bf16Table, ex2F16Table, List.lookup, acls_beq]
  <;> norm_num))

end

/-- A one-lane instruction of operation `op` on format `fmt`. -/
private abbrev I (op : FOp) (fmt : FloatFmt := .f32) (rnd : Option FloatRound := some .rn) :
    FloatInstr :=
  { op, ty := ⟨fmt, 1⟩, rnd, dsts := [some 0], srcs := [] }

private abbrev nan : FVal := .nan none
private abbrev pinf : FVal := .inf false
private abbrev ninf : FVal := .inf true
private abbrev pz : FVal := .zero false
private abbrev nz : FVal := .zero true
private abbrev one : FVal := .fin 1
private abbrev val (v : FVal) : Option FOut := some (.val v)

/-! ## Addition and subtraction -/

-- A NaN operand gives an opaque NaN, a known pattern included.
example : (I .add).lane [nan, one] = val nan := by lane_eval
example : (I .add).lane [one, .nan (some 0x7fc00000)] = val nan := by lane_eval
-- `+∞ + -∞` and `+∞ - +∞` are invalid.
example : (I .add).lane [pinf, ninf] = val nan := by lane_eval
example : (I .sub).lane [pinf, pinf] = val nan := by lane_eval
-- An infinity and a number, or two infinities of one sign, give that infinity.
example : (I .add).lane [pinf, one] = val pinf := by lane_eval
example : (I .add).lane [one, ninf] = val ninf := by lane_eval
example : (I .add).lane [ninf, ninf] = val ninf := by lane_eval
example : (I .sub).lane [one, pinf] = val ninf := by lane_eval
-- The sign of an exact zero sum: `(+0) + (-0)` is `+0` under `.rn` and `-0` under `.rm`.
example : (I .add).lane [pz, nz] = val pz := by lane_eval
example : (I .add (rnd := some .rm)).lane [pz, nz] = val nz := by lane_eval
example : (I .add).lane [nz, nz] = val nz := by lane_eval
example : (I .add (rnd := some .rm)).lane [pz, pz] = val pz := by lane_eval
-- `x - x` is `+0`, and `-0` under `.rm`.
example : (I .sub).lane [one, one] = val pz := by lane_eval
example : (I .sub (rnd := some .rm)).lane [one, one] = val nz := by lane_eval
example : (I .sub (rnd := some .rz)).lane [.fin (-3), .fin (-3)] = val pz := by lane_eval
example : (I .sub).lane [nz, pz] = val nz := by lane_eval
-- Without a written rounding modifier `add`, `sub` and `mul` have no rule (D2).
example : (I .add (rnd := none)).lane [one, one] = none := by lane_eval
example : (I .sub (rnd := none)).lane [pinf, ninf] = none := by lane_eval
example : (I .mul (rnd := none)).lane [pz, one] = none := by lane_eval

/-! ## Multiplication, fused multiply-add, division -/

-- `(-0) · (+1) = -0`; `0 · ∞` is invalid; an infinite product has the XOR of the signs.
example : (I .mul).lane [nz, one] = val nz := by lane_eval
example : (I .mul).lane [pz, ninf] = val nan := by lane_eval
example : (I .mul).lane [ninf, .fin (-2)] = val pinf := by lane_eval
example : (I .mul).lane [nan, pinf] = val nan := by lane_eval
-- `fma(0, ∞, NaN)` and `fma(+∞, 1, -∞)` are NaN; an infinite product or addend gives it.
example : (I .fma).lane [pz, pinf, nan] = val nan := by lane_eval
example : (I .fma).lane [pinf, one, ninf] = val nan := by lane_eval
example : (I .fma).lane [pinf, .fin (-1), one] = val ninf := by lane_eval
example : (I .fma).lane [one, one, ninf] = val ninf := by lane_eval
-- An exactly cancelling product: `fma(2, 3, -6)` is `+0`, and `-0` under `.rm`.
example : (I .fma).lane [.fin 2, .fin 3, .fin (-6)] = val pz := by lane_eval
example : (I .fma (rnd := some .rm)).lane [.fin 2, .fin 3, .fin (-6)] = val nz := by lane_eval
-- A zero product keeps its sign in the zero sum: `(-0)·1 + (-0) = -0`, `(+0)·1 + (-0) = +0`.
example : (I .fma).lane [nz, one, nz] = val nz := by lane_eval
example : (I .fma).lane [pz, one, nz] = val pz := by lane_eval
-- `mad` has the rule of `fma`.
example : (I .mad).lane [pz, pinf, one] = val nan := by lane_eval
example : (I .mad).lane [.fin 2, .fin 3, .fin (-6)] = val pz := by lane_eval
-- Division: `0 / 0`, `∞ / ∞` invalid; a nonzero number over zero and an infinity over a number
-- give an infinity; a number over an infinity gives a zero; signs by XOR.
example : (I .div).lane [pz, nz] = val nan := by lane_eval
example : (I .div).lane [ninf, pinf] = val nan := by lane_eval
example : (I .div).lane [one, nz] = val ninf := by lane_eval
example : (I .div).lane [.fin (-1), pz] = val ninf := by lane_eval
example : (I .div).lane [pinf, .fin (-2)] = val ninf := by lane_eval
example : (I .div).lane [.fin (-1), pinf] = val nz := by lane_eval
example : (I .div).lane [nz, .fin 5] = val nz := by lane_eval
example : (I .div).lane [nan, one] = val nan := by lane_eval
-- `rcp.rn` is `1 / a`.
example : (I .rcp).lane [pz] = val pinf := by lane_eval
example : (I .rcp).lane [nz] = val ninf := by lane_eval
example : (I .rcp).lane [ninf] = val nz := by lane_eval
example : (I .rcp (fmt := .f64)).lane [nan] = val nan := by lane_eval
-- `sqrt.rn`: a NaN and every negative operand give NaN; a zero keeps its sign; `+∞` stays.
example : (I .sqrt).lane [nan] = val nan := by lane_eval
example : (I .sqrt).lane [.fin (-1)] = val nan := by lane_eval
example : (I .sqrt).lane [ninf] = val nan := by lane_eval
example : (I .sqrt).lane [nz] = val nz := by lane_eval
example : (I .sqrt).lane [pinf] = val pinf := by lane_eval

/-! ## `.sat`, `.relu`, `.oob` -/

-- `.sat`: a NaN result is `+0`, `-∞` gives `+0`, `+∞` gives `1.0`, a `-0` result has no rule.
example : { I .add with sat := true }.lane [pinf, ninf] = val pz := by lane_eval
example : { I .add with sat := true }.lane [ninf, one] = val pz := by lane_eval
example : { I .mul with sat := true }.lane [pinf, one] = val one := by lane_eval
example : { I .add with sat := true }.lane [nz, nz] = none := by lane_eval
example : { I .fma with sat := true }.lane [nz, one, nz] = none := by lane_eval
-- `.relu` (half `fma`): a negative result is `+0`, NaN stays an opaque NaN, `-0` has no rule.
example : { I .fma .f16 with relu := true }.lane [ninf, one, pz] = val pz := by lane_eval
example : { I .fma .bf16 with relu := true }.lane [nan, one, pz] = val nan := by lane_eval
example : { I .fma .f16 with relu := true }.lane [nz, one, nz] = none := by lane_eval
example : { I .fma .f16 with relu := true }.lane [pinf, one, pz] = val pinf := by lane_eval
-- `.oob`: a NaN operand has no rule; otherwise the result is that of `fma`.
example : { I .fma .f16 with oob := true }.lane [nan, one, pz] = none := by lane_eval
example : { I .fma .bf16 with oob := true }.lane [one, one, .nan (some 0x7fff)] = none := by
  lane_eval
example : { I .fma .f16 with oob := true }.lane [pinf, one, one] = val pinf := by lane_eval
example : { I .fma .bf16 with oob := true, relu := true }.lane [ninf, one, one] = val pz := by
  lane_eval

/-! ## `.ftz` on inputs -/

/-- The smallest positive `.f32` subnormal number. -/
private abbrev sub32 : FVal := .fin (1 / 2 ^ 149)

-- With `.ftz` the subnormal input is a zero: `0 · ∞` is NaN; without it the product is `+∞`.
example : { I .mul with ftz := true }.lane [sub32, pinf] = val nan := by lane_eval
example : (I .mul).lane [sub32, pinf] = val pinf := by lane_eval
-- The flushed zero keeps the sign: `(-sub) + (-0) = -0` under `.ftz`.
example : { I .add with ftz := true }.lane [.fin (-(1 / 2 ^ 149)), nz] = val nz := by lane_eval
example : { I .div with ftz := true }.lane [one, .fin (-(1 / 2 ^ 149))] = val ninf := by lane_eval
-- `sqrt.rn.ftz` of a negative subnormal is `-0`.
example : { I .sqrt with ftz := true }.lane [.fin (-(1 / 2 ^ 149))] = val nz := by lane_eval

/-! ## Rounded results

These evaluate `Layout.round` with the characterization lemmas of THREAD-FLOAT-ROUND. -/

/-- Without `.ftz` the rounding of a result is `Layout.round` with IEEE 754 overflow. -/
private theorem roundFtz_false (L : Layout) (m : RoundMode) (r : ℝ) :
    L.roundFtz m false r = L.round m .inf r false := by
  simp [Layout.roundFtz]

-- An exact sum: `add.rn.f16 1 + 2 = 3` (field `16896` of `.f16`).
example : (I .add .f16).lane [one, .fin 2] = val (.fin 3) := by
  lane_eval
  rw [roundFtz_false, Layout.round_exact (eb := 5) (mb := 10) (m := .rn) (x := 3) (F := 16896)
    trivial (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]
-- A midpoint goes to the even code under `.rn`: `1 + 2^-11` gives `1`; `.rp` gives `1 + 2^-10`.
example : (I .add .f16).lane [one, .fin (1 / 2 ^ 11)] = val one := by
  lane_eval
  rw [roundFtz_false, Layout.round_between (eb := 5) (mb := 10) (m := .rn) (F := 15360) trivial
    (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp),
    RoundMode.away_rn_tie (by norm_num [Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]
example : (I .add .f16 (some .rp)).lane [one, .fin (1 / 2 ^ 11)] =
    val (.fin (1 + 1 / 2 ^ 10)) := by
  lane_eval
  rw [roundFtz_false, Layout.round_between (eb := 5) (mb := 10) (m := .rp) (F := 15360) trivial
    (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp), RoundMode.away_rp]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]
-- Overflow: `65504 + 65504` is `+∞` under `.rn` and MAX_NORM `65504` under `.rz`.
example : (I .add .f16).lane [.fin 65504, .fin 65504] = val pinf := by
  lane_eval
  rw [roundFtz_false, Layout.round_inf_ieee (eb := 5) (mb := 10) (m := .rn) trivial
    (by norm_num [Layout.maxNorm, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.topField, Layout.magnitude, Layout.bias]
example : (I .add .f16 (some .rz)).lane [.fin 65504, .fin 65504] = val (.fin 65504) := by
  lane_eval
  rw [roundFtz_false, Layout.round_inf_ieee (eb := 5) (mb := 10) (m := .rz) trivial
    (by norm_num [Layout.maxNorm, Layout.topField, Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.topField, Layout.magnitude, Layout.bias]
-- `sqrt.rn.f32 4 = 2`.
example : (I .sqrt).lane [.fin 4] = val (.fin 2) := by
  lane_eval
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
  rw [h, roundFtz_false, Layout.round_exact (eb := 8) (mb := 23) (m := .rn) (x := 2)
    (F := 2 ^ 30) trivial (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]
-- `.sat` clamps a rounded `3` to `1.0`.
example : { I .add .f16 with sat := true }.lane [one, .fin 2] = val one := by
  lane_eval
  rw [roundFtz_false, Layout.round_exact (eb := 5) (mb := 10) (m := .rn) (x := 3) (F := 16896)
    trivial (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, FVal.sat]
-- `.ftz` on a result: the subnormal product `2^-130` is flushed to `+0`.
example : { I .mul with ftz := true }.lane [.fin (1 / 2 ^ 100), .fin (1 / 2 ^ 30)] = val pz := by
  lane_eval
  rw [Layout.roundFtz, Layout.round_exact (eb := 8) (mb := 23) (m := .rn) (F := 2 ^ 19) trivial
    (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal,
    Layout.minNormal]
-- `.ftz` with `.sat` on a negative subnormal result gives `-0`, which `.sat` leaves without a
-- rule.
example : { I .mul with ftz := true, sat := true }.lane
    [.fin (-(1 / 2 ^ 100)), .fin (1 / 2 ^ 30)] = none := by
  lane_eval
  rw [Layout.roundFtz, Layout.round_exact (eb := 8) (mb := 23) (m := .rn) (F := 2 ^ 19) trivial
    (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal,
    Layout.minNormal, FVal.sat]
-- The band of D7: `(1 - 2^-24) · 2^-126` lies below the smallest normal number and rounds to it
-- (a tie to the even field `2^23`), so `.ftz` has no rule; without `.ftz` the result is `2^-126`.
example : { I .mul with ftz := true }.lane [.fin (1 - 1 / 2 ^ 24), .fin (1 / 2 ^ 126)] =
    none := by
  lane_eval
  rw [Layout.roundFtz, Layout.round_between (eb := 8) (mb := 23) (m := .rn) (F := 2 ^ 23 - 1)
    trivial (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp),
    RoundMode.away_rn_tie (by norm_num [Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, Layout.flush, Layout.subnormal,
    Layout.minNormal]
example : (I .mul).lane [.fin (1 - 1 / 2 ^ 24), .fin (1 / 2 ^ 126)] =
    val (.fin (1 / 2 ^ 126)) := by
  lane_eval
  rw [roundFtz_false, Layout.round_between (eb := 8) (mb := 23) (m := .rn) (F := 2 ^ 23 - 1)
    trivial (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp),
    RoundMode.away_rn_tie (by norm_num [Layout.magnitude, Layout.bias])]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]
-- `add.rz.bf16x2.f32x2.f32x2`: `1 + 2^-10` rounds toward zero to the `.bf16` value `1`.
example : { I .add .bf16 (some .rz) with
    ty := ⟨.bf16, 2⟩, srcTys := [⟨.f32, 2⟩, ⟨.f32, 2⟩] }.lane [one, .fin (1 / 2 ^ 10)] =
    val one := by
  lane_eval
  rw [roundFtz_false, Layout.round_between (eb := 8) (mb := 7) (m := .rz) (F := 127 * 2 ^ 7)
    trivial (by decide) (by norm_num [Layout.magnitude, Layout.bias])
    (by norm_num [Layout.magnitude, Layout.bias]) (by simp), RoundMode.away_rz]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias]

/-! ## Mixed precision -/

-- `add.rn.f32.f16`: an `.f16` source is read in its format and converted exactly.
example : { I .add with srcTys := [⟨.f16, 1⟩, ⟨.f32, 1⟩] }.lane [pinf, ninf] = val nan := by
  lane_eval
example : { I .add with srcTys := [⟨.f16, 1⟩, ⟨.f32, 1⟩] }.lane [nz, nz] = val nz := by lane_eval
-- `fma.rn.sat.f32.bf16` with a NaN operand gives `+0`.
example : { I .fma with srcTys := [⟨.bf16, 1⟩, ⟨.bf16, 1⟩, ⟨.f32, 1⟩], sat := true }.lane
    [nan, one, one] = val pz := by lane_eval
-- `add.rz.ftz.f16x2.f32x2.f32x2`: an `.f32` subnormal input has no rule (D18).
example : { I .add .f16 (some .rz) with
    ty := ⟨.f16, 2⟩, srcTys := [⟨.f32, 2⟩, ⟨.f32, 2⟩], ftz := true }.lane
    [sub32, pinf] = none := by lane_eval
example : { I .add .f16 (some .rz) with
    ty := ⟨.f16, 2⟩, srcTys := [⟨.f32, 2⟩, ⟨.f32, 2⟩], ftz := true }.lane
    [one, pinf] = val pinf := by lane_eval
-- The decode-only forms have no lane: `mul.bf16x2.bf16x2.f16x2` and the mixed `fma` with a packed
-- half source.
example : { I .mul .bf16 none with ty := ⟨.bf16, 2⟩, srcTys := [⟨.bf16, 2⟩, ⟨.f16, 2⟩] }.lane
    [one, one] = none := by lane_eval
example : { I .fma with ty := ⟨.f32, 2⟩, srcTys := [⟨.f16, 2⟩, ⟨.f32, 2⟩, ⟨.f32, 2⟩] }.lane
    [one, one, one] = none := by lane_eval

end

end PTX.Tests.FloatIeee
