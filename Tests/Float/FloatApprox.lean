-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Float.FloatIeee

/-! The tables of THREAD-FLOAT-APPROX (§9.7.3.8, §9.7.3.13–22, §9.7.4.9–10) on one lane: every row
of every table, `.ftz` on inputs, a finite input of each instruction without a rule, the upper word
of the `.ftz.f64` approximations with the canonical NaN `0x7fffffff00000000`, `-Inf` of
`rsqrt.approx.ftz.f64`, `div.approx` for `2^126 < |b| < 2^128`, and `div.full` without a rule. -/
namespace PTX.Tests.FloatApprox
noncomputable section

set_option exponentiation.threshold 1100
set_option maxRecDepth 4000

/-- An approximate one-lane instruction. -/
private abbrev A (op : FOp) (fmt : FloatFmt := .f32) (ftz : Bool := false) (lanes : Nat := 1) :
    FloatInstr :=
  { op, ty := ⟨fmt, lanes⟩, mode := .approx, ftz, dsts := [some 0], srcs := [] }

private abbrev nan : FVal := .nan none
private abbrev pinf : FVal := .inf false
private abbrev ninf : FVal := .inf true
private abbrev pz : FVal := .zero false
private abbrev nz : FVal := .zero true
private abbrev val (v : FVal) : Option FOut := some (.val v)
/-- The smallest positive `.f32` subnormal number. -/
private abbrev s32 : FVal := .fin (1 / 2 ^ 149)
private abbrev ns32 : FVal := .fin (-(1 / 2 ^ 149))

/-! ## rcp.approx.f32 -/

example : (A .rcp).lane [ninf] = val nz := by lane_eval
example : (A .rcp).lane [nz] = val ninf := by lane_eval
example : (A .rcp).lane [pz] = val pinf := by lane_eval
example : (A .rcp).lane [pinf] = val pz := by lane_eval
example : (A .rcp).lane [.nan (some 0x7fc00000)] = val nan := by lane_eval
example : (A .rcp).lane [.fin 2] = none := by lane_eval
example : (A .rcp).lane [s32] = none := by lane_eval
example : (A .rcp (ftz := true)).lane [ns32] = val ninf := by lane_eval

/-! ## sqrt.approx.f32 -/

example : (A .sqrt).lane [ninf] = val nan := by lane_eval
example : (A .sqrt).lane [.fin (-4)] = val nan := by lane_eval
example : (A .sqrt).lane [nz] = val nz := by lane_eval
example : (A .sqrt).lane [pz] = val pz := by lane_eval
example : (A .sqrt).lane [pinf] = val pinf := by lane_eval
example : (A .sqrt).lane [nan] = val nan := by lane_eval
example : (A .sqrt).lane [.fin 4] = none := by lane_eval
-- A negative subnormal is not listed without `.ftz`; with `.ftz` it is the `-0.0` row.
example : (A .sqrt).lane [ns32] = none := by lane_eval
example : (A .sqrt (ftz := true)).lane [ns32] = val nz := by lane_eval

/-! ## rsqrt.approx.f32 and rsqrt.approx.f64 -/

example : (A .rsqrt).lane [ninf] = val nan := by lane_eval
example : (A .rsqrt).lane [.fin (-4)] = val nan := by lane_eval
example : (A .rsqrt).lane [nz] = val ninf := by lane_eval
example : (A .rsqrt).lane [pz] = val pinf := by lane_eval
example : (A .rsqrt).lane [pinf] = val pz := by lane_eval
example : (A .rsqrt).lane [nan] = val nan := by lane_eval
example : (A .rsqrt).lane [.fin 4] = none := by lane_eval
example : (A .rsqrt .f64).lane [nz] = val ninf := by lane_eval
example : (A .rsqrt .f64).lane [.nan (some 0x7ff8000000000000)] = val nan := by lane_eval
example : (A .rsqrt .f64).lane [.fin 4] = none := by lane_eval

/-! ## rcp.approx.ftz.f64 and rsqrt.approx.ftz.f64 on the upper word -/

/-- The smallest positive `.f64` subnormal number. -/
private abbrev s64 : FVal := .fin (1 / 2 ^ 1074)
private abbrev ns64 : FVal := .fin (-(1 / 2 ^ 1074))

example : (A .rcp .f64 true).lane [ninf] = val nz := by lane_eval
example : (A .rcp .f64 true).lane [ns64] = val ninf := by lane_eval
example : (A .rcp .f64 true).lane [nz] = val ninf := by lane_eval
example : (A .rcp .f64 true).lane [pz] = val pinf := by lane_eval
example : (A .rcp .f64 true).lane [s64] = val pinf := by lane_eval
example : (A .rcp .f64 true).lane [pinf] = val pz := by lane_eval
-- A NaN whose upper word is a NaN gives the canonical NaN.
example : (A .rcp .f64 true).lane [.nan (some 0x7ff8000000000000)] =
    val (.nan (some 0x7fffffff00000000)) := by lane_eval
example : (A .rcp .f64 true).lane [.nan (some 0xfff0000100000000)] =
    val (.nan (some 0x7fffffff00000000)) := by lane_eval
-- A NaN with its payload in the low word only has an infinite upper word: no rule.
example : (A .rcp .f64 true).lane [.nan (some 0x7ff0000000000001)] = none := by lane_eval
-- An opaque NaN has an unknown upper word: no rule.
example : (A .rcp .f64 true).lane [nan] = none := by lane_eval

example : (A .rsqrt .f64 true).lane [ninf] = val nan := by lane_eval
example : (A .rsqrt .f64 true).lane [ns64] = val ninf := by lane_eval
example : (A .rsqrt .f64 true).lane [nz] = val ninf := by lane_eval
example : (A .rsqrt .f64 true).lane [pz] = val pinf := by lane_eval
example : (A .rsqrt .f64 true).lane [s64] = val pinf := by lane_eval
example : (A .rsqrt .f64 true).lane [pinf] = val pz := by lane_eval
example : (A .rsqrt .f64 true).lane [.nan (some 0x7ff8000000000000)] =
    val (.nan (some 0x7fffffff00000000)) := by lane_eval
example : (A .rsqrt .f64 true).lane [.nan (some 0x7ff0000000000001)] = none := by lane_eval

-- A negative normal input is not in the table: its upper word is `-1.0` in 1.11.20.
example : (A .rsqrt .f64 true).lane [.fin (-1)] = none := by
  lane_eval
  rw [Layout.round_exact (eb := 11) (mb := 20) (m := .rz) (x := -1) (F := 1023 * 2 ^ 20) trivial
    (by norm_num) (by decide) (by norm_num [Layout.magnitude, Layout.bias]) (by simp)]
  norm_num [Layout.fieldVal, Layout.magnitude, Layout.bias, ACls.of, Layout.subnormal,
    Layout.minNormal, List.lookup, Tests.FloatIeee.acls_beq]

/-! ## sin, cos, lg2, ex2 (`.f32`) -/

example : (A .sin).lane [ninf] = val nan := by lane_eval
example : (A .sin).lane [nz] = val nz := by lane_eval
example : (A .sin).lane [pz] = val pz := by lane_eval
example : (A .sin).lane [pinf] = val nan := by lane_eval
example : (A .sin).lane [nan] = val nan := by lane_eval
example : (A .sin).lane [.fin 1] = none := by lane_eval
example : (A .sin (ftz := true)).lane [ns32] = val nz := by lane_eval

example : (A .cos).lane [ninf] = val nan := by lane_eval
example : (A .cos).lane [nz] = val (.fin 1) := by lane_eval
example : (A .cos).lane [pz] = val (.fin 1) := by lane_eval
example : (A .cos).lane [pinf] = val nan := by lane_eval
example : (A .cos).lane [nan] = val nan := by lane_eval
example : (A .cos).lane [.fin 1] = none := by lane_eval

example : (A .lg2).lane [ninf] = val nan := by lane_eval
example : (A .lg2).lane [.fin (-1)] = val nan := by lane_eval
example : (A .lg2).lane [nz] = val ninf := by lane_eval
example : (A .lg2).lane [pz] = val ninf := by lane_eval
example : (A .lg2).lane [pinf] = val pinf := by lane_eval
example : (A .lg2).lane [nan] = val nan := by lane_eval
example : (A .lg2).lane [.fin 2] = none := by lane_eval

example : (A .ex2).lane [ninf] = val pz := by lane_eval
example : (A .ex2).lane [nz] = val (.fin 1) := by lane_eval
example : (A .ex2).lane [pz] = val (.fin 1) := by lane_eval
example : (A .ex2).lane [pinf] = val pinf := by lane_eval
example : (A .ex2).lane [nan] = val nan := by lane_eval
example : (A .ex2).lane [.fin 1] = none := by lane_eval
example : (A .ex2).lane [s32] = none := by lane_eval
example : (A .ex2 (ftz := true)).lane [s32] = val (.fin 1) := by lane_eval

/-! ## tanh (every type) -/

example : (A .tanh).lane [ninf] = val (.fin (-1)) := by lane_eval
example : (A .tanh).lane [nz] = val nz := by lane_eval
example : (A .tanh).lane [pz] = val pz := by lane_eval
example : (A .tanh).lane [pinf] = val (.fin 1) := by lane_eval
example : (A .tanh).lane [nan] = val nan := by lane_eval
example : (A .tanh).lane [.fin (1 / 2)] = none := by lane_eval
example : (A .tanh .f16).lane [ninf] = val (.fin (-1)) := by lane_eval
example : (A .tanh .bf16 (lanes := 2)).lane [pinf] = val (.fin 1) := by lane_eval
example : (A .tanh .f16 (lanes := 2)).lane [.fin 1] = none := by lane_eval

/-! ## ex2.approx.ftz.bf16 and ex2.approx.f16 -/

example : (A .ex2 .bf16 true).lane [ninf] = val pz := by lane_eval
example : (A .ex2 .bf16 true).lane [.fin (-(1 / 2 ^ 133))] = val (.fin 1) := by lane_eval
example : (A .ex2 .bf16 true).lane [nz] = val (.fin 1) := by lane_eval
example : (A .ex2 .bf16 true).lane [pz] = val (.fin 1) := by lane_eval
example : (A .ex2 .bf16 true (lanes := 2)).lane [.fin (1 / 2 ^ 133)] = val (.fin 1) := by lane_eval
example : (A .ex2 .bf16 true).lane [pinf] = val pinf := by lane_eval
example : (A .ex2 .bf16 true).lane [nan] = val nan := by lane_eval
example : (A .ex2 .bf16 true).lane [.fin 1] = none := by lane_eval

example : (A .ex2 .f16).lane [ninf] = val pz := by lane_eval
example : (A .ex2 .f16).lane [nz] = val (.fin 1) := by lane_eval
example : (A .ex2 .f16 (lanes := 2)).lane [pz] = val (.fin 1) := by lane_eval
example : (A .ex2 .f16).lane [pinf] = val pinf := by lane_eval
example : (A .ex2 .f16).lane [nan] = val nan := by lane_eval
example : (A .ex2 .f16).lane [.fin 1] = none := by lane_eval
-- An `.f16` subnormal input is not listed.
example : (A .ex2 .f16).lane [.fin (1 / 2 ^ 24)] = none := by lane_eval

/-! ## div.approx.f32 and div.full.f32 -/

/-- A divisor in `2^126 < |b| < 2^128`. -/
private abbrev big : ℚ := 2 ^ 127

-- An infinite `a` gives NaN; a finite `a` over a positive `b` gives the zero with the sign of `a`.
example : (A .div).lane [pinf, .fin big] = val nan := by lane_eval
example : (A .div).lane [ninf, .fin (-big)] = val nan := by lane_eval
example : (A .div).lane [.fin (-3), .fin big] = val nz := by lane_eval
example : (A .div).lane [.fin 3, .fin big] = val pz := by lane_eval
example : (A .div).lane [nz, .fin big] = val nz := by lane_eval
-- A negative `b` leaves the sign of the zero open, and a NaN `a` is not covered: no rule.
example : (A .div).lane [.fin 3, .fin (-big)] = none := by lane_eval
example : (A .div).lane [nan, .fin big] = none := by lane_eval
-- Outside the range there is no rule.
example : (A .div).lane [.fin 3, .fin 2] = none := by lane_eval
example : (A .div).lane [.fin 3, .fin (2 ^ 126)] = none := by lane_eval
example : (A .div).lane [.fin 3, pinf] = none := by lane_eval
example : { A .div with mode := .full }.lane [pinf, .fin big] = none := by lane_eval

end

end PTX.Tests.FloatApprox
