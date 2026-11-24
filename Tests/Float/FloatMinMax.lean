-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Float.FloatIeee

/-! `min` and `max` of THREAD-FLOAT-IEEE (§9.7.3.11–12, §9.7.4.7–8) on one lane: signed zeros, one
and two NaN inputs, `.NaN`, `.abs`, `.xorsign`, three inputs, `.ftz`, the packed half types and the
cases without a rule (Appendix B item 1 of the floating design, `.xorsign` with an opaque NaN). -/
namespace PTX.Tests.FloatMinMax
noncomputable section

/-- A `min` or `max` lane on format `fmt` with `lanes` elements per register. -/
private abbrev I (op : FOp) (fmt : FloatFmt := .f32) (lanes : Nat := 1) : FloatInstr :=
  { op, ty := ⟨fmt, lanes⟩, dsts := [some 0], srcs := [] }

private abbrev nan : FVal := .nan none
private abbrev pz : FVal := .zero false
private abbrev nz : FVal := .zero true
private abbrev val (v : FVal) : Option FOut := some (.val v)

-- `-0` is below `+0` in either order.
example : (I .min).lane [pz, nz] = val nz := by lane_eval
example : (I .min).lane [nz, pz] = val nz := by lane_eval
example : (I .max).lane [nz, pz] = val pz := by lane_eval
example : (I .max (fmt := .f64)).lane [pz, nz] = val pz := by lane_eval
-- Numbers and infinities.
example : (I .min).lane [.fin 2, .fin (-3)] = val (.fin (-3)) := by lane_eval
example : (I .max).lane [.inf true, .fin (-3)] = val (.fin (-3)) := by lane_eval
example : (I .min).lane [.inf false, .fin 7] = val (.fin 7) := by lane_eval
-- One NaN input gives the other input; two give an opaque NaN.
example : (I .min).lane [nan, .fin 2] = val (.fin 2) := by lane_eval
example : (I .max).lane [.fin 2, .nan (some 0x7fc00000)] = val (.fin 2) := by lane_eval
example : (I .max).lane [nan, .nan (some 0x7fc00000)] = val nan := by lane_eval
-- `.NaN`: any NaN input gives an opaque NaN.
example : { I .min with nanMod := true }.lane [nan, .fin 2] = val nan := by lane_eval
example : { I .max .f16 2 with nanMod := true }.lane [.fin 2, nan] = val nan := by lane_eval
-- `.abs`: the minimum and maximum of the absolute values.
example : { I .min with absMod := true }.lane [.fin (-1), .fin 2] = val (.fin 1) := by lane_eval
example : { I .max with absMod := true }.lane [.fin (-3), .fin 2] = val (.fin 3) := by lane_eval
-- `.xorsign.abs`: the sign bit is the XOR of the input signs, taken before `.abs`.
example : { I .min with absMod := true, xorsign := true }.lane [.fin (-1), .fin 2] =
    val (.fin (-1)) := by lane_eval
example : { I .max with absMod := true, xorsign := true }.lane [.fin (-3), .fin (-2)] =
    val (.fin 3) := by lane_eval
example : { I .min .bf16 with absMod := true, xorsign := true }.lane [nz, .fin 2] = val nz := by
  lane_eval
-- A NaN input with a known pattern supplies its sign bit (`0xffc00000` is negative).
example : { I .min with absMod := true, xorsign := true }.lane
    [.nan (some 0xffc00000), .fin 2] = val (.fin (-2)) := by lane_eval
-- An opaque NaN input has no known sign bit: no rule when the result is a number.
example : { I .min with absMod := true, xorsign := true }.lane [nan, .fin 2] = none := by lane_eval
-- A NaN result ignores `.xorsign`.
example : { I .min with absMod := true, xorsign := true, nanMod := true }.lane [nan, .fin 2] =
    val nan := by lane_eval
-- The `.f32` `max` pseudocode is read with `&&`: `.xorsign` applies to a number result.
example : { I .max with absMod := true, xorsign := true }.lane
    [.nan (some 0x7fc00000), .fin (-2)] = val (.fin (-2)) := by lane_eval
-- Three inputs, with `.abs`.
example : (I .min).lane [.fin 3, .fin 1, .fin 2] = val (.fin 1) := by lane_eval
example : (I .max).lane [.fin 3, nan, .fin 5] = val (.fin 5) := by lane_eval
example : { I .max with absMod := true }.lane [.fin 3, .fin 1, .fin (-4)] = val (.fin 4) := by
  lane_eval
example : { I .min with nanMod := true }.lane [.fin 3, .fin 1, nan] = val nan := by lane_eval
-- `.ftz` flushes inputs: a positive subnormal becomes `+0`, which is above `-0`.
example : { I .max with ftz := true }.lane [.fin (1 / 2 ^ 149), nz] = val pz := by lane_eval
example : (I .max).lane [.fin (1 / 2 ^ 149), nz] = val (.fin (1 / 2 ^ 149)) := by lane_eval
-- `.f16x2` lanes: each lane is computed on its own elements.
example : (I .min .f16 2).lane [.fin 1, .fin (-1)] = val (.fin (-1)) := by lane_eval
example : (I .max .bf16 2).lane [nan, .fin 4] = val (.fin 4) := by lane_eval
-- Appendix B item 1: packed half `max.xorsign.abs` with a NaN `fA[i]` and a number result has
-- no rule; a NaN `fB[i]` uses its sign bit; the scalar half `max` and packed `min` follow `d`.
example : { I .max .f16 2 with absMod := true, xorsign := true }.lane
    [.nan (some 0x7e00), .fin 2] = none := by lane_eval
example : { I .max .f16 2 with absMod := true, xorsign := true }.lane
    [.fin 2, .nan (some 0xfe00)] = val (.fin (-2)) := by lane_eval
example : { I .max .f16 with absMod := true, xorsign := true }.lane
    [.nan (some 0x7e00), .fin (-2)] = val (.fin (-2)) := by lane_eval
example : { I .min .f16 2 with absMod := true, xorsign := true }.lane
    [.nan (some 0x7e00), .fin (-2)] = val (.fin (-2)) := by lane_eval

end

end PTX.Tests.FloatMinMax
