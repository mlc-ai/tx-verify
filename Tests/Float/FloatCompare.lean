-- SPDX-License-Identifier: Apache-2.0
module

public import Tests.Float.FloatIeee

/-! Comparisons, classification and the sign instructions of THREAD-FLOAT-IEEE on one lane: Tables
23 to 25 (§9.3.1.2) with NaN, signed zeros and infinities, `num` and `nan`, `.ftz` on comparison
inputs, `testp` for every class (§9.7.3.1), `copysign` (§9.7.3.2), `neg` and `abs` (§9.7.3.9–10),
`abs.f64` passing a NaN through. The combination with `BoolOp`, `p|q` and the `set` encodings
need the whole instruction and are tested with `execFloat`. -/
namespace PTX.Tests.FloatCompare
noncomputable section

set_option exponentiation.threshold 1100
set_option maxRecDepth 4000

/-- A one-lane instruction of operation `op` on format `fmt`. -/
private abbrev I (op : FOp) (fmt : FloatFmt := .f32) : FloatInstr :=
  { op, ty := ⟨fmt, 1⟩, dsts := [some 0], srcs := [] }

/-- `setp` with comparison `c`. -/
private abbrev S (c : FCmp) (fmt : FloatFmt := .f32) : FloatInstr := I (.setp c none) fmt

private abbrev nan : FVal := .nan none
private abbrev pinf : FVal := .inf false
private abbrev ninf : FVal := .inf true
private abbrev pz : FVal := .zero false
private abbrev nz : FVal := .zero true
private abbrev T : Option FOut := some (.pred true)
private abbrev F : Option FOut := some (.pred false)
private abbrev val (v : FVal) : Option FOut := some (.val v)

/-! ## Table 23: ordered comparisons are false with a NaN operand -/

example : (S (.ord .eq)).lane [nan, nan] = F := by lane_eval
example : (S (.ord .ne)).lane [nan, .fin 1] = F := by lane_eval
example : (S (.ord .lt)).lane [.fin 1, .nan (some 0x7fc00000)] = F := by lane_eval
example : (S (.ord .ge)).lane [nan, pinf] = F := by lane_eval
-- Both zeros denote `0`.
example : (S (.ord .eq)).lane [pz, nz] = T := by lane_eval
example : (S (.ord .lt)).lane [nz, pz] = F := by lane_eval
example : (S (.ord .le)).lane [pz, nz] = T := by lane_eval
example : (S (.ord .ne)).lane [pz, nz] = F := by lane_eval
-- Infinities in the extended reals.
example : (S (.ord .lt)).lane [ninf, .fin (-1000)] = T := by lane_eval
example : (S (.ord .gt)).lane [pinf, .fin 1000] = T := by lane_eval
example : (S (.ord .eq)).lane [pinf, pinf] = T := by lane_eval
example : (S (.ord .ge)).lane [ninf, ninf] = T := by lane_eval
example : (S (.ord .gt)).lane [ninf, pinf] = F := by lane_eval
example : (S (.ord .le) .f64).lane [.fin (1 / 2), .fin (1 / 3)] = F := by lane_eval
example : (S (.ord .ne) .f16).lane [.fin 2, .fin 3] = T := by lane_eval

/-! ## Table 24: unordered comparisons are true with a NaN operand -/

example : (S (.unord .eq)).lane [nan, .fin 1] = T := by lane_eval
example : (S (.unord .lt)).lane [.fin 1, nan] = T := by lane_eval
example : (S (.unord .ne)).lane [nan, nan] = T := by lane_eval
-- Without NaN they are their ordered counterparts.
example : (S (.unord .eq)).lane [pz, nz] = T := by lane_eval
example : (S (.unord .ne)).lane [pz, nz] = F := by lane_eval
example : (S (.unord .lt)).lane [.fin 2, .fin 1] = F := by lane_eval
example : (S (.unord .ge)).lane [pinf, ninf] = T := by lane_eval

/-! ## Table 25: `num` and `nan` -/

example : (S .num).lane [.fin 1, pinf] = T := by lane_eval
example : (S .num).lane [.fin 1, nan] = F := by lane_eval
example : (S .nan).lane [nz, ninf] = F := by lane_eval
example : (S .nan).lane [.fin 1, .nan (some 0x7f800001)] = T := by lane_eval

/-! ## `.ftz`, `set`, and comparisons without a floating rule -/

-- `.ftz` flushes the inputs: a subnormal equals zero.
example : { S (.ord .eq) with ftz := true }.lane [.fin (1 / 2 ^ 149), pz] = T := by lane_eval
example : (S (.ord .eq)).lane [.fin (1 / 2 ^ 149), pz] = F := by lane_eval
-- `set` gives the same comparison; one with an integer source type has no floating lane.
example : (I (.set (.ord .lt) none (.float .f32))).lane [.fin 1, .fin 2] = T := by lane_eval
example : { I (.set (.ord .lt) none (.float .f32)) with cmpTy := some (.int .s 32) }.lane
    [.fin 1, .fin 2] = none := by lane_eval
-- `lo` is an integer comparison.
example : (S (.ord .lo)).lane [.fin 1, .fin 2] = none := by lane_eval

/-! ## testp -/

private abbrev tp (p : TestProp) (v : FVal) : Option FOut := (I (.testp p)).lane [v]

example : tp .finite (.fin 1) = T := by lane_eval
example : tp .finite nz = T := by lane_eval
example : tp .finite pinf = F := by lane_eval
example : tp .finite nan = F := by lane_eval
example : tp .infinite ninf = T := by lane_eval
example : tp .infinite (.fin 1) = F := by lane_eval
example : tp .number pinf = T := by lane_eval
example : tp .number nan = F := by lane_eval
example : tp .notanumber nan = T := by lane_eval
example : tp .notanumber (.nan (some 0x7fc00000)) = T := by lane_eval
example : tp .notanumber ninf = F := by lane_eval
-- Both zeros are normal; a subnormal number is subnormal and not normal.
example : tp .normal pz = T := by lane_eval
example : tp .normal nz = T := by lane_eval
example : tp .normal (.fin (-1)) = T := by lane_eval
example : tp .normal (.fin (1 / 2 ^ 149)) = F := by lane_eval
example : tp .normal pinf = F := by lane_eval
example : tp .subnormal (.fin (-(1 / 2 ^ 149))) = T := by lane_eval
example : tp .subnormal pz = F := by lane_eval
example : tp .subnormal nan = F := by lane_eval
example : (I (.testp .subnormal) .f64).lane [.fin (1 / 2 ^ 149)] = F := by lane_eval

/-! ## copysign, neg, abs -/

-- `copysign a b` is `b` with the sign bit of `a`, for every class of `b`.
example : (I .copysign).lane [.fin (-1), .fin 2] = val (.fin (-2)) := by lane_eval
example : (I .copysign).lane [pz, .fin (-2)] = val (.fin 2) := by lane_eval
example : (I .copysign).lane [nz, pinf] = val ninf := by lane_eval
example : (I .copysign).lane [.fin 1, nz] = val pz := by lane_eval
example : (I .copysign).lane [.fin (-1), .nan (some 0x7fc00000)] =
    val (.nan (some 0xffc00000)) := by lane_eval
-- A NaN `a` with a known pattern supplies its sign bit; an opaque one has no rule unless `b`
-- is an opaque NaN.
example : (I .copysign).lane [.nan (some 0xffc00000), .fin 2] = val (.fin (-2)) := by lane_eval
example : (I .copysign).lane [nan, .fin 2] = none := by lane_eval
example : (I .copysign).lane [nan, nan] = val nan := by lane_eval
example : (I .copysign).lane [.fin 1, nan] = val nan := by lane_eval
example : (I .copysign .f64).lane [ninf, .nan (some 0x7ff8000000000000)] =
    val (.nan (some 0xfff8000000000000)) := by lane_eval
-- `neg` flips the sign: `neg(+0) = -0`; a NaN gives an opaque NaN.
example : (I .neg).lane [pz] = val nz := by lane_eval
example : (I .neg).lane [.fin 3] = val (.fin (-3)) := by lane_eval
example : (I .neg).lane [ninf] = val pinf := by lane_eval
example : (I .neg).lane [.nan (some 0x7fc00000)] = val nan := by lane_eval
example : (I .neg .f64).lane [.nan (some 0x7ff8000000000000)] = val nan := by lane_eval
example : { I .neg with ftz := true }.lane [.fin (1 / 2 ^ 149)] = val nz := by lane_eval
-- `abs` clears the sign: `abs(-∞) = +∞`; `abs.f32` of a NaN is an opaque NaN, while `abs.f64`
-- passes the NaN through.
example : (I .abs).lane [ninf] = val pinf := by lane_eval
example : (I .abs).lane [nz] = val pz := by lane_eval
example : (I .abs).lane [.fin (-3)] = val (.fin 3) := by lane_eval
example : (I .abs).lane [.nan (some 0xffc00000)] = val nan := by lane_eval
example : (I .abs .f64).lane [.nan (some 0xfff8000000000001)] =
    val (.nan (some 0xfff8000000000001)) := by lane_eval
example : (I .abs .f64).lane [nan] = val nan := by lane_eval
example : { I .abs .f16 with ftz := true }.lane [.fin (-(1 / 2 ^ 24))] = val pz := by lane_eval

end

end PTX.Tests.FloatCompare
