-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Assumption constructor `approxExact`

A kernel declares an approximate-as-exact assumption with `Assumption.approxExact`, naming
exactly the approximate instruction forms its proof reads as their exact functions. This file
is not itself an assumption.
-/

namespace PTX.Assumption
noncomputable section

/-! ## ASM-APPROX — approximate instructions read as exact, for the forms a kernel names
Statement: For the approximate instruction forms a kernel names (`div.approx`, `rsqrt.approx`,
  `ex2.approx`, `rcp.approx`), the model takes each result to be the exact real value of the
  function the instruction approximates, ignoring its error bound and the flushing of tiny results
  to zero, for finite operands. A divisor of zero or a `rsqrt` argument that is not positive is
  undefined behaviour, and an infinite or NaN operand takes the Core rule.

Defs: Assumption.ApproxForm, Assumption.ApproxForm.ofOp, Assumption.ApproxForm.text,
  Assumption.readFinite, Assumption.execApproxExact, Assumption.approxExact

Source:
- §9.7.3.8 (div.approx.f32: bounded ulp error)
- §9.7.3.16 (rsqrt.approx.f32: bounded relative error)
- §9.7.3.21 (ex2): "Raise 2 to the power a ."
- §9.7.3.21 (ex2): "The maximum ulp error is 2 ulp from correctly rounded result across the full
    range of inputs."
- §9.7.3.21 (ex2): "ex2.ftz.f32 flushes subnormal inputs and results to sign-preserving zero."
- §9.7.3.13 (rcp): "Compute 1/a , store result in d ."
- §9.7.3.13 (rcp): "The maximum ulp error is 1 across the full range of inputs."

Direction: not-conservative

Effect: The core gives these approximations only the special values of their tables
  (THREAD-FLOAT-APPROX). `approxExact name forms why` gives each form listed in `forms` one exact
  real value on finite operands, through the field `localRule`, which is consulted before the Core
  rule (THREAD-LOCAL): `div.approx` the exact real `a / b`, `rsqrt.approx` the exact `1 / sqrt a`,
  `ex2.approx` the exact `2 ^ a` (`Real.rpow`) and `rcp.approx` the exact `1 / a`. The result is
  undefined unless the divisor of `div` and `rcp` is nonzero and the `rsqrt` argument positive, so
  the ideal result exists; this is stricter than the Core table, which gives `rcp(±0) = ±∞`. On an
  infinite or NaN operand the rule declines and the Core table gives the result (`ex2(-∞) = +0`).
  The constructor sets no `wf` and no `ub`. The statement is generated from the forms and lists
  every form it covers.

Review: This is ASM-IDEAL extended to approximate instructions, so it is not conservative in the
  same way (OPEN-NUM). The ulp error of the instruction is ignored. With `.ftz`, a result below
  the smallest normal number, which the hardware flushes to zero (`2 ^ a` for `a` below about
  -126), is the exact positive value.
-/

/-- A decoded approximate instruction form. -/
inductive ApproxForm where
  /-- `div.approx{.ftz}.<fmt>` -/
  | div (fmt : FloatFmt)
  /-- `rsqrt.approx{.ftz}.<fmt>` -/
  | rsqrt (fmt : FloatFmt)
  /-- `ex2.approx{.ftz}.<fmt>` -/
  | ex2 (fmt : FloatFmt)
  /-- `rcp.approx{.ftz}.<fmt>` -/
  | rcp (fmt : FloatFmt)
  deriving DecidableEq, Repr

/-- The `ApproxForm` of a decoded instruction: `div`, `rsqrt`, `ex2` or `rcp` with `.approx` of a
scalar format. -/
def ApproxForm.ofOp : Op → Option ApproxForm
  | .float f =>
    if f.mode == .approx && f.ty.lanes == 1 then
      match f.op with
      | .div => some (.div f.ty.fmt)
      | .rsqrt => some (.rsqrt f.ty.fmt)
      | .ex2 => some (.ex2 f.ty.fmt)
      | .rcp => some (.rcp f.ty.fmt)
      | _ => none
    else none
  | _ => none

def ApproxForm.text : ApproxForm → String
  | .div fmt => s!"div.approx\{.ftz}.{floatFmtText fmt} as the exact a / b"
  | .rsqrt fmt => s!"rsqrt.approx\{.ftz}.{floatFmtText fmt} as the exact 1 / sqrt a"
  | .ex2 fmt => s!"ex2.approx\{.ftz}.{floatFmtText fmt} as the exact 2 ^ a (no ulp error; a \
    result .ftz flushes to zero is the exact positive value)"
  | .rcp fmt => s!"rcp.approx\{.ftz}.{floatFmtText fmt} as the exact 1 / a, undefined at 0 \
    (no ulp error)"

/-- A finite operand of an approximate form as a real (`readERealOpnd`); `none` (decline) for an
infinite or NaN operand. -/
def readFinite (t : TState) (fmt : FloatFmt) (o : Opnd) : Option (Exec ℝ) :=
  bindRead (readERealOpnd t fmt o) fun x =>
    if x = ⊤ ∨ x = ⊥ then none else some (pure x.toReal)

/-- The exact functions of the approximate instructions on finite operands; `none` (the Core rule
applies) when an operand is infinite or NaN. -/
def execApproxExact (t : TState) : Op → Option (Exec TState)
  | .float f =>
    let fmt := f.ty.fmt
    match f.op, f.dsts, f.srcs with
    | .div, [some d], [a, b] =>
      bindRead (readFinite t fmt a) fun x => bindRead (readFinite t fmt b) fun y =>
        some (if y = 0 then throw .badValue else pure (next (setReg t d (.float fmt (x / y)))))
    | .rsqrt, [some d], [a] => bindRead (readFinite t fmt a) fun x =>
      some (if x ≤ 0 then throw .badValue
        else pure (next (setReg t d (.float fmt (1 / Real.sqrt x)))))
    | .ex2, [some d], [a] => bindRead (readFinite t fmt a) fun x =>
      some (pure (next (setReg t d (.float fmt (Real.rpow 2 x)))))
    | .rcp, [some d], [a] => bindRead (readFinite t fmt a) fun x =>
      some (if x = 0 then throw .badValue else pure (next (setReg t d (.float fmt (1 / x)))))
    | _, _, _ => some (throw .noRule)
  | _ => some (throw .noRule)

/-- Read exactly the approximate forms in `forms` as their exact functions; `why` says why the
kernel needs it. -/
def approxExact (name : String) (forms : List ApproxForm) (why : String) : Assumption where
  name := name
  statement := s!"Read as exact real functions, for exactly these forms: \
    {", ".intercalate (forms.map ApproxForm.text)}. {why}"
  localRule _ _ t op := match ApproxForm.ofOp op with
    | some f => if f ∈ forms then execApproxExact t op else none
    | none => none

end
end PTX.Assumption
