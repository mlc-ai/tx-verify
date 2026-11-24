-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Float.Ieee

@[expose] public section

/-!
# Approximate floating instructions

The special-value tables of the approximate instructions. The manual bounds their other results
only by an error, so those inputs have no rule.
-/

namespace PTX

noncomputable section

/-! ## THREAD-FLOAT-APPROX — the tables of the approximate instructions
Statement: An approximate instruction gives the result its table lists for the class of its
  operand after the `.ftz` flush, and has no rule for every input the table does not list.

Defs: ACls, ACls.of, ARes, ARes.val, ATable, rcpTable, rcpF64Table, sqrtTable, rsqrtTable,
  rsqrtF64Table, sinTable, cosTable, lg2Table, ex2Table, tanhTable, ex2Bf16Table, ex2F16Table,
  upperLayout, upperWord, approxF64, divApprox, FloatInstr.approxTable?, FloatInstr.approx

Source:
- §9.7.3.13: "Input Result -Inf -0.0 -0.0 -Inf +0.0 +Inf +Inf +0.0 NaN NaN"
- §9.7.3.14: "extract the most-significant 32 bits of .f64 operand a in 1.11.20 IEEE floating-point
    format (i.e., ignore the least-significant 32 bits of a )"
- §9.7.3.14: "tmp = a[63:32]; // upper word of a, 1.11.20 format d[63:32] = 1.0 / tmp; d[31:0] =
    0x00000000;"
- §9.7.3.14: "Input a[63:32] Result d[63:32] -Inf -0.0 -subnormal -Inf -0.0 -Inf +0.0 +Inf
    +subnormal +Inf +Inf +0.0 NaN NaN Input NaN s map to a canonical NaN with encoding
    0x7fffffff00000000"
- §9.7.3.14: "Subnormal inputs and results are flushed to sign-preserving zero."
- §9.7.3.15: "Input Result -Inf NaN -normal NaN -0.0 -0.0 +0.0 +0.0 +Inf +Inf NaN NaN"
- §9.7.3.16: "Input Result -Inf NaN -normal NaN -0.0 -Inf +0.0 +Inf +Inf +0.0 NaN NaN"
- §9.7.3.17: "tmp = a[63:32]; // upper word of a, 1.11.20 format d[63:32] = 1.0 / sqrt(tmp);
    d[31:0] = 0x00000000;"
- §9.7.3.17: "Input Result -Inf NaN -subnormal -Inf -0.0 -Inf +0.0 +Inf +subnormal +Inf +Inf +0.0
    NaN NaN Input NaN s map to a canonical NaN with encoding 0x7fffffff00000000"
- §9.7.3.18: "Input Result -Inf NaN -0.0 -0.0 +0.0 +0.0 +Inf NaN NaN NaN"
- §9.7.3.19: "Input Result -Inf NaN -0.0 +1.0 +0.0 +1.0 +Inf NaN NaN NaN"
- §9.7.3.20: "Input Result -Inf NaN -normal NaN -0.0 -Inf +0.0 -Inf +Inf +Inf NaN NaN"
- §9.7.3.21: "Input Result -Inf +0.0 -0.0 +1.0 +0.0 +1.0 +Inf +Inf NaN NaN"
- §9.7.3.22: "Input Result -Inf -1.0 -0.0 -0.0 +0.0 +0.0 +Inf 1.0 NaN NaN"
- §9.7.4.10: "Results of ex2.approx.ftz.bf16 for various corner-case inputs are as follows: Input
    Result -Inf +0.0 -subnormal +1.0 -0.0 +1.0 +0.0 +1.0 +subnormal +1.0 +Inf +Inf NaN NaN"
- §9.7.4.10: "Results of ex2.approx.f16 for various corner-case inputs are as follows: Input Result
    -Inf +0.0 -0.0 +1.0 +0.0 +1.0 +Inf +Inf NaN NaN"
- §9.7.3.8: "For 2 126 < |b| < 2 128 , if a is infinity, div.approx.f32 returns NaN , otherwise it
    returns a sign-preserving zero."
- §9.7.3.8: "div.full.f32 implements a relatively fast, full-range approximation that scales
    operands to achieve better accuracy, but is not fully IEEE 754 compliant and does not support
    rounding modifiers"
- §9.7.3: "Single-precision instructions return an unspecified NaN"

Direction: stricter

Applies: The floating instructions whose rule is THREAD-FLOAT and whose mode is `.approx`

Premises: The sources are read as data of their formats (THREAD-FLOAT).

Effect: Local evaluation. The tables are data (`ATable`), one per instruction and format, with
  the rows of the manual; a row gives a zero, an infinity, `±1.0` or NaN, and a NaN result is an
  opaque NaN. `.ftz` flushes a subnormal input to the zero of its sign before the lookup; no
  listed result is subnormal. A row the table does not list has no rule; this includes every
  finite nonzero input of `sin`, `cos`, `ex2` and `tanh`, every positive one of `rcp`, `sqrt`,
  `rsqrt` and `lg2`, and a subnormal input without `.ftz` where the table has no subnormal row.
  `rcp.approx.ftz.f64` and `rsqrt.approx.ftz.f64` look up the upper word `a[63:32]` in the 1.11.20
  layout: for a number it is the rounding toward zero of the number to that layout, for a zero or
  an infinity the same datum, and for a NaN with a known pattern the datum of its upper 32 bits. A
  NaN whose upper word is a NaN gives the NaN `0x7fffffff00000000`; a NaN whose upper word is an
  infinity (a payload in the low word only) has no rule, since its row and the NaN sentence give
  different results; an opaque NaN has no rule, since its upper word is unknown. The NaN that
  `rsqrt.approx.ftz.f64` gives for `-Inf` is an opaque NaN, since the stated encoding is for NaN
  inputs. `rsqrt.approx.f64` uses the `.f32` table with an opaque NaN. `div.approx.f32` with
  `2^126 < |b| < 2^128` gives an opaque NaN for an infinite `a`, and for a finite `a` and a
  positive `b` the zero with the sign of `a`; for a negative `b` the sign-preserving zero can have
  the sign of `a` or of the quotient, so it has no rule, and so has a NaN `a`. Every other
  `div.approx` input has no rule. `div.full` has no rule (`FloatInstr.rule`); its text gives only
  an error bound.
-/

/-- The class of an operand in an approximate table. -/
inductive ACls where
  | negInf | negNormal | negSub | negZero | posZero | posSub | posNormal | posInf | nan
  deriving DecidableEq, Repr

/-- The class of a datum of layout `L`. -/
def ACls.of (L : Layout) : FVal → ACls
  | .nan _ => .nan
  | .inf s => if s then .negInf else .posInf
  | .zero s => if s then .negZero else .posZero
  | .fin x =>
    if x < 0 then (if L.subnormal x then .negSub else .negNormal)
    else if L.subnormal x then .posSub else .posNormal

/-- A result of an approximate table: a zero, an infinity or `1.0` with its sign, or NaN. -/
inductive ARes where
  | zero (neg : Bool)
  | inf (neg : Bool)
  | one (neg : Bool)
  | nan
  deriving DecidableEq, Repr

/-- The datum of a table result; NaN is an opaque NaN. -/
def ARes.val : ARes → FVal
  | .zero s => .zero s
  | .inf s => .inf s
  | .one s => .fin (if s then -1 else 1)
  | .nan => .nan none

/-- A table: the listed classes and their results. -/
abbrev ATable := List (ACls × ARes)

/-- `rcp.approx.f32` (§9.7.3.13). -/
def rcpTable : ATable :=
  [(.negInf, .zero true), (.negZero, .inf true), (.posZero, .inf false),
    (.posInf, .zero false), (.nan, .nan)]

/-- `rcp.approx.ftz.f64` on `a[63:32]` (§9.7.3.14). -/
def rcpF64Table : ATable :=
  [(.negInf, .zero true), (.negSub, .inf true), (.negZero, .inf true), (.posZero, .inf false),
    (.posSub, .inf false), (.posInf, .zero false), (.nan, .nan)]

/-- `sqrt.approx.f32` (§9.7.3.15). -/
def sqrtTable : ATable :=
  [(.negInf, .nan), (.negNormal, .nan), (.negZero, .zero true), (.posZero, .zero false),
    (.posInf, .inf false), (.nan, .nan)]

/-- `rsqrt.approx.f32` and `rsqrt.approx.f64` (§9.7.3.16). -/
def rsqrtTable : ATable :=
  [(.negInf, .nan), (.negNormal, .nan), (.negZero, .inf true), (.posZero, .inf false),
    (.posInf, .zero false), (.nan, .nan)]

/-- `rsqrt.approx.ftz.f64` on `a[63:32]` (§9.7.3.17). -/
def rsqrtF64Table : ATable :=
  [(.negInf, .nan), (.negSub, .inf true), (.negZero, .inf true), (.posZero, .inf false),
    (.posSub, .inf false), (.posInf, .zero false), (.nan, .nan)]

/-- `sin.approx.f32` (§9.7.3.18). -/
def sinTable : ATable :=
  [(.negInf, .nan), (.negZero, .zero true), (.posZero, .zero false), (.posInf, .nan),
    (.nan, .nan)]

/-- `cos.approx.f32` (§9.7.3.19). -/
def cosTable : ATable :=
  [(.negInf, .nan), (.negZero, .one false), (.posZero, .one false), (.posInf, .nan),
    (.nan, .nan)]

/-- `lg2.approx.f32` (§9.7.3.20). -/
def lg2Table : ATable :=
  [(.negInf, .nan), (.negNormal, .nan), (.negZero, .inf true), (.posZero, .inf true),
    (.posInf, .inf false), (.nan, .nan)]

/-- `ex2.approx.f32` (§9.7.3.21). -/
def ex2Table : ATable :=
  [(.negInf, .zero false), (.negZero, .one false), (.posZero, .one false),
    (.posInf, .inf false), (.nan, .nan)]

/-- `tanh.approx` of every type (§9.7.3.22, §9.7.4.9). -/
def tanhTable : ATable :=
  [(.negInf, .one true), (.negZero, .zero true), (.posZero, .zero false),
    (.posInf, .one false), (.nan, .nan)]

/-- `ex2.approx.ftz.bf16` and `.bf16x2` (§9.7.4.10). -/
def ex2Bf16Table : ATable :=
  [(.negInf, .zero false), (.negSub, .one false), (.negZero, .one false),
    (.posZero, .one false), (.posSub, .one false), (.posInf, .inf false), (.nan, .nan)]

/-- `ex2.approx.f16` and `.f16x2` (§9.7.4.10). -/
def ex2F16Table : ATable :=
  [(.negInf, .zero false), (.negZero, .one false), (.posZero, .one false),
    (.posInf, .inf false), (.nan, .nan)]

/-- The 1.11.20 layout of the upper word of an `.f64` datum. -/
def upperLayout : Layout := .binary 11 20 true .ieee

/-- The upper word `a[63:32]` of an `.f64` datum as a datum of `upperLayout`: a number rounded
toward zero, a zero or an infinity itself, the upper 32 bits of a NaN with a known pattern; an
opaque NaN has none. -/
def upperWord : FVal → Option FVal
  | .fin x => upperLayout.round .rz .inf x false
  | .nan (some n) => upperLayout.decode (n / 2 ^ 32)
  | .nan none => none
  | v => some v

/-- `rcp.approx.ftz.f64` or `rsqrt.approx.ftz.f64` of the flushed `.f64` datum `x` with table `t`
on its upper word. A NaN input whose upper word is a NaN gives `0x7fffffff00000000`; one whose
upper word is not a NaN has no rule. A NaN row for another input is an opaque NaN. -/
def approxF64 (t : ATable) (x : FVal) : Option FVal := do
  let u ← upperWord x
  guard (x.isNaN == u.isNaN)
  match ← t.lookup (ACls.of upperLayout u) with
  | .nan => some (.nan (if x.isNaN then some 0x7fffffff00000000 else none))
  | r => some r.val

/-- `div.approx.f32` of the flushed `a` and `b`: for `2^126 < |b| < 2^128`, an opaque NaN when `a`
is an infinity and the zero with the sign of `a` when `a` is finite and `b` positive. -/
def divApprox (a b : FVal) : Option FVal :=
  match b with
  | .fin y =>
    if 2 ^ 126 < |y| ∧ |y| < 2 ^ 128 then
      match a with
      | .inf _ => some (.nan none)
      | .nan _ => none
      | _ => if 0 < y then some (.zero a.isNeg) else none
    else none
  | _ => none

/-- The table of a one-operand approximate instruction of a format other than the `.ftz.f64`
forms; `none` for a form without one. -/
def FloatInstr.approxTable? (f : FloatInstr) : Option ATable :=
  match f.op, f.ty.fmt, f.ftz with
  | .rcp, .f32, _ => some rcpTable
  | .sqrt, .f32, _ => some sqrtTable
  | .rsqrt, .f32, _ | .rsqrt, .f64, false => some rsqrtTable
  | .sin, .f32, _ => some sinTable
  | .cos, .f32, _ => some cosTable
  | .lg2, .f32, _ => some lg2Table
  | .ex2, .f32, _ => some ex2Table
  | .ex2, .bf16, true => some ex2Bf16Table
  | .ex2, .f16, false => some ex2F16Table
  | .tanh, .f32, false | .tanh, .f16, false | .tanh, .bf16, false => some tanhTable
  | _, _, _ => none

/-- The value of one lane of an approximate instruction: the table row of the flushed operand. -/
def FloatInstr.approx (f : FloatInstr) (xs : List FVal) : Option FVal :=
  match f.op, f.ty.fmt, f.ftz, f.flushIn xs with
  | .div, .f32, _, [a, b] => divApprox a b
  | .rcp, .f64, true, [a] => approxF64 rcpF64Table a
  | .rsqrt, .f64, true, [a] => approxF64 rsqrtF64Table a
  | _, _, _, [a] => do
    let t ← f.approxTable?
    let r ← t.lookup (ACls.of f.ty.fmt.layout a)
    some r.val
  | _, _, _, _ => none

end

end PTX
