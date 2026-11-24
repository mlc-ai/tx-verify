-- SPDX-License-Identifier: Apache-2.0
module

public import Assumption.IdealReal
public import Assumption.ApproxExact
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Numeric readings of the Inkling relative decode kernel

Forms of the program that neither `idealReal` nor `approxExact` covers, each limited to the
instructions that need it. Every one reads an instruction as an exact real function of its
operands, so that the theorem can state the exact attention; the hardware's rounding and
approximation error is the separate numerical question OPEN-NUM leaves open.

- `lg2.approx.ftz.f32` (PTX 2562, the log2 of the row sum, `_gl_lg2`, `attention.py:537-541`) as
  the exact `log2`. `approxExact`'s forms do not include `lg2`.
- `div.full.f32` (PTX 600, `1 / softmax_scale`, `attention.py:749`) as the exact quotient. Core
  gives `div.full` no rule.
- `neg.f32` (PTX 807, `-scale_log2`) as the exact negation of a real. Core's rule reads the
  operand through its bit pattern, which rounds a real that `mul.f32` produced exactly, so the two
  `scale_log2` factors of `fma(s, scale_log2, -(m · scale_log2))` would differ.
- `cvt.f32.bf16` (the 64 bias widenings) and `cvt.rn.bf16x2.f32` (the 32 packs of `P`) as exact:
  the widening keeps the number, the pack keeps both numbers as `bf16` payloads. `FloatForm` has
  only the `f16` pair of these.
-/

namespace PTX.Kernels.InklingRelDecode.Assumptions
open PTX PTX.Assumption

/-- The sites of the single-instruction readings. -/
def lg2Sites : List Nat := [2562]
def divFullSites : List Nat := [600]
def negSites : List Nat := [807]

/-- `lg2.approx.ftz.f32` at a listed site is the exact `log2` of a finite positive operand. Zero,
a negative operand and the infinities take Core's rule (the row sum of an empty row is zero, its
logarithm is discarded). -/
noncomputable def lg2Exact : Assumption where
  name := "inkling-lg2"
  statement := "`lg2.approx.ftz.f32` at PTX 2562 is read as the exact log2 of a finite positive \
    operand (§9.7.3.20: \"lg2.approx.f32 implements a fast approximation to log 2 (a).\"; \"For \
    positive finite inputs outside of this interval, maximum relative error is 2 -22 .\"), \
    ignoring its error and the flush of subnormals. A zero, negative or infinite operand takes \
    Core's rule."
  localRule _ _ t op :=
    if lg2Sites.contains t.pc then
      match op with
      | .float f =>
        match f.op, f.mode, f.ty, f.dsts, f.srcs with
        | .lg2, .approx, ⟨.f32, 1⟩, [some d], [a] =>
          bindRead (readERealOpnd t .f32 a) fun x =>
            if 0 < x ∧ x ≠ ⊤ then
              some (pure (next (setReg t d (.float .f32 (Real.logb 2 x.toReal)))))
            else none
        | _, _, _, _, _ => none
      | _ => none
    else none

/-- `div.full.f32` at a listed site is the exact quotient of finite operands; a zero divisor is
undefined behaviour. -/
noncomputable def divFullExact : Assumption where
  name := "inkling-div-full"
  statement := "`div.full.f32` at PTX 600 is read as the exact quotient a / b of finite operands \
    (§9.7.3.8: \"div.full.f32 implements a relatively fast, full-range approximation that scales \
    operands to achieve better accuracy, but is not fully IEEE 754 compliant and does not \
    support rounding modifiers. The maximum ulp error is 2 across the full range of inputs.\"), \
    ignoring its error; a zero divisor is undefined behaviour and an infinite or NaN operand \
    takes Core's rule."
  localRule _ _ t op :=
    if divFullSites.contains t.pc then
      match op with
      | .float f =>
        match f.op, f.mode, f.ty, f.dsts, f.srcs with
        | .div, .full, ⟨.f32, 1⟩, [some d], [a, b] =>
          bindRead (readFinite t .f32 a) fun x => bindRead (readFinite t .f32 b) fun y =>
            some (if y = 0 then throw .badValue
              else pure (next (setReg t d (.float .f32 (x / y)))))
        | _, _, _, _, _ => none
      | _ => none
    else none

/-- `neg.f32` at a listed site is the exact negation of its operand. -/
noncomputable def negExact : Assumption where
  name := "inkling-neg"
  statement := "`neg.f32` at PTX 807 is read as the exact negation of its operand, an infinity \
    as the opposite infinity; a NaN operand takes Core's rule."
  localRule _ _ t op :=
    if negSites.contains t.pc then
      match op with
      | .float f =>
        match f.op, f.ty, f.dsts, f.srcs with
        | .neg, ⟨.f32, 1⟩, [some d], [a] =>
          bindRead (readERealOpnd t .f32 a) fun x =>
            some (pure (next (setReg t d (erealValue .f32 (-x)))))
        | _, _, _, _ => none
      | _ => none
    else none

/-- `cvt.f32.bf16` and `cvt.rn.bf16x2.f32` without other qualifiers, read as exact. -/
noncomputable def bf16Exact : Assumption where
  name := "inkling-bf16-exact"
  statement := "`cvt.f32.bf16` and `cvt.rn.bf16x2.f32` (no `.ftz`, `.sat`, `.relu` or other \
    qualifier) are read as exact: the widening keeps the number of its bf16 operand, and the \
    pack keeps the numbers of its two f32 operands as the two bf16 halves (a to the upper half, \
    b to the lower) without rounding them to bf16, so that the theorem states the exact \
    attention. The kernel rounds the probabilities `P` to bf16 before `O += P V`; the rounding \
    error is part of the hardware's numerical error that the theorem does not model."
  localRule _ _ t op :=
    match op with
    | .cvt c =>
      match c.dst, c.src, c.rnd, c.srcs with
      | .float .f32, .float .bf16, none, [a] =>
        if c.plain then
          bindRead (readERealOpnd t .bf16 a) fun x =>
            some (pure (next (setReg t c.d (erealValue .f32 x))))
        else none
      | .packed (.float .bf16) 2, .float .f32, some .rn, [a, b] =>
        if c.plain then
          bindRead (readERealOpnd t .f32 a) fun x => bindRead (readERealOpnd t .f32 b) fun y =>
            some (pure (next (setReg t c.d (.pair (erealValue .bf16 y) (erealValue .bf16 x)))))
        else none
      | _, _, _, _ => none
    | _ => none

end PTX.Kernels.InklingRelDecode.Assumptions
