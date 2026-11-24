-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Thread.Local
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Numeric assumptions of the FlashMLA sparse decode kernel

Three forms have no exact-real constructor in `Core/Assumption/`:

* `mul.bf16x2` and `cvt.rn.bf16x2.f32`: Core rounds them as IEEE operations, while `Post` states
  the ideal attention; they are read as exact real operations here.
* `cvt.rn.bf16x2.ue8m0x2`: Core's `EXT-UE8M0` gives `2^(e-127)` for `1 ≤ e ≤ 254` and no value
  for `e = 0`; CUDA 13.2 reads `0` as `2^-127`, the value the quantizer can produce for a
  near-zero tile. The rule supplies that one pattern and declines every other pattern, which Core
  already handles exactly.
* `lg2.approx.ftz.f32`: `ApproxForm` has no `lg2`; the single site computes `logf(li)` of the
  row sum. The rule reads a positive finite operand as the exact `log2` and declines otherwise.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
open PTX
noncomputable section

/-- A packed pair of two bf16 reals, low half first. -/
def bf16Pair (x y : ℝ) : Value := .pair (.float .bf16 x) (.float .bf16 y)

/-- The two finite bf16 numbers in a packed register operand, including a negative zero
preserved by a widening conversion. -/
def pairValue (L : Launch) (g : Nat) (t : TState) (o : Opnd) : Option (ℝ × ℝ) :=
  match readValue L g t 32 o with
  | .ok (.pair lo hi) => do
    let x ← (valFloat .bf16 lo).toOption
    let y ← (valFloat .bf16 hi).toOption
    pure (x, y)
  | _ => none

/-- The bf16 negative-zero bits preserved by widening still select the ideal pair rule. -/
theorem pairValue_negZero_low {L : Launch} {g : Nat} {t : TState} {r : Nat} {y : ℝ}
    (hr : t.regs r = some (.pair (.bits 16 (BitVec.ofNat 64 32768)) (.float .bf16 y))) :
    pairValue L g t (.reg r) = some (0, y) := by
  have hc : classify .bf16 (.bits 16 (BitVec.ofNat 64 32768)) = .ok (.zero true) :=
    classify_bits (fmt := .bf16) (by decide) (by decide)
  have hz : valFloat .bf16 (.bits 16 (BitVec.ofNat 64 32768)) = .ok 0 := by
    rw [valFloat_of_classify (by intro f x hx; cases hx) hc]
    simp [FVal.finite, pure, Except.pure]
  simp [pairValue, readValue, readReg, hr, pure, Except.pure, hz, valFloat_float,
    Except.toOption]

/-- A positive finite f32 operand, if it is a number. -/
def f32ValueOf (L : Launch) (g : Nat) (t : TState) (o : Opnd) : Option ℝ :=
  match readValue L g t 32 o with
  | .ok v => (valFloat .f32 v).toOption
  | .error _ => none

/-- `mul.bf16x2` is the exact product of the two halves. -/
def mulBf16x2 : Assumption where
  name := "flashmla-h64-mul-bf16x2"
  statement := "The kernel dequantizes an e4m3 value by multiplying the bf16 pair of its two \
    values with the bf16 pair of their ue8m0 scales (`__hmul2`); each half of `mul.bf16x2` is \
    read as the exact real product of its two bf16 inputs, not the IEEE-rounding result."
  localRule L g t op :=
    match op with
    | .float f =>
      match f.op, f.ty, f.srcTys, f.dsts, f.srcs with
      | .mul, ⟨.bf16, 2⟩, [], [some d], [a, b] =>
        match pairValue L g t a, pairValue L g t b with
        | some (x0, x1), some (y0, y1) =>
          some (pure (next (setReg t d (bf16Pair (x0 * y0) (x1 * y1)))))
        | _, _ => none
      | _, _, _, _, _ => none
    | _ => none

/-- `cvt.rn.bf16x2.f32` packs two f32 numbers as their exact real values in bf16; the second
source is the low half (§9.7.10.24). -/
def cvtBf16x2 : Assumption where
  name := "flashmla-h64-cvt-bf16x2"
  statement := "The softmax values and the output are packed with `cvt.rn.bf16x2.f32`; each bf16 \
    result is read as the exact real value of its f32 source (the second source in the low half), \
    not the round-to-nearest bf16 result."
  localRule L g t op :=
    match op with
    | .cvt c =>
      match c.dst, c.src, c.rnd, c.srcs with
      | .packed (.float .bf16) 2, .float .f32, some .rn, [a, b] =>
        match f32ValueOf L g t a, f32ValueOf L g t b with
        | some x, some y => some (pure (next (setReg t c.d (bf16Pair y x))))
        | _, _ => none
      | _, _, _, _ => none
    | _ => none

/-- `cvt.rn.bf16x2.ue8m0x2` with the pattern `0` read as `2^-127` (CUDA 13.2); every other
pattern is left to Core's exact rule. -/
def cvtUe8m0 : Assumption where
  name := "flashmla-h64-cvt-ue8m0"
  statement := "The dequantizer converts two ue8m0 scale bytes to a bf16 pair. Byte `0` is read \
    as `2^-127` (CUDA 13.2's `cvt.rn.bf16x2.ue8m0x2`), while PTX leaves that pattern without a \
    value; every other pattern is Core's exact `2^(e-127)`, and `0xff` (NaN) is excluded by the \
    input premise."
  localRule L g t op :=
    match op with
    | .cvt c =>
      match c.dst, c.src, c.rnd, c.srcs with
      | .packed (.float .bf16) 2, .packed (.float .ue8m0) 2, some .rn, [a] =>
        match readBits L g t 16 a with
        | .ok n =>
          let b0 := n.toNat % 256
          let b1 := n.toNat / 256 % 256
          if b0 = 0 ∨ b1 = 0 then
            if b0 = 255 ∨ b1 = 255 then none
            else some (pure (next (setReg t c.d (bf16Pair (ue8m0Val b0) (ue8m0Val b1)))))
          else none
        | .error _ => none
      | _, _, _, _ => none
    | _ => none

/-- The single `lg2.approx.ftz.f32` is the exact base-2 logarithm of its positive input. -/
def lg2Exact : Assumption where
  name := "flashmla-h64-lg2"
  statement := "The kernel computes `logf(li)` of the row sum with `lg2.approx.ftz.f32`; a \
    positive finite operand is read as the exact `log2`, ignoring the approximation's ulp error \
    and the flush to zero. On a zero, negative or non-finite operand the rule declines and Core \
    applies."
  localRule L g t op :=
    match op with
    | .float f =>
      match f.op, f.mode, f.ty, f.dsts, f.srcs with
      | .lg2, .approx, ⟨.f32, 1⟩, [some d], [a] =>
        match f32ValueOf L g t a with
        | some x => if 0 < x then
            some (pure (next (setReg t d (.float .f32 (Real.log x / Real.log 2)))))
          else none
        | none => none
      | _, _, _, _, _ => none
    | _ => none

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Assumptions
