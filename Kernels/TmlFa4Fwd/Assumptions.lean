-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions.Sites
public import Kernels.TmlFa4Fwd.Assumptions.Synchronization
public import Kernels.TmlFa4Fwd.Assumptions.InputReadOnly
public import Assumption.ApproxExact
public import Kernels.FlashAttn4Fwd.Assumptions.Exp2Template

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Assumptions

open PTX.Assumption
noncomputable section

/-- Score and value MMAs and the scalar and packed operations of the softmax and LSE. -/
def arithScope : IdealScope :=
  { float := [.add .f32, .mul .f32, .subRn .f32, .fma .f32, .addRnF32x2, .subRnF32x2,
      .mulF32x2, .fmaRnF32x2, .max .f32, .setp .f32, .setpInf .f32],
    mma := [.f16 .bf16 .f32] }

def idealArith : Assumption :=
  idealReal "tml-fa4-fwd-ideal-arith" arithScope
    "The BF16 QK and PV MMAs and the listed FP32 arithmetic, maximums and comparisons use \
    exact real operands and results. Floating rounding, overflow and underflow are outside \
    this model."

def approxForms : List ApproxForm := [.ex2 .f32, .rcp .f32]

def approx : Assumption :=
  approxExact "tml-fa4-fwd-approx-exp2-rcp" approxForms
    "The hardware exp2 and the final row-sum reciprocal use the exact functions on finite \
    inputs. The reciprocal's input is selected to be one when the row sum is zero. Core's \
    tables still handle nonfinite inputs, including exp2(-infinity) = +0."

/-- `lg2.approx.ftz.f32 d, a` with the plain scalar register form used by the two LSE stores. -/
def lg2Operands : Op → Option (Nat × Opnd)
  | .float f =>
    match f.op, f.dsts, f.srcs with
    | .lg2, [some d], [a@(.reg _)] =>
      if f.ty == ⟨.f32, 1⟩ && f.mode == .approx && f.ftz && f.srcTys.isEmpty
          && f.cmpTy.isNone && f.rnd.isNone && !f.sat && !f.relu && !f.oob
          && !f.nanMod && !f.xorsign && !f.absMod then
        some (d, a)
      else none
    | _, _, _ => none
  | _ => none

/-- Give the LSE logarithm its exact meaning for positive finite operands. Core handles zero,
negative and nonfinite operands. -/
def lg2 : Assumption where
  name := "tml-fa4-fwd-approx-lg2"
  statement := s!"At pc {siteText lg2Sites}, lg2.approx.ftz.f32 on a positive finite \
    value x gives the exact logb 2 x, ignoring approximation error and flush to zero. \
    Other inputs use Core's rule, including lg2(0) = -infinity."
  localRule _ _ t op := do
    let (d, a) ← lg2Operands op
    if !lg2Sites.contains t.pc then none else
      bindRead (readFinite t .f32 a) fun x =>
        if 0 < x then some (pure (next (setReg t d (.float .f32 (Real.logb 2 x))))) else none

/-- `cvt.f32.bf16` in the bias load path. -/
def biasWidenOperands : Op → Option (Nat × Opnd)
  | .cvt c =>
    match c.dst, c.src, c.rnd, c.srcs with
    | .float .f32, .float .bf16, none, [a@(.reg _)] =>
      if c.plain && c.ext == .same then some (c.d, a) else none
    | _, _, _, _ => none
  | _ => none

/-- `cvt.rn.bf16x2.f32` in the probability store path. -/
def probPackOperands : Op → Option (Nat × Opnd × Opnd)
  | .cvt c =>
    match c.dst, c.src, c.rnd, c.srcs with
    | .packed (.float .bf16) 2, .float .f32, some .rn, [a@(.reg _), b@(.reg _)] =>
      if c.plain && c.ext == .same then some (c.d, a, b) else none
    | _, _, _, _ => none
  | _ => none

def bf16Convert : Assumption where
  name := "tml-fa4-fwd-bf16-convert"
  statement := s!"At pc {siteText biasWidenSites}, cvt.f32.bf16 preserves each finite BF16 \
    real payload supplied by the bias tensor. At pc {siteText probPackSites}, cvt.rn.bf16x2.f32 \
    stores the two finite real probabilities without BF16 rounding, with the first source in \
    the high half and the second in the low half. Other operands use Core's conversion rules, \
    including widening a BF16 negative infinity to FP32 negative infinity."
  localRule _ _ t op :=
    if let some (d, a) := biasWidenOperands op then
      if !biasWidenSites.contains t.pc then none else
        bindRead (readFinite t .bf16 a) fun x =>
          some (pure (next (setReg t d (.float .f32 x))))
    else do
      let (d, a, b) ← probPackOperands op
      if !probPackSites.contains t.pc then none else
        bindRead (readFinite t .f32 a) fun x => bindRead (readFinite t .f32 b) fun y =>
          some (pure (next (setReg t d (.pair (.float .bf16 y) (.float .bf16 x)))))

/-- The exponent of a finite input, or zero for the exact negative-infinity encoding.
The clamp sends that encoding to -127, giving zero fractional part and a polynomial value of
one. The encoded exponent then cancels the exponent bits of one. -/
def swExp2Lane (v : Value) : Exec ℝ :=
  match v with
  | .float .f32 x => pure (cuteExp2.fn x)
  | _ => do
    let x ← classify .f32 v
    match x with
    | .inf true => pure 0
    | _ => cuteExp2.fn <$> x.finite

@[simp]
theorem swExp2Lane_negInf :
    swExp2Lane (.bits 32 (BitVec.ofNat 64 0xFF800000)) = .ok 0 := by
  have h := classify_bits (fmt := .f32) (n := 0xFF800000) (x := .inf true)
    (by decide) (by decide)
  change (classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000)) >>= _) = _
  change classify .f32 (.bits 32 (BitVec.ofNat 64 0xFF800000)) = .ok (.inf true) at h
  rw [h]
  rfl

open Classical in
/-- The `execSegment` register effect with a lane reader that also accepts the mask encoding. -/
def execSwExp2 (m : SegMatch CuteSlot) (t : TState) : Exec TState := do
  let reg := fun slot => (m.reg.lookup slot).getD 0
  unless m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (reg p.1) = some p.2 do
    throw .badValue
  let outs ← m.shape.io.mapM fun (input, output) => do
    let x ← swExp2Lane (← readReg t (reg input))
    pure (reg output, Value.float .f32 x)
  let cleared := m.shape.writes.foldl (fun rs slot => Function.update rs (reg slot) none) t.regs
  let consts := if m.shape.defines then
      m.shape.consts.foldl (fun rs (slot, v) => Function.update rs (reg slot) (some v)) cleared
    else cleared
  let regs := outs.foldl (fun rs (d, v) => Function.update rs d (some v)) consts
  pure { t with regs := regs, pc := m.stop, sub := 0, acc := [] }

/-- The FA4 software exp2 template in the biased and unbiased loops. The biased loop can
include padding rows, whose packed bias columns can contain negative infinity. -/
def swExp2 : Assumption :=
  { segmentExact kernel "tml-fa4-fwd-sw-exp2" cuteExp2 swExp2Sites
      "At the matched template sites, a lane whose input is the FP32 negative infinity \
      encoding produces zero. This is the bit result of the clamp and exponent construction, \
      and covers masked bias on padding rows." with
    segmentRule := fun _ _ t =>
      if swExp2Sites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
        (cuteExp2.matchAt kernel t.pc).map fun m => execSwExp2 m t
      else none }

/-- The numerical assumptions selected for the frozen specialization. -/
def numeric : List Assumption := [idealArith, approx, lg2, bf16Convert, swExp2]

/-- The numerical, synchronization and read-only input assumptions of the frozen
specialization. -/
def all : List Assumption := numeric ++ synchronization ++ [inputReadOnly]

end
end PTX.Kernels.TmlFa4Fwd.Assumptions
