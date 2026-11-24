-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Assumption.IdealReal
public import Assumption.ApproxExact
public import Tests.Float.FloatExec

/-! The floating forms the assumptions name, in their FA4 spellings: `sub.f32`, `add`, `sub`,
`fma` of `.f32x2` (§9.7.3.3, §9.7.3.4, §9.7.3.6), two- and three-input `max`/`min` (§9.7.3.11,
§9.7.3.12), floating `setp` (§9.7.7.2, §9.3.1.2), `ex2.approx` (§9.7.3.21) and `rcp.approx`
(§9.7.3.13). Each decodes to `Op.float`; the 18 `FloatForm` and `ApproxForm` names are the image
of their spellings and not of their neighbours (`.sat`, a mixed source type, `.NaN`, `num`, a
`BoolOp`, `mad`, `rcp.rn`). Under `idealReal` and `approxExact` a finite operand gives the exact
real result; a NaN, `∞ - ∞` and `0 · ∞` decline, and the Core rule (THREAD-FLOAT, THREAD-CVT)
gives the instruction its result in every case that a scope leaves out: directed rounding
(`add.rm.f32x2`, `sub.rz.f32`), `setp` with an infinite constant outside `setpInf`, and the
approximations on an infinite operand. -/
namespace PTX.Tests.FloatForms
noncomputable section

set_option linter.unusedSimpArgs false

private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 4, 32⟩, ⟨"%rd".toList, 4, 64⟩, ⟨"%p".toList, 1, 1⟩,
      ⟨"%rs".toList, 4, 16⟩], labels := [], params := [] }
-- ids: %r0..%r3 = 0..3, %rd0..%rd3 = 4..7, %p0 = 8, %rs0..%rs3 = 9..12
private def r (n : String) : Syntax.Operand := .register n

private def f32 : FTy := { fmt := .f32 }
private def f32x2 : FTy := { fmt := .f32, lanes := 2 }

/-- A decoded floating instruction. -/
private def fl (op : FOp) (ty : FTy) (dsts : List (Option Nat)) (srcs : List Opnd)
    (rnd : Option FloatRound := none) (mode : FMode := .ieee) (ftz : Bool := false) : Op :=
  .float { op, ty, rnd, mode, ftz, dsts, srcs }

/-! ## Decoding -/

example : Decode.op env "sub.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (fl .sub f32 [some 0] [.reg 1, .reg 2]) := rfl
example : Decode.op env "sub.rz.ftz.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (fl .sub f32 [some 0] [.reg 1, .reg 2] (some .rz) (ftz := true)) := rfl
example : Decode.op env "add.rn.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (fl .add f32x2 [some 4] [.reg 5, .reg 6] (some .rn)) := rfl
example : Decode.op env "add.rm.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (fl .add f32x2 [some 4] [.reg 5, .reg 6] (some .rm)) := rfl
example : Decode.op env "add.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (fl .add f32x2 [some 4] [.reg 5, .reg 6]) := rfl
example : Decode.op env "sub.rn.f32x2" [r "%rd0", r "%rd1", r "%rd2"] =
    .ok (fl .sub f32x2 [some 4] [.reg 5, .reg 6] (some .rn)) := rfl
example : Decode.op env "fma.rn.f32x2" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"] =
    .ok (fl .fma f32x2 [some 4] [.reg 5, .reg 6, .reg 7] (some .rn)) := rfl
example : Decode.op env "max.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (fl .max f32 [some 0] [.reg 1, .reg 2]) := rfl
example : Decode.op env "max.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (fl .max f32 [some 0] [.reg 1, .reg 2, .reg 3]) := rfl
example : Decode.op env "min.ftz.f32" [r "%r0", r "%r1", .literal "0f00000000"] =
    .ok (fl .min f32 [some 0] [.reg 1, .f32imm 0] (ftz := true)) := rfl
example : Decode.op env "setp.neu.f32" [r "%p0", r "%r1", .literal "0fFF800000"] =
    .ok (fl (.setp (.unord .ne) none) f32 [some 8] [.reg 1, .f32imm 0xFF800000]) := rfl
example : Decode.op env "setp.ge.f32" [r "%p0", r "%r1", .literal "0fC1000000"] =
    .ok (fl (.setp (.ord .ge) none) f32 [some 8] [.reg 1, .f32imm 0xC1000000]) := rfl
example : Decode.op env "setp.lt.f32" [r "%p0", r "%r1", r "%r2"] =
    .ok (fl (.setp (.ord .lt) none) f32 [some 8] [.reg 1, .reg 2]) := rfl
example : Decode.op env "setp.ne.f32" [r "%p0", r "%r1", .literal "0f00000000"] =
    .ok (fl (.setp (.ord .ne) none) f32 [some 8] [.reg 1, .f32imm 0]) := rfl
example : Decode.op env "ex2.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (fl .ex2 f32 [some 0] [.reg 1] (mode := .approx) (ftz := true)) := rfl
example : Decode.op env "rcp.approx.ftz.f32" [r "%r0", r "%r1"] =
    .ok (fl .rcp f32 [some 0] [.reg 1] (mode := .approx) (ftz := true)) := rfl
-- The integer forms of the same opcodes are unchanged.
example : Decode.op env "sub.s32" [r "%r0", r "%r1", .literal "1"] =
    .ok (.int ⟨.sub, .int .s 32, false, [some 0], [.reg 1, .imm 1]⟩) := rfl
example : Decode.op env "setp.ne.s32" [r "%p0", r "%r1", .literal "0"] =
    .ok (.int ⟨.setp .ne none, .int .s 32, false, [some 8], [.reg 1, .imm 0]⟩) := rfl

-- Rejected: `fma` without a rounding modifier (§9.7.3.6: "no default"), four sources,
-- a `.ftz` integer `setp`, `ex2.approx.f64`, and an integer constant at a floating type
-- (Table 26).
example : (Decode.op env "fma.f32x2" [r "%rd0", r "%rd1", r "%rd2", r "%rd3"]).isOk = false :=
  rfl
example : (Decode.op env "max.f32" [r "%r0", r "%r1", r "%r2", r "%r3", r "%r0"]).isOk =
    false := rfl
example : (Decode.op env "setp.ne.ftz.s32" [r "%p0", r "%r1", r "%r2"]).isOk = false := rfl
example : (Decode.op env "ex2.approx.f64" [r "%rd0", r "%rd1"]).isOk = false := rfl
example : (Decode.op env "sub.f32" [r "%r0", r "%r1", .literal "1"]).isOk = false := rfl
example : (Decode.op env "max.f32" [r "%r0", r "%r1", .literal "0"]).isOk = false := rfl

-- Valid PTX that the assumptions do not name decodes to `Op.float` as well.
example : Decode.op env "sub.sat.f32" [r "%r0", r "%r1", r "%r2"] =
    .ok (.float
      { op := .sub, ty := f32, sat := true, dsts := [some 0], srcs := [.reg 1, .reg 2] }) :=
  rfl
example : Decode.op env "mad.rn.f32" [r "%r0", r "%r1", r "%r2", r "%r3"] =
    .ok (fl .mad f32 [some 0] [.reg 1, .reg 2, .reg 3] (some .rn)) := rfl
example : Decode.op env "rcp.rn.f32" [r "%r0", r "%r1"] =
    .ok (fl .rcp f32 [some 0] [.reg 1] (some .rn)) := rfl

/-! ## The 18 names -/

open Assumption in
/-- The `FloatForm` of a spelling. -/
private def form (s : String) (a : List Syntax.Operand) : Option FloatForm :=
  (Decode.op env s a).toOption.bind FloatForm.ofOp

open Assumption in
/-- The `ApproxForm` of a spelling. -/
private def aform (s : String) (a : List Syntax.Operand) : Option ApproxForm :=
  (Decode.op env s a).toOption.bind ApproxForm.ofOp

open Assumption

private def a3 : List Syntax.Operand := [r "%r0", r "%r1", r "%r2"]
private def a4 : List Syntax.Operand := [r "%r0", r "%r1", r "%r2", r "%r3"]
private def d3 : List Syntax.Operand := [r "%rd0", r "%rd1", r "%rd2"]
private def d4 : List Syntax.Operand := [r "%rd0", r "%rd1", r "%rd2", r "%rd3"]
private def a2 : List Syntax.Operand := [r "%r0", r "%r1"]

-- `add`, `mul`, `fma` of a scalar: every rounding modifier, written or not.
example : form "add.rn.f32" a3 = some (.add .f32) := rfl
example : form "add.rm.f32" a3 = some (.add .f32) := rfl
example : form "add.f32" a3 = some (.add .f32) := rfl
example : form "add.sat.f32" a3 = none := rfl
example : form "add.f32.f16" [r "%r0", r "%rs0", r "%r1"] = none := rfl
example : form "add.f32x2.f16x2.f32x2" [r "%rd0", r "%r1", r "%rd1"] = none := rfl
example : form "mul.rn.f32" a3 = some (.mul .f32) := rfl
example : form "mul.f32" a3 = some (.mul .f32) := rfl
example : form "mul.sat.f32" a3 = none := rfl
example : form "fma.rn.f32" a4 = some (.fma .f32) := rfl
example : form "fma.rz.f32" a4 = some (.fma .f32) := rfl
example : form "fma.rn.sat.f32" a4 = none := rfl
example : form "mad.rn.f32" a4 = none := rfl
-- `mul.f32x2`
example : form "mul.f32x2" d3 = some .mulF32x2 := rfl
example : form "mul.rz.f32x2" d3 = some .mulF32x2 := rfl
-- `sub`, `add`, `sub`, `fma` of `.f32x2` keep `.rn` only.
example : form "sub.f32" a3 = some (.subRn .f32) := rfl
example : form "sub.rn.f32" a3 = some (.subRn .f32) := rfl
example : form "sub.rn.ftz.f32" a3 = some (.subRn .f32) := rfl
example : form "sub.rz.f32" a3 = none := rfl
example : form "sub.sat.f32" a3 = none := rfl
example : form "add.rn.f32x2" d3 = some .addRnF32x2 := rfl
example : form "add.f32x2" d3 = some .addRnF32x2 := rfl
example : form "add.rm.f32x2" d3 = none := rfl
example : form "sub.rn.f32x2" d3 = some .subRnF32x2 := rfl
example : form "sub.f32x2" d3 = some .subRnF32x2 := rfl
example : form "sub.rm.f32x2" d3 = none := rfl
example : form "fma.rn.f32x2" d4 = some .fmaRnF32x2 := rfl
example : form "fma.rz.f32x2" d4 = none := rfl
-- `min` and `max` of two or three sources.
example : form "max.f32" a3 = some (.max .f32) := rfl
example : form "max.f32" a4 = some (.max .f32) := rfl
example : form "max.ftz.f32" a3 = some (.max .f32) := rfl
example : form "min.f32" a3 = some (.min .f32) := rfl
example : form "max.NaN.f32" a3 = none := rfl
example : form "max.abs.f32" a4 = none := rfl
example : form "max.xorsign.abs.f32" a3 = none := rfl
-- `setp`, with an infinite constant operand a form of its own.
example : form "setp.lt.f32" [r "%p0", r "%r1", r "%r2"] = some (.setp .f32) := rfl
example : form "setp.neu.f32" [r "%p0", r "%r1", r "%r2"] = some (.setp .f32) := rfl
example : form "setp.ne.f32" [r "%p0", r "%r1", .literal "0f00000000"] = some (.setp .f32) := rfl
example : form "setp.neu.f32" [r "%p0", r "%r1", .literal "0fFF800000"] = some (.setpInf .f32) :=
  rfl
example : form "setp.lt.f32" [r "%p0", r "%r1", .literal "0f7F800000"] = some (.setpInf .f32) :=
  rfl
example : form "setp.num.f32" [r "%p0", r "%r1", r "%r2"] = none := rfl
example : form "setp.lt.and.f32" [r "%p0", r "%r1", r "%r2", r "%p0"] = none := rfl
example : form "setp.lt.f32" [.pair [r "%p0", .sink], r "%r1", r "%r2"] = none := rfl
-- `cvt`.
example : form "cvt.f32.f16" [r "%r0", r "%rs1"] = some .cvtF32F16 := rfl
example : form "cvt.f32.bf16" [r "%r0", r "%rs1"] = none := rfl
example : form "cvt.rn.f16x2.f32" [r "%r0", r "%r1", r "%r2"] = some .cvtRnF16x2F32 := rfl
example : form "cvt.rn.f16.f32" [r "%rs0", r "%r1"] = none := rfl
-- The approximations.
example : aform "div.approx.f32" a3 = some (.div .f32) := rfl
example : aform "div.rn.f32" a3 = none := rfl
example : aform "rsqrt.approx.ftz.f32" a2 = some (.rsqrt .f32) := rfl
example : aform "sqrt.rn.f32" a2 = none := rfl
example : aform "ex2.approx.ftz.f32" a2 = some (.ex2 .f32) := rfl
example : aform "ex2.approx.f32" a2 = some (.ex2 .f32) := rfl
example : aform "ex2.approx.f16x2" a2 = none := rfl
example : aform "rcp.approx.ftz.f32" a2 = some (.rcp .f32) := rfl
example : aform "rcp.rn.f32" a2 = none := rfl
-- A floating form is no approximate form and the converse.
example : aform "sub.f32" a3 = none := rfl
example : form "ex2.approx.f32" a2 = none := rfl

/-! ## Meaning under `idealReal` and `approxExact`

A finite operand gives the exact real result. The assumption rule is selected once by a lemma
(`viaIdeal`, `viaApprox`) and the instruction is then evaluated by `Assumption.execIdealFloat` and
`Assumption.execApproxExact`. -/

/-- Every named form, and `mul.f32x2`, as exact real arithmetic. -/
private def ideal : Assumption :=
  Assumption.idealReal "test-ideal-float-forms"
    { float := [.subRn .f32, .addRnF32x2, .subRnF32x2, .fmaRnF32x2, .mulF32x2, .min .f32,
      .max .f32, .setp .f32] } "test"
/-- Only `add.rn.f32x2`. -/
private def idealAdd2 : Assumption :=
  Assumption.idealReal "test-ideal-add-f32x2" { float := [.addRnF32x2] } "test"
/-- `add{.rnd}.f32` and `mul{.rnd}.f32`. -/
private def idealAdd : Assumption :=
  Assumption.idealReal "test-ideal-add-f32" { float := [.add .f32] } "test"
private def idealMul : Assumption :=
  Assumption.idealReal "test-ideal-mul-f32" { float := [.mul .f32] } "test"
/-- Comparisons with an infinite constant. -/
private def idealInf : Assumption :=
  Assumption.idealReal "test-ideal-setp-inf" { float := [.setpInf .f32] } "test"
/-- `cvt.f32.f16`. -/
private def idealCvt : Assumption :=
  Assumption.idealReal "test-ideal-cvt" { float := [.cvtF32F16] } "test"
/-- `ex2.approx.f32` and `rcp.approx.f32` as exact functions. -/
private def exact : Assumption := Assumption.approxExact "test" [.ex2 .f32, .rcp .f32] ""

/-- A thread state holding the given registers. -/
private def mk : List (Nat × Value) → TState
  | [] => {}
  | (r, v) :: rest => setReg (mk rest) r v

private def launch : Launch := { grid := 1, block := 1, params := fun _ => none }
private def scalars (x y z : ℝ) : TState :=
  { regs := fun r => if r = 1 then some (.float .f32 x) else if r = 2 then some (.float .f32 y)
    else if r = 3 then some (.float .f32 z) else none }
private def pairs (x0 x1 y0 y1 z0 z1 : ℝ) : TState :=
  { regs := fun r =>
    if r = 5 then some (.pair (.float .f32 x0) (.float .f32 x1))
    else if r = 6 then some (.pair (.float .f32 y0) (.float .f32 y1))
    else if r = 7 then some (.pair (.float .f32 z0) (.float .f32 z1)) else none }

private theorem coe_max (x y : ℝ) : max (x : EReal) y = ((max x y : ℝ) : EReal) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.2 h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.2 h)]
private theorem coe_min (x y : ℝ) : min (x : EReal) y = ((min x y : ℝ) : EReal) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (EReal.coe_le_coe_iff.2 h)]
  · rw [min_eq_right h, min_eq_right (EReal.coe_le_coe_iff.2 h)]

private def sub1 : Op := fl .sub f32 [some 0] [.reg 1, .reg 2]
private def add2 : Op := fl .add f32x2 [some 4] [.reg 5, .reg 6] (some .rn)
private def sub2 : Op := fl .sub f32x2 [some 4] [.reg 5, .reg 6] (some .rn)
private def fma2 : Op := fl .fma f32x2 [some 4] [.reg 5, .reg 6, .reg 7] (some .rn)
private def mul2 : Op := fl .mul f32x2 [some 4] [.reg 5, .reg 6]
private def max2 : Op := fl .max f32 [some 0] [.reg 1, .reg 2]
private def max3 : Op := fl .max f32 [some 0] [.reg 1, .reg 2, .reg 3]
private def min2 : Op := fl .min f32 [some 0] [.reg 1, .reg 2]
private def setpLt : Op := fl (.setp (.ord .lt) none) f32 [some 8] [.reg 1, .reg 2]
private def setpNeu : Op := fl (.setp (.unord .ne) none) f32 [some 8] [.reg 1, .reg 2]
private def add2rm : Op := fl .add f32x2 [some 4] [.reg 5, .reg 6] (some .rm)
private def subRz : Op := fl .sub f32 [some 0] [.reg 1, .reg 2] (some .rz)
private def ex2Op : Op := fl .ex2 f32 [some 0] [.reg 1] (mode := .approx)
private def rcpOp : Op := fl .rcp f32 [some 0] [.reg 1] (mode := .approx)
private def setpInfOp : Op :=
  fl (.setp (.unord .ne) none) f32 [some 8] [.reg 1, .f32imm 0xFF800000]
private def setpGtInf : Op :=
  fl (.setp (.ord .gt) none) f32 [some 8] [.reg 1, .f32imm 0xFF800000]
private def addOp : Op := fl .add f32 [some 0] [.reg 1, .reg 2] (some .rn)
private def mulOp : Op := fl .mul f32 [some 0] [.reg 1, .reg 2] (some .rn)
/-- `cvt.f32.f16 %r0, %r1` -/
private def cvtWiden : CvtInstr :=
  { dst := .float .f32, src := .float .f16, d := 0, srcs := [.reg 1] }
private def infTwice : TState := mk [(1, .bits 32 0x7f800000), (2, .bits 32 0x7f800000)]

/-- The local step under an ideal-real assumption that selects the form `f`: the assumption's
rule, or the Core rule where it declines. -/
private theorem viaIdeal {n : String} {s : Assumption.IdealScope} {w : String} {L : Launch}
    {g : Nat} {t : TState} {op : Op} {f : FloatForm} (h : FloatForm.ofOp op = some f)
    (hm : f ∈ s.float) :
    execLocalA [Assumption.idealReal n s w] L g t op =
      (match Assumption.execIdealFloat L g t op with
        | some r => r
        | none => execLocal L g t op) := by
  simp [execLocalA, execLocalRule, Assumption.idealReal, h, hm]
  rfl

/-- The same for `approxExact`. -/
private theorem viaApprox {n : String} {fs : List Assumption.ApproxForm} {w : String}
    {L : Launch} {g : Nat} {t : TState} {op : Op} {f : Assumption.ApproxForm}
    (h : Assumption.ApproxForm.ofOp op = some f) (hm : f ∈ fs) :
    execLocalA [Assumption.approxExact n fs w] L g t op =
      (match Assumption.execApproxExact t op with
        | some r => r
        | none => execLocal L g t op) := by
  simp [execLocalA, execLocalRule, Assumption.approxExact, h, hm]
  rfl

/-- The assumption's rule on an instruction it selects. -/
private theorem ruleIdeal {n : String} {s : Assumption.IdealScope} {w : String} {L : Launch}
    {g : Nat} {t : TState} {op : Op} {f : FloatForm} (h : FloatForm.ofOp op = some f)
    (hm : f ∈ s.float) :
    (Assumption.idealReal n s w).localRule L g t op = Assumption.execIdealFloat L g t op := by
  simp [Assumption.idealReal, h, hm]

private theorem ruleApprox {n : String} {fs : List Assumption.ApproxForm} {w : String}
    {L : Launch} {g : Nat} {t : TState} {op : Op} {f : Assumption.ApproxForm}
    (h : Assumption.ApproxForm.ofOp op = some f) (hm : f ∈ fs) :
    (Assumption.approxExact n fs w).localRule L g t op = Assumption.execApproxExact t op := by
  simp [Assumption.approxExact, h, hm]

/-- An ideal-real assumption declines an instruction that is no form or whose form is outside its
scope. -/
private theorem declIdeal {a : Assumption} {n : String} {s : Assumption.IdealScope} {w : String}
    (ha : a = Assumption.idealReal n s w) {L : Launch} {g : Nat} {t : TState} {op : Op}
    (h : FloatForm.ofOp op = none ∨ ∃ f, FloatForm.ofOp op = some f ∧ f ∉ s.float) :
    a.localRule L g t op = none := by
  subst ha
  rcases h with h | ⟨f, h, hm⟩
  · simp [Assumption.idealReal, h]
  · simp [Assumption.idealReal, h, hm]

private theorem declApprox {a : Assumption} {n : String} {fs : List Assumption.ApproxForm}
    {w : String} (ha : a = Assumption.approxExact n fs w) {L : Launch} {g : Nat} {t : TState}
    {op : Op} (h : Assumption.ApproxForm.ofOp op = none) : a.localRule L g t op = none := by
  subst ha
  simp [Assumption.approxExact, h]

private theorem one_ne_bot : (1 : EReal) ≠ ⊥ := by
  intro h
  have := congrArg EReal.toReal h
  simp at this
private theorem one_ne_bot' : ((1 : EReal) = ⊥) = False := eq_false one_ne_bot
private theorem top_add_one : (⊤ : EReal) + 1 = ⊤ := EReal.top_add_of_ne_bot one_ne_bot

/-- Evaluation of `Assumption.execIdealFloat` and `Assumption.execApproxExact` on an instruction
whose operands are payloads or the bits of a register. -/
macro "exec_ideal" : tactic => `(tactic| (
  simp [pure, Except.pure, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    Assumption.bindRead, Assumption.readERealOpnd, Assumption.readERealPair,
    Assumption.readEReal, Assumption.readEReal.ofDatum, Assumption.addEReal,
    Assumption.mulEReal, Assumption.erealValue, Assumption.erealCompare, Assumption.readFinite,
    scalars, pairs, mk, readReg, readValue, setReg, next, splitValue, classify, Value.bitPattern,
    Value.bytes, FloatFmt.bytes, FloatFmt.layout, Layout.decode, Layout.width, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.topField, FVal.toValue, Layout.signPattern,
    Layout.infPattern, CvtInstr.widenF16?, CvtInstr.plain, ← EReal.coe_add, ← EReal.coe_neg,
    ← EReal.coe_mul, ← EReal.coe_sub, EReal.toReal_coe, coe_max, coe_min, sub_eq_add_neg,
    one_ne_bot', top_add_one]))

/-- `ideal_run F [ops]`: the local step under an ideal-real assumption of this file that selects
the form `F` of the instruction `ops`. -/
syntax "ideal_run" term:max ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ideal_run $f $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (simp only [ideal, idealAdd2, idealAdd, idealMul, idealInf, idealCvt, exact]
               rw [viaIdeal (f := ($f : Assumption.FloatForm)) rfl (by decide)]
               dsimp only [Assumption.execIdealFloat, fl, f32, f32x2, $ls,*]
               exec_ideal))

/-- `approx_run F [ops]`: the same under `approxExact`. -/
syntax "approx_run" term:max ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| approx_run $f $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (simp only [ideal, idealAdd2, idealAdd, idealMul, idealInf, idealCvt, exact]
               rw [viaApprox (f := ($f : Assumption.ApproxForm)) rfl (by decide)]
               dsimp only [Assumption.execApproxExact, fl, f32, $ls,*]
               exec_ideal))

/-- `rule_ideal F [ops]`: the assumption's rule, which declines when it is `none`. -/
syntax "rule_ideal" term:max ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rule_ideal $f $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (simp only [ideal, idealAdd2, idealAdd, idealMul, idealInf, idealCvt, exact]
               rw [ruleIdeal (f := ($f : Assumption.FloatForm)) rfl (by decide)]
               dsimp only [Assumption.execIdealFloat, fl, f32, f32x2, $ls,*]
               exec_ideal))

syntax "rule_approx" term:max ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rule_approx $f $[[$ls,*]]?) => do
    let ls := ls.map (·.getElems) |>.getD #[]
    `(tactic| (simp only [ideal, idealAdd2, idealAdd, idealMul, idealInf, idealCvt, exact]
               rw [ruleApprox (f := ($f : Assumption.ApproxForm)) rfl (by decide)]
               dsimp only [Assumption.execApproxExact, fl, f32, $ls,*]
               exec_ideal))

/-! ### Exact results on finite operands -/

-- `sub.f32`
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) sub1 =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (x - y)))) := by
  ideal_run (.subRn .f32) [sub1]
-- `add`, `sub`, `fma` of `.f32x2`, and `mul.f32x2` which shares the element reading
example (x0 x1 y0 y1 z0 z1 : ℝ) : execLocalA [ideal] launch 0 (pairs x0 x1 y0 y1 z0 z1) add2 =
    .ok (next (setReg (pairs x0 x1 y0 y1 z0 z1) 4
      (.pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1))))) := by
  ideal_run (.addRnF32x2) [add2]
example (x0 x1 y0 y1 z0 z1 : ℝ) : execLocalA [ideal] launch 0 (pairs x0 x1 y0 y1 z0 z1) sub2 =
    .ok (next (setReg (pairs x0 x1 y0 y1 z0 z1) 4
      (.pair (.float .f32 (x0 - y0)) (.float .f32 (x1 - y1))))) := by
  ideal_run (.subRnF32x2) [sub2]
example (x0 x1 y0 y1 z0 z1 : ℝ) : execLocalA [ideal] launch 0 (pairs x0 x1 y0 y1 z0 z1) fma2 =
    .ok (next (setReg (pairs x0 x1 y0 y1 z0 z1) 4
      (.pair (.float .f32 (x0 * y0 + z0)) (.float .f32 (x1 * y1 + z1))))) := by
  ideal_run (.fmaRnF32x2) [fma2]
example (x0 x1 y0 y1 z0 z1 : ℝ) : execLocalA [ideal] launch 0 (pairs x0 x1 y0 y1 z0 z1) mul2 =
    .ok (next (setReg (pairs x0 x1 y0 y1 z0 z1) 4
      (.pair (.float .f32 (x0 * y0)) (.float .f32 (x1 * y1))))) := by
  ideal_run (.mulF32x2) [mul2]
-- `idealAdd2` selects `add.rn.f32x2` only.
example (x0 x1 y0 y1 z0 z1 : ℝ) : execLocalA [idealAdd2] launch 0
    (pairs x0 x1 y0 y1 z0 z1) add2 =
    .ok (next (setReg (pairs x0 x1 y0 y1 z0 z1) 4
      (.pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1))))) := by
  ideal_run (.addRnF32x2) [add2]
-- `max` of two and of three values, and `min`
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) max2 =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (max x y)))) := by
  ideal_run (.max .f32) [max2]
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) max3 =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (max (max x y) z)))) := by
  ideal_run (.max .f32) [max3]
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) min2 =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (min x y)))) := by
  ideal_run (.min .f32) [min2]
-- an unordered comparison is its ordered counterpart on reals
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) setpLt =
    .ok (next (setReg (scalars x y z) 8 (.pred (decide (x < y))))) := by
  ideal_run (.setp .f32) [setpLt]
example (x y z : ℝ) : execLocalA [ideal] launch 0 (scalars x y z) setpNeu =
    .ok (next (setReg (scalars x y z) 8 (.pred (decide (x ≠ y))))) := by
  ideal_run (.setp .f32) [setpNeu]
-- `ex2.approx` and `rcp.approx` read as `2 ^ a` and `1 / a` under `approxExact`
example (x y z : ℝ) : execLocalA [exact] launch 0 (scalars x y z) ex2Op =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (Real.rpow 2 x)))) := by
  approx_run (.ex2 .f32) [ex2Op]
example (x y z : ℝ) (hx : x ≠ 0) : execLocalA [exact] launch 0 (scalars x y z) rcpOp =
    .ok (next (setReg (scalars x y z) 0 (.float .f32 (1 / x)))) := by
  approx_run (.rcp .f32) [rcpOp]
  exact hx
-- `rcp.approx(0)` still faults, where the Core table gives `+inf`
example (y z : ℝ) : execLocalA [exact] launch 0 (scalars 0 y z) rcpOp = .error .badValue := by
  approx_run (.rcp .f32) [rcpOp]

/-! ### Forms the scopes leave to the Core rule: the assumption declines

The Core rule gives the result in each case (Tests/Float/FloatExec.lean). Directed rounding is no
`FloatForm` (`add.rm.f32x2`, `sub.rz.f32`), so an exact sum never erases the rounding. Outside its
scope `sub.rn.f32x2` is not selected, a scope that names `setp` only does not select `setp` with
an infinite constant, the approximations are no `FloatForm`, and `approxExact` selects no floating
arithmetic. -/

example : FloatForm.ofOp add2rm = none ∧ FloatForm.ofOp subRz = none := ⟨rfl, rfl⟩

example (t : TState) : ideal.localRule launch 0 t add2rm = none :=
  declIdeal (ha := rfl) (Or.inl rfl)
example (t : TState) : ideal.localRule launch 0 t subRz = none :=
  declIdeal (ha := rfl) (Or.inl rfl)
example (t : TState) : ideal.localRule launch 0 t ex2Op = none :=
  declIdeal (ha := rfl) (Or.inl rfl)
example (t : TState) : ideal.localRule launch 0 t rcpOp = none :=
  declIdeal (ha := rfl) (Or.inl rfl)
example (t : TState) : idealAdd2.localRule launch 0 t sub2 = none :=
  declIdeal (ha := rfl) (Or.inr ⟨.subRnF32x2, rfl, by decide⟩)
example (t : TState) : ideal.localRule launch 0 t setpInfOp = none :=
  declIdeal (ha := rfl) (Or.inr ⟨.setpInf .f32, rfl, by decide⟩)
example (t : TState) : exact.localRule launch 0 t sub1 = none :=
  declApprox (ha := rfl) rfl

-- A NaN operand (opaque, or its bits), `∞ - ∞` and `0 · ∞` decline.
example : ideal.localRule launch 0 (mk [(1, .nan .f32), (2, .float .f32 1)]) sub1 = none := by
  rule_ideal (.subRn .f32) [sub1]
example : ideal.localRule launch 0 (mk [(1, .bits 32 0x7fc00000), (2, .float .f32 1)]) sub1 =
    none := by
  rule_ideal (.subRn .f32) [sub1]
example : ideal.localRule launch 0 infTwice sub1 = none := by
  rule_ideal (.subRn .f32) [sub1, infTwice]
example : idealMul.localRule launch 0 (mk [(1, .float .f32 0), (2, .bits 32 0xff800000)])
    mulOp = none := by
  rule_ideal (.mul .f32) [mulOp]
-- An infinite operand of an approximation declines.
example : exact.localRule launch 0 (mk [(1, .bits 32 0xff800000)]) ex2Op = none := by
  rule_approx (.ex2 .f32) [ex2Op]

/-! ### Infinities, signed zeros and `cvt` -/

-- `+∞ + 1` is the bits of `+∞`.
example : execLocalA [idealAdd] launch 0 (mk [(1, .bits 32 0x7f800000), (2, .float .f32 1)])
    addOp = .ok (next (setReg (mk [(1, .bits 32 0x7f800000), (2, .float .f32 1)]) 0
      (.bits 32 0x7f800000))) := by
  ideal_run (.add .f32) [addOp]
-- A `-0` operand reads as `0`, and a zero result is `+0` where the Core rule gives `-0`.
example : execLocalA [idealAdd] launch 0 (mk [(1, .bits 32 0x80000000), (2, .float .f32 3)])
    addOp = .ok (next (setReg (mk [(1, .bits 32 0x80000000), (2, .float .f32 3)]) 0
      (.float .f32 3))) := by
  ideal_run (.add .f32) [addOp]
example : execLocalA [idealAdd] launch 0 (mk [(1, .bits 32 0x80000000), (2, .bits 32 0x80000000)])
    addOp = .ok (next (setReg (mk [(1, .bits 32 0x80000000), (2, .bits 32 0x80000000)]) 0
      (.float .f32 0))) := by
  ideal_run (.add .f32) [addOp]
-- A register that holds `-inf` is compared as that infinity.
example (y : ℝ) : execLocalA [ideal] launch 0 (mk [(1, .bits 32 0xff800000), (2, .float .f32 y)])
    setpLt = .ok (next (setReg (mk [(1, .bits 32 0xff800000), (2, .float .f32 y)]) 8
      (.pred true))) := by
  ideal_run (.setp .f32) [setpLt]
-- So is the constant `-inf` under `setpInf`: a real is not `-inf` and is greater than it.
example (x : ℝ) : execLocalA [idealInf] launch 0 (mk [(1, .float .f32 x)]) setpInfOp =
    .ok (next (setReg (mk [(1, .float .f32 x)]) 8 (.pred true))) := by
  ideal_run (.setpInf .f32) [setpInfOp]
example (x : ℝ) : execLocalA [idealInf] launch 0 (mk [(1, .float .f32 x)]) setpGtInf =
    .ok (next (setReg (mk [(1, .float .f32 x)]) 8 (.pred true))) := by
  ideal_run (.setpInf .f32) [setpGtInf]
-- `cvt.f32.f16` of `0x8000` under `cvtF32F16` gives `+0`; the Core rule gives the bits of `-0`.
example : execLocalA [idealCvt] launch 0 (mk [(1, .bits 16 0x8000)]) (.cvt cvtWiden) =
    .ok (next (setReg (mk [(1, .bits 16 0x8000)]) 0 (.float .f32 0))) := by
  ideal_run (.cvtF32F16) [cvtWiden]

-- The statement of `idealReal` names the forms and the reading of infinities and NaN.
set_option maxRecDepth 100000 in
example : (Assumption.idealReal "n" { float := [.cvtF32F16] } "w").statement =
    "Exact real arithmetic for exactly these forms: cvt.f32.f16. Results are not rounded, do not \
    overflow and are never subnormal, and zero has no sign (a zero result is +0). For the \
    floating instruction forms an infinite operand is read as that infinity, and an operation \
    with a NaN operand, ∞ − ∞ or 0 × ∞ takes the Core rule; MMA, warp-level MMA and atomic or \
    reduction elements must be finite numbers. w" := by
  simp [Assumption.idealReal, Assumption.IdealScope.text, Assumption.FloatForm.text]
  rfl

end
end PTX.Tests.FloatForms
