-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.ClusterScopeMbar
public import Core.Thread.Local
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Assumption constructor `segmentExact`

A kernel declares a segment-as-exact-function assumption with `Assumption.segmentExact`, naming
a reviewed code template, the exact real function it is read as, and exactly the sites (`pc`)
where an instance of the template starts. This file is not itself an assumption. A template
belongs to the kernel that uses it: the FlashAttention-4 forward kernel's software `exp2`,
`cuteExp2`, is in `Kernels/FlashAttn4Fwd/Assumptions/Exp2Template.lean`.
-/

namespace PTX.Assumption
noncomputable section

/-! ## ASM-SEGMENT — a straight-line code template read as an exact function, at named sites
Statement: At the sites a kernel names where the code matches a reviewed straight-line template, the
  model executes the whole template as one step that gives each output the exact value of the
  template's real function of its input. The template, its function and the approximations the
  reading ignores are part of the kernel's assumption.

Defs: Assumption.SegInstr, Assumption.SegInstr.bind, Assumption.SegInstr.writes,
  Assumption.SegShape, Assumption.SegShape.writes, Assumption.SegTemplate,
  Assumption.SegMatch, Assumption.matchBody, Assumption.SegTemplate.matchAt,
  Assumption.execSegment, Assumption.segmentExact

Source:
- §9.7.3.3 (`add.f32x2`): ".rm mantissa LSB rounds toward negative infinity"
- §9.7.3.6 (`fma.f32x2`)
- §9.7.3.12 (max)
- §9.7.9.8 (shl)
- §9.7.1.1 (add)
- §9.7.10.3
- §9.7.10.4 (mov)
- CuTeDSL `cute/math` software `exp2` (the source of the template)

Direction: not-conservative

Effect: `segmentExact K name T sites why` reads the code at the selected sites as one local step,
  through the field `segmentRule`, which is consulted before the instruction rules (THREAD-LOCAL).
  At a thread state whose `pc` is in `sites`, between instructions, the instructions of kernel `K`
  from that `pc` must match one of the template's shapes exactly: every instruction unguarded and
  of the given form, and its registers a one-to-one assignment of the shape's slots (`matchBody`),
  so that no two slots share a register. The step then writes each output slot with
  `.float .f32 (T.fn x)` for the `f32` number `x` its input slot holds (THREAD-NUM). It sets the
  constant slots of a defining shape to the values Core's moves of those literals produce. It
  leaves the constant slots of a reusing shape as they are (which must hold those values,
  otherwise the step faults). It clears every other register the instructions write (a later read
  of one is `uninitialized`). It continues after the last instruction. At a site where the code
  does not match, or between the events of one instruction, the hook selects nothing and Core's
  rules apply. A path that enters the instructions after the first one is not affected: only the
  first `pc` selects the reading. The statement is generated from the template's text and the
  sites and lists every site it covers. The constructor sets no `wf` and no `ub`.

Review: Some code computes a real function through float bit patterns and directed rounding, which
  the ideal reading of single instructions (ASM-IDEAL) cannot express. CuTeDSL's software `exp2`
  rounds with `add.rm.f32x2` against 1.5·2^23 and adds the integer part into the exponent field
  with integer instructions. The step replaces the semantics of instructions Core defines, and it
  is a reading of the whole code as its intended function, with every approximation of that
  function named in the template's text and the kernel's `why`.
-/

/-- One instruction of a template, with slots `σ` for its registers. -/
inductive SegInstr (σ : Type) where
  /-- `max.f32 d, a, 0f<c>` -/
  | maxF32 (d a : σ) (c : Nat)
  /-- `mov.b64 d, {a, b}` -/
  | pack64 (d a b : σ)
  /-- `mov.b64 {lo, hi}, a` -/
  | unpack64 (lo hi a : σ)
  /-- `mov.b32 d, 0f<c>` -/
  | movF32 (d : σ) (c : Nat)
  /-- `mov.b32 d, a` -/
  | mov32 (d a : σ)
  /-- `add.rm.f32x2 d, a, b` -/
  | addRmF32x2 (d a b : σ)
  /-- `sub.rn.f32x2 d, a, b` -/
  | subRnF32x2 (d a b : σ)
  /-- `fma.rn.f32x2 d, a, b, c` -/
  | fmaRnF32x2 (d a b c : σ)
  /-- `shl.b32 d, a, n` -/
  | shl32 (d a : σ) (n : Int)
  /-- `add.s32 d, a, b` -/
  | addS32 (d a b : σ)

/-- The slot–register pairs of an instruction of the template's form; `none` for any other
instruction. -/
def SegInstr.bind {σ : Type} : SegInstr σ → Instr → Option (List (σ × Nat))
  | .maxF32 d a c, ⟨none, .float f⟩ =>
    match f.op, f.dsts, f.srcs with
    | .max, [some d'], [.reg a', .f32imm c'] =>
      if f.ty == ⟨.f32, 1⟩ && f.srcTys.isEmpty && !f.nanMod && !f.xorsign && !f.absMod && c' == c
      then some [(a, a'), (d, d')] else none
    | _, _, _ => none
  | .pack64 d a b, ⟨none, .move m@⟨.pack, ty, [some d'], [.reg a', .reg b']⟩⟩ =>
    if ty.width = 64 ∧ m.rule.isSome then some [(a, a'), (b, b'), (d, d')] else none
  | .unpack64 lo hi a, ⟨none, .move m@⟨.unpack, ty, [some lo', some hi'], [.reg a']⟩⟩ =>
    if ty.width = 64 ∧ m.rule.isSome then some [(a, a'), (lo, lo'), (hi, hi')] else none
  | .movF32 d c, ⟨none, .move m@⟨.scalar, ty, [some d'], [.f32imm c']⟩⟩ =>
    if ty.width = 32 ∧ m.rule.isSome ∧ c' = c then some [(d, d')] else none
  | .mov32 d a, ⟨none, .move m@⟨.scalar, ty, [some d'], [.reg a']⟩⟩ =>
    if ty.width = 32 ∧ m.rule.isSome then some [(a, a'), (d, d')] else none
  | .addRmF32x2 d a b, ⟨none, .float f⟩ =>
    match f.op, f.dsts, f.srcs with
    | .add, [some d'], [.reg a', .reg b'] =>
      if f.ty == ⟨.f32, 2⟩ && f.srcTys.isEmpty && f.rnd == some .rm && !f.sat
      then some [(a, a'), (b, b'), (d, d')] else none
    | _, _, _ => none
  | .subRnF32x2 d a b, ⟨none, .float f⟩ =>
    match f.op, f.dsts, f.srcs with
    | .sub, [some d'], [.reg a', .reg b'] =>
      if f.ty == ⟨.f32, 2⟩ && f.srcTys.isEmpty && (f.rnd == none || f.rnd == some .rn) && !f.sat
      then some [(a, a'), (b, b'), (d, d')] else none
    | _, _, _ => none
  | .fmaRnF32x2 d a b c, ⟨none, .float f⟩ =>
    match f.op, f.dsts, f.srcs with
    | .fma, [some d'], [.reg a', .reg b', .reg c'] =>
      if f.ty == ⟨.f32, 2⟩ && f.srcTys.isEmpty && f.rnd == some .rn && !f.sat
      then some [(a, a'), (b, b'), (c, c'), (d, d')] else none
    | _, _, _ => none
  | .shl32 d a n, ⟨none, .int i@⟨.shl, ty, _, [some d'], [.reg a', .imm n']⟩⟩ =>
    if ty.width = 32 ∧ i.rule.isSome ∧ n' = n then some [(a, a'), (d, d')] else none
  | .addS32 d a b, ⟨none, .int i@⟨.add, ty, false, [some d'], [.reg a', .reg b']⟩⟩ =>
    if ty.width = 32 ∧ ty.kind?.isSome ∧ i.rule.isSome then some [(a, a'), (b, b'), (d, d')]
    else none
  | _, _ => none

/-- The slots an instruction writes. -/
def SegInstr.writes {σ : Type} : SegInstr σ → List σ
  | .maxF32 d .. | .pack64 d .. | .movF32 d .. | .mov32 d .. | .addRmF32x2 d .. | .subRnF32x2 d ..
  | .fmaRnF32x2 d .. | .shl32 d .. | .addS32 d .. => [d]
  | .unpack64 lo hi _ => [lo, hi]

/-- One shape of a template: its instructions, its (input, output) slot pairs, its constant
slots with their values, and whether it defines the constants (or reuses them). -/
structure SegShape (σ : Type) where
  body : List (SegInstr σ)
  io : List (σ × σ)
  consts : List (σ × Value)
  defines : Bool

/-- The slots a shape writes. -/
def SegShape.writes {σ : Type} (sh : SegShape σ) : List σ := sh.body.flatMap SegInstr.writes

/-- A reviewed template: the text quoted in the statement, its shapes and the exact function
each output is read as. -/
structure SegTemplate (σ : Type) where
  text : String
  shapes : List (SegShape σ)
  fn : ℝ → ℝ

/-- An instance of a shape in the code: the shape, the registers of its slots and the first
`pc` after it. -/
structure SegMatch (σ : Type) where
  shape : SegShape σ
  reg : List (σ × Nat)
  stop : Nat

/-- Match the instructions `code` against `body` with the slot assignment `asg`: every slot
gets one register, and no two slots the same register. -/
def matchBody {σ : Type} [DecidableEq σ] :
    List (SegInstr σ) → List Instr → List (σ × Nat) → Option (List (σ × Nat))
  | [], _, asg => some asg
  | _ :: _, [], _ => none
  | p :: ps, i :: is, asg => do
    let pairs ← p.bind i
    let asg' ← pairs.foldlM (init := asg) fun acc (s, r) =>
      match acc.lookup s with
      | some r' => if r' = r then some acc else none
      | none => if acc.any (·.2 == r) then none else some ((s, r) :: acc)
    matchBody ps is asg'

/-- The first shape of the template that matches the code of `K` from `pc`. -/
def SegTemplate.matchAt {σ : Type} [DecidableEq σ] (T : SegTemplate σ) (K : Kernel) (pc : Nat) :
    Option (SegMatch σ) :=
  T.shapes.findSome? fun sh =>
    (matchBody sh.body (K.code.drop pc) []).map fun asg => ⟨sh, asg, pc + sh.body.length⟩

open Classical in
/-- The effect of one instance: reusing shapes check their constants; every written register is
cleared, then the constants of a defining shape and each output (the exact function of its
input's `f32` number) are set; execution continues after the instance. -/
def execSegment {σ : Type} [DecidableEq σ] (fn : ℝ → ℝ) (m : SegMatch σ) (t : TState) :
    Exec TState := do
  let reg := fun s => (m.reg.lookup s).getD 0
  unless m.shape.defines ∨ ∀ p ∈ m.shape.consts, t.regs (reg p.1) = some p.2 do
    throw .badValue
  let outs : List (Nat × Value) ← m.shape.io.mapM fun p => do
    let x ← valFloat .f32 (← readReg t (reg p.1))
    pure (reg p.2, Value.float .f32 (fn x))
  let cleared : Nat → Option Value :=
    m.shape.writes.foldl (fun rs s => Function.update rs (reg s) none) t.regs
  let consts : Nat → Option Value := if m.shape.defines then
      m.shape.consts.foldl (fun rs p => Function.update rs (reg p.1) (some p.2)) cleared
    else cleared
  let regs : Nat → Option Value :=
    outs.foldl (fun rs p => Function.update rs p.1 (some p.2)) consts
  pure { t with regs := regs, pc := m.stop, sub := 0, acc := [] }

/-- Read the instances of `T` in kernel `K` that start at exactly `sites` as `T.fn`, element by
element; `why` says why the kernel needs it. -/
def segmentExact {σ : Type} [DecidableEq σ] (K : Kernel) (name : String) (T : SegTemplate σ)
    (sites : List Nat) (why : String) : Assumption where
  name := name
  statement := s!"The straight-line code {T.text} is read as one step that gives each output \
    the exact function of its input, clears every other register it writes and continues after \
    it, at exactly the instances starting at these sites: {siteText sites}. {why}"
  segmentRule _ _ t :=
    if sites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (T.matchAt K t.pc).map fun m => execSegment T.fn m t
    else none

end
end PTX.Assumption
