-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.IdealReal
public import Core.Assumption.SegmentExact

@[expose] public section

/-!
# The software `exp2` template of the Inkling relative decode kernel

The kernel's `_gl_ex2_emu` (`attention.py:503-506`, the inline assembly `_EX2_EMU_ASM`,
`attention.py:405-419`, from `tml_fa4 utils.ex2_emulation_2`) computes `2 ^ x` for one `f32` with a
clamp, a rounding trick and a degree-3 polynomial:

```
max.ftz.f32 c, x, 0fC2FE0000;             // c = max(x, -127)
add.rm.ftz.f32 r, c, 0f4B400000;          // r = c + 1.5 * 2^23, rounded down: floor(c) + 1.5 * 2^23
sub.rn.ftz.f32 rb, r, 0f4B400000;         // rb = floor(c)
sub.rn.ftz.f32 f, c, rb;                  // f = c - floor(c)
fma.rn.ftz.f32 p, f, 0f3D9DF09D, 0f3E6906A4;
fma.rn.ftz.f32 p, p, f, 0f3F31F519;
fma.rn.ftz.f32 p, p, f, 0f3F800000;       // p = degree-3 polynomial of f, about 2 ^ f
mov.b32 e, r; shl.b32 e, e, 23;           // the integer part, shifted into the exponent field
mov.b32 y, p; add.s32 y, y, e;            // y = p's bit pattern plus the exponent
```

It differs from CuTeDSL's `cuteExp2` (`Core/Assumption/SegmentExact`'s `SegInstr` vocabulary) in
using scalar `.ftz` instructions with immediate constants, so the shapes of Core's template cannot
express it and the kernel carries its own. The 16 instances of the program are consecutive
11-instruction blocks (PTX 1913 to 2088); `ptxas` keeps them in this order and the temporaries
`c, r, rb, f, p, e` are the registers of the inline assembly's scope.
-/

namespace PTX.Kernels.InklingRelDecode.Assumptions
open PTX PTX.Assumption

/-- One instruction of the template, with slots `σ` for its registers. -/
inductive EmuInstr (σ : Type) where
  /-- `max.ftz.f32 d, a, 0f<c>` -/
  | maxFtz (d a : σ) (c : Nat)
  /-- `add.rm.ftz.f32 d, a, 0f<c>` -/
  | addRmFtz (d a : σ) (c : Nat)
  /-- `sub.rn.ftz.f32 d, a, 0f<c>` -/
  | subRnFtzC (d a : σ) (c : Nat)
  /-- `sub.rn.ftz.f32 d, a, b` -/
  | subRnFtz (d a b : σ)
  /-- `fma.rn.ftz.f32 d, a, 0f<c1>, 0f<c2>` -/
  | fmaFtzCC (d a : σ) (c1 c2 : Nat)
  /-- `fma.rn.ftz.f32 d, a, b, 0f<c>` -/
  | fmaFtzRC (d a b : σ) (c : Nat)
  /-- `mov.b32 d, a` -/
  | mov32 (d a : σ)
  /-- `shl.b32 d, a, n` -/
  | shl32 (d a : σ) (n : Int)
  /-- `add.s32 d, a, b` -/
  | addS32 (d a b : σ)

/-- The scalar `.f32` floating form of the template: unguarded, `.ieee` mode, with the given
rounding and `.ftz`, no saturation or other modifier. -/
def isEmuFloat (f : FloatInstr) (op : FOp) (rnd : Option FloatRound) : Bool :=
  f.op == op && f.ty == ⟨.f32, 1⟩ && f.srcTys.isEmpty && f.cmpTy.isNone && f.rnd == rnd &&
    f.mode == .ieee && f.ftz && !f.sat && !f.relu && !f.oob && !f.nanMod && !f.xorsign &&
    !f.absMod

/-- The slot–register pairs of an instruction of the template's form; `none` for any other
instruction. -/
def EmuInstr.bind {σ : Type} : EmuInstr σ → Instr → Option (List (σ × Nat))
  | .maxFtz d a c, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .f32imm c'] =>
      if isEmuFloat f .max none && c' == c then some [(a, a'), (d, d')] else none
    | _, _ => none
  | .addRmFtz d a c, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .f32imm c'] =>
      if isEmuFloat f .add (some .rm) && c' == c then some [(a, a'), (d, d')] else none
    | _, _ => none
  | .subRnFtzC d a c, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .f32imm c'] =>
      if isEmuFloat f .sub (some .rn) && c' == c then some [(a, a'), (d, d')] else none
    | _, _ => none
  | .subRnFtz d a b, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .reg b'] =>
      if isEmuFloat f .sub (some .rn) then some [(a, a'), (b, b'), (d, d')] else none
    | _, _ => none
  | .fmaFtzCC d a c1 c2, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .f32imm c1', .f32imm c2'] =>
      if isEmuFloat f .fma (some .rn) && c1' == c1 && c2' == c2 then some [(a, a'), (d, d')]
      else none
    | _, _ => none
  | .fmaFtzRC d a b c, ⟨none, .float f⟩ =>
    match f.dsts, f.srcs with
    | [some d'], [.reg a', .reg b', .f32imm c'] =>
      if isEmuFloat f .fma (some .rn) && c' == c then some [(a, a'), (b, b'), (d, d')] else none
    | _, _ => none
  | .mov32 d a, ⟨none, .move m@⟨.scalar, ty, [some d'], [.reg a']⟩⟩ =>
    if ty.width = 32 ∧ m.rule.isSome then some [(a, a'), (d, d')] else none
  | .shl32 d a n, ⟨none, .int i@⟨.shl, ty, _, [some d'], [.reg a', .imm n']⟩⟩ =>
    if ty.width = 32 ∧ i.rule.isSome ∧ n' = n then some [(a, a'), (d, d')] else none
  | .addS32 d a b, ⟨none, .int i@⟨.add, ty, false, [some d'], [.reg a', .reg b']⟩⟩ =>
    if ty.width = 32 ∧ ty.kind?.isSome ∧ i.rule.isSome then some [(a, a'), (b, b'), (d, d')]
    else none
  | _, _ => none

/-- The slots of the template. `x` is the input, `y` the output. -/
inductive EmuSlot where
  | x | c | r | rb | f | p | e | y
  deriving DecidableEq

/-- The 11 instructions of `_EX2_EMU_ASM`. -/
def emuBody : List (EmuInstr EmuSlot) :=
  [.maxFtz .c .x 0xC2FE0000, .addRmFtz .r .c 0x4B400000, .subRnFtzC .rb .r 0x4B400000,
   .subRnFtz .f .c .rb, .fmaFtzCC .p .f 0x3D9DF09D 0x3E6906A4,
   .fmaFtzRC .p .p .f 0x3F31F519, .fmaFtzRC .p .p .f 0x3F800000, .mov32 .e .r,
   .shl32 .e .e 23, .mov32 .y .p, .addS32 .y .y .e]

/-- The slots the template writes: every temporary and the output, never the input. -/
def emuWrites : List EmuSlot := [.c, .r, .rb, .f, .p, .e, .y]

/-- The slot–register assignment of a match, or `none`: every slot gets one register and no two
slots share one. -/
def matchEmu {σ : Type} [DecidableEq σ] :
    List (EmuInstr σ) → List Instr → List (σ × Nat) → Option (List (σ × Nat))
  | [], _, asg => some asg
  | _ :: _, [], _ => none
  | p :: ps, i :: is, asg => do
    let pairs ← p.bind i
    let asg' ← pairs.foldlM (init := asg) fun acc (s, r) =>
      match acc.lookup s with
      | some r' => if r' = r then some acc else none
      | none => if acc.any (·.2 == r) then none else some ((s, r) :: acc)
    matchEmu ps is asg'

/-- The register of slot `s` in a match. -/
def emuReg (asg : List (EmuSlot × Nat)) (s : EmuSlot) : Nat := (asg.lookup s).getD 0

/-- The effect of one instance: every register the template writes is cleared, then the output is
the exact `2 ^ x` of the input, `0` for `x = -∞`; execution continues after the 11 instructions.
A NaN input declines (Core's rules apply to the instructions one by one), and `+∞` is a fault. -/
noncomputable def execEmu (asg : List (EmuSlot × Nat)) (t : TState) : Option (Exec TState) :=
  bindRead (readERealOpnd t .f32 (.reg (emuReg asg .x))) fun x =>
    some (if x = ⊤ then throw .badValue else
      let cleared : Nat → Option Value :=
        emuWrites.foldl (fun rs s => Function.update rs (emuReg asg s) none) t.regs
      let out : Value := .float .f32 (if x = ⊥ then 0 else Real.rpow 2 x.toReal)
      pure { t with regs := Function.update cleared (emuReg asg .y) (some out),
                    pc := t.pc + emuBody.length, sub := 0, acc := [] })

/-- The first `pc` of each of the 16 instances: the `max.ftz.f32` that opens a block of 11. -/
def emuSites : List Nat := (List.range 16).map fun i => 1913 + 11 * i

/-- The 16 software-`exp2` instances of `_gl_ex2_emu`, read as the exact `2 ^ x` of their `f32`
input. -/
noncomputable def swExp2 (K : Kernel) : Assumption where
  name := "inkling-sw-exp2"
  statement := "The straight-line code of `_EX2_EMU_ASM` (`max.ftz.f32` with 0fC2FE0000, \
    `add.rm.ftz.f32` and `sub.rn.ftz.f32` with 0f4B400000, a second `sub.rn.ftz.f32`, three \
    `fma.rn.ftz.f32` with 0f3D9DF09D, 0f3E6906A4, 0f3F31F519, 0f3F800000, and `shl.b32` by 23 and \
    `add.s32` of the integer part into the polynomial's exponent field; 11 instructions) is read \
    as one step that gives the output the exact 2 ^ x of the input (0 for -infinity), clears the \
    other registers it writes and continues after it, at exactly the instances starting at the \
    sites 1913, 1924, ..., 2078 (every 11th). The code computes approximately 2 ^ max(x, -127) \
    with a degree-3 polynomial: the clamp and the polynomial's error are approximations that the \
    theorem does not model."
  segmentRule _ _ t :=
    if emuSites.contains t.pc ∧ t.sub = 0 ∧ t.acc.isEmpty then
      (matchEmu emuBody (K.code.drop t.pc) []).bind (execEmu · t)
    else none

end PTX.Kernels.InklingRelDecode.Assumptions
