-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutLit

@[expose] public section

/-! # Run items for instructions Core reads: integer, predicate, move and conversion forms

A proof tool for `Tools/out_gen.py`. An `XItem.fn op d srcs f` item is a local instruction with
one destination whose value is `f` of its source registers' values (`XItem.Rule`). For the forms
below, where no assumption has a rule for the instruction, `f` is Core's computation written on
the register values (`coreF op srcs`, by `coreW`), so a kernel declares no reading of its own:

* `setp.<cmp>` without a combining predicate, `add`/`sub` of a scalar integer type (including the
  symbolic-pointer arms), `mul.lo`, `shl`, `shr`, `and`/`or` (of bits, or of predicates),
  `prmt`, `selp`, on register, integer-immediate or `0f` operands (`plainB`);
* `mov` of one operand (a predicate, or a value of the type's width), `mov` packing two values;
* `cvt` from an integer to an integer, and from a float register to a float without rounding
  mode (`cvt.f32.bf16`).

Each form has a rule lemma `XItem.core_<form>` (`Lemmas/Flow/OutCoreRules.lean`): at a pc
where no assumption takes a segment (`SegFreePc`) and none has a local rule for the instruction
(`NoLocalRule`), and the form's Boolean checks hold (by `rfl` on the literal instruction), the
item reads Core's value. The values are read through `oBits`, `oVal`, `oPred`, `oCvt`
(`readBits`, `readValue`, `readPred`, `readCvtFloat` of a state whose registers hold `W`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-! ### Operands read from register values -/

/-- A register, integer-immediate or `0f` operand. -/
def plainB : Opnd → Bool
  | .reg _ | .imm _ | .f32imm _ => true
  | _ => false

/-- The register of an operand, if any. -/
def regOf : Opnd → List Nat
  | .reg r => [r]
  | _ => []

/-- The source registers of a list of operands. -/
def regsOf (os : List Opnd) : List Nat := os.flatMap regOf

/-- The value of register `r` in the values `vs` of the registers `srcs`. -/
def lk (srcs : List Nat) (vs : List Value) (r : Nat) : Value :=
  ((srcs.zip vs).lookup r).getD (.bits 32 0)

theorem lk_map {W : Nat → Value} : ∀ {srcs : List Nat} {r : Nat}, r ∈ srcs →
    lk srcs (srcs.map W) r = W r
  | [], _, h => by simp at h
  | q :: srcs, r, h => by
    by_cases e : r = q
    · subst e
      simp [lk]
    · have hb : (r == q) = false := by simpa using e
      have h' : r ∈ srcs := by simpa [e] using h
      have := lk_map (W := W) h'
      simp only [lk, List.map_cons, List.zip_cons_cons, List.lookup, hb] at this ⊢
      exact this

/-- `readBits` of a register holding `W r`, or of a literal. -/
def oBits (W : Nat → Value) (w : Nat) : Opnd → Exec (BitVec 64)
  | .reg r => match W r with
    | .bits _ x => pure (truncBits w x)
    | .ptr .. | .policy => throw .noRule
    | v => match v.bitPattern with
      | some n => pure (truncBits w (BitVec.ofNat 64 n))
      | none => throw .typeMismatch
  | .imm v => pure (truncBits w (BitVec.ofInt 64 v))
  | .f32imm b => if w = 32 then pure (BitVec.ofNat 64 b) else throw .typeMismatch
  | _ => throw .noRule

/-- `readValue` of a register holding `W r`, or of a literal. -/
def oVal (W : Nat → Value) (w : Nat) : Opnd → Exec Value
  | .reg r => pure (W r)
  | o => return .bits w (← oBits W w o)

/-- `readPred` of a register holding `W r`. -/
def oPred (W : Nat → Value) : Opnd → Exec Bool
  | .reg r => match W r with
    | .pred b => pure b
    | _ => throw .typeMismatch
  | .imm v => pure (v ≠ 0)
  | _ => throw .typeMismatch

/-- `readCvtFloat` of a register holding `W r`. -/
def oCvt (W : Nat → Value) (wide : Bool) (fmt : FloatFmt) : Opnd → Exec FVal
  | .reg r =>
    if wide ∧ fmt.bytes < (W r).bytes then do classify fmt (← lowValue fmt.bytes (W r))
    else classify fmt (W r)
  | _ => throw .typeMismatch

section
variable {L : Launch} {g : Nat} {t : TState} {W : Nat → Value} {o : Opnd}

theorem readBits_oBits {w : Nat} (hp : plainB o = true)
    (hW : ∀ r, o = .reg r → t.regs r = some (W r)) : readBits L g t w o = oBits W w o := by
  cases o <;> simp [plainB] at hp
  · rename_i r
    simp only [readBits, readReg, hW r rfl, oBits, bind, Except.bind, pure, Except.pure]
    cases W r <;> rfl
  · rfl
  · rfl

theorem readValue_oVal {w : Nat} (hp : plainB o = true)
    (hW : ∀ r, o = .reg r → t.regs r = some (W r)) : readValue L g t w o = oVal W w o := by
  cases o <;> simp [plainB] at hp
  · rename_i r
    simp [readValue, readReg, hW r rfl, oVal, pure, Except.pure]
  · rfl
  · rfl

theorem readPred_oPred (hp : plainB o = true)
    (hW : ∀ r, o = .reg r → t.regs r = some (W r)) : readPred L g t o = oPred W o := by
  cases o <;> simp [plainB] at hp
  · rename_i r
    simp only [readPred, readReg, hW r rfl, oPred, bind, Except.bind, pure, Except.pure]
    cases W r <;> rfl
  · rfl
  · rfl

theorem readCvtFloat_oCvt {wide : Bool} {fmt : FloatFmt} {r : Nat}
    (hW : t.regs r = some (W r)) : readCvtFloat wide t fmt (.reg r) = oCvt W wide fmt (.reg r) := by
  simp only [readCvtFloat, readReg, hW, oCvt, bind, Except.bind, pure, Except.pure]

end

/-! ### Core's values of the forms -/

/-- `add` of a scalar integer type, with Core's symbolic-pointer arms. -/
def addW (W : Nat → Value) (w : Nat) (a b : Opnd) : Exec Value := do
  let va ← oVal W w a
  let vb ← oVal W w b
  match va, vb with
  | .ptr _ _ (.shared ..) _, .bits _ _ | .ptr _ _ (.local _) _, .bits _ _
  | .ptr _ _ .const _, .bits _ _ =>
    let delta ← oBits W w b
    offsetPointer w va (toSigned w delta)
  | .bits _ _, .ptr _ _ (.shared ..) _ | .bits _ _, .ptr _ _ (.local _) _
  | .bits _ _, .ptr _ _ .const _ =>
    let delta ← oBits W w a
    offsetPointer w vb (toSigned w delta)
  | _, _ =>
    let x ← oBits W w a; let y ← oBits W w b
    pure (.bits w (truncBits w (x + y)))

/-- `sub` of a scalar integer type, with Core's symbolic-pointer arm. -/
def subW (W : Nat → Value) (w : Nat) (a b : Opnd) : Exec Value := do
  let va ← oVal W w a
  match va with
  | .ptr _ _ (.shared ..) _ | .ptr _ _ (.local _) _ | .ptr _ _ .const _ =>
    let delta ← oBits W w b
    offsetPointer w va (-(toSigned w delta))
  | _ =>
    let x ← oBits W w a; let y ← oBits W w b
    pure (.bits w (truncBits w (x - y)))

/-- A logic operation of bits, or of predicates at width 1. -/
def logicW (W : Nat → Value) (w : Nat) (fb : BitVec 64 → BitVec 64 → BitVec 64)
    (fp : Bool → Bool → Bool) (a b : Opnd) : Exec Value :=
  if w = 1 then do
    let x ← oPred W a; let y ← oPred W b
    pure (.pred (fp x y))
  else do
    let x ← oBits W w a; let y ← oBits W w b
    pure (.bits w (fb x y))

/-- `cvt` from an integer to an integer, or from a float to a float. -/
def cvtW (W : Nat → Value) (c : CvtInstr) : Exec Value :=
  match c.dst, c.src, c.srcs with
  | .int dk dw, .int sk sw, [a] => do
    let v ← oVal W sw a
    match v with
    | .ptr w generic sp off =>
      let narrows : Bool := match sp with
        | .shared .. => true
        | _ => false
      if sk = .u ∧ dk = .u ∧ c.sat = false ∧ c.ext = .same ∧ w = sw ∧
          (dw = sw ∨ (generic = false ∧ (dw = 32 ∨ dw = 64) ∧ (sw ≤ dw ∨ narrows))) then
        pure (.ptr dw generic sp off)
      else throw .noRule
    | _ => do
      let x ← oBits W sw a
      match c.sat, sk, c.ext with
      | false, .u, .same => pure (.bits dw (truncBits dw x))
      | sat, sk, ext => pure (ext.extendBits dw (cvtIntBits sat dk dw sk sw x))
  | .float df, .float sf, [a] => do
    let some dfmt := df.fmt? | throw .noRule
    let some sfmt := sf.fmt? | throw .noRule
    let x ← oCvt W (sf != .bf16) sfmt a
    let x := if c.ftz ∧ sfmt = .f32 then sfmt.layout.flush x else x
    let ftz := c.ftz && dfmt == .f32
    let y ← match c.rnd with
      | none => widenElem c df dfmt.layout ftz x
      | some r => match r.mode? with
        | some m => cvtNum c df dfmt.layout m ftz 1 x
        | none => roundIntElem c r dfmt.layout ftz x
    pure (cvtFloatDst c.ext (y.toValue dfmt))
  | _, _, _ => throw .noRule

/-- **Core's value of an instruction of the forms above**, from the register values `W`. -/
def coreW (W : Nat → Value) : Op → Exec Value
  | .int ⟨.setp cmp none, ty, _, [some _], [a, b]⟩ => do
    let x ← oBits W ty.width a; let y ← oBits W ty.width b
    pure (.pred (compare cmp (ty.kind?.getD .b) ty.width x y))
  | .int ⟨.add, .int k w, false, [some _], [a, b]⟩ => addW W (DType.int k w).width a b
  | .int ⟨.sub, .int k w, false, [some _], [a, b]⟩ => subW W (DType.int k w).width a b
  | .int ⟨.mul .lo, ty, _, [some _], [a, b]⟩ => do
    let x ← oBits W ty.width a; let y ← oBits W ty.width b
    pure (.bits ty.width (truncBits ty.width (x * y)))
  | .int ⟨.prmt mode, _, _, [some _], [a, b, c]⟩ => do
    let x ← oBits W 32 a; let y ← oBits W 32 b; let z ← oBits W 32 c
    pure (.bits 32 (BitVec.ofNat 64 (prmtBits mode x.toNat y.toNat z.toNat)))
  | .int ⟨.selp, ty, _, [some _], [a, b, .reg p]⟩ => do
    let .pred pick := W p | throw .typeMismatch
    let v ← oVal W ty.width (if pick then a else b)
    unless v.bytes = ty.width / 8 do throw .typeMismatch
    pure v
  | .int ⟨.shl, ty, _, [some _], [a, b]⟩ => do
    let x ← oBits W ty.width a; let s ← oBits W 32 b
    pure (.bits ty.width (if s.toNat ≥ ty.width then 0 else truncBits ty.width (x <<< s.toNat)))
  | .int ⟨.shr, ty, _, [some _], [a, b]⟩ => do
    let x ← oBits W ty.width a; let s ← oBits W 32 b
    if ty.kind? == some .s then
      pure (.bits ty.width (truncBits ty.width
        (BitVec.ofInt 64 (toSigned ty.width x / 2 ^ min s.toNat ty.width))))
    else pure (.bits ty.width (if s.toNat ≥ ty.width then 0 else x >>> s.toNat))
  | .int ⟨.and, ty, _, [some _], [a, b]⟩ => logicW W ty.width (· &&& ·) (· && ·) a b
  | .int ⟨.or, ty, _, [some _], [a, b]⟩ => logicW W ty.width (· ||| ·) (· || ·) a b
  | .move ⟨.scalar, ty, [some _], [a]⟩ =>
    if ty = .pred then do pure (.pred (← oPred W a))
    else do
      let v ← oVal W ty.width a
      unless v.bytes = ty.width / 8 do throw .typeMismatch
      pure v
  | .move ⟨.pack, ty, [some _], [a, b]⟩ => do
    let x ← oVal W (ty.width / 2) a; let y ← oVal W (ty.width / 2) b
    unless x.bytes = ty.width / 16 ∧ y.bytes = ty.width / 16 do throw .typeMismatch
    pure (joinValue x y)
  | .cvt c => cvtW W c
  | _ => throw .noRule

/-- The outcome function of a `fn` item of Core's forms with source registers `srcs`. -/
def coreF (op : Op) (srcs : List Nat) (vs : List Value) : Exec Value := coreW (lk srcs vs) op

/-- No assumption has a local rule for `op` at `pc`. -/
def NoLocalRule (A : List Assumption) (L : Launch) (g pc : Nat) (op : Op) : Prop :=
  ∀ s : TState, s.pc = pc → ∀ a ∈ A, a.localRule L g s op = none

/-! ### The rules -/

/-- The closing tactic of the Core equations: the two sides are the same computation, the left
one ending in the state update. -/
syntax "core_close" : tactic
macro_rules
  | `(tactic| core_close) =>
    `(tactic| (simp_all only [bind, Except.bind, Except.map, pure, Except.pure] <;>
      repeat' (split <;> simp_all only [bind, Except.bind, Except.map, pure, Except.pure]) <;>
      (try (split_ifs <;> simp only [throw, throwThe, MonadExceptOf.throw, Except.map]))))

/-- Two-operand forms: the Boolean check. -/
abbrev Ok2 (op : Op) (rid : RuleId) (a b : Opnd) : Bool :=
  op.rule == some rid && plainB a && plainB b

section
variable {A : List Assumption} {L : Launch} {g : Nat}

theorem reg_of_mem {os : List Opnd} {o : Opnd} (ho : o ∈ os) {W : Nat → Value} {t : TState}
    (h : ∀ r ∈ regsOf os, t.regs r = some (W r)) : ∀ r, o = .reg r → t.regs r = some (W r) := by
  rintro r rfl
  exact h r (List.mem_flatMap.mpr ⟨_, ho, by simp [regOf]⟩)

/-- **A `fn` item of Core's forms reads Core's value**, from Core's equation at every state whose
source registers hold `W`. -/
theorem XItem.core_of {pc d : Nat} {op : Op} {srcs : List Nat} (hS : SegFreePc A pc)
    (hn : NoLocalRule A L g pc op)
    (hc : ∀ (t : TState) (W : Nat → Value), (∀ r ∈ srcs, t.regs r = some (W r)) →
      execLocal L g t op = (coreW W op).map fun v => PTX.next (setReg t d v)) :
    ∀ s : TState, s.pc = pc → (XItem.fn op d srcs (coreF op srcs)).Rule A L g s := by
  intro s hs W hW
  rw [hS.exec hs, execLocalRule_of_none (hn s hs),
    hc s (lk srcs (srcs.map W)) (fun r hr => by rw [lk_map hr]; exact hW r hr)]
  rfl

end

end
end PTX.Flow
