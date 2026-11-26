-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatOutcome
public import Lemmas.Flow.EmuStep

@[expose] public section

/-! # Core's values of packed conversions and packed `bf16` products

A proof tool, generic over the kernel (promoted from FlashMLA's dequantizer readings,
`Proof2/Dequant/GenRules.lean`): Core's value, from the values of the source registers, of

* `cvt.rn.bf16x2.<sf>x2 d, a` from a packed pair of 8-bit floats (`cvtPair8I`, `coreCvtPair8`,
  `execLocal_cvtPair8`, for `sf` `.e4m3` or `.ue8m0`);
* `mul.bf16x2 d, a, b` (`mulBf16x2I`, `execLocal_mulBf16x2`, the value `coreFloat`).

A kernel whose assumption reads these instructions ideally gives its outcome function as its
reading where the assumption applies, else these values. The integer forms and the widening
`cvt.u64.u32` are Core's forms of `Lemmas/Flow/OutCore.lean` (`coreW`); the bits of a register
value are `readBitsOf` (`readBits_reg_bitsOf`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {L : Launch} {g : Nat}

/-- `cvt.rn.bf16x2.<sf>x2 d, a`. -/
def cvtPair8I (sf : FType) (a d : Nat) : CvtInstr where
  dst := .packed (.float .bf16) 2
  src := .packed (.float sf) 2
  rnd := some .rn
  d := d
  srcs := [.reg a]

/-- **Core's conversion** of a packed pair of 8-bit floats `sf` to a pair of `bf16`. -/
def coreCvtPair8 (sf : FType) (v : Value) : Exec Value := do
  let (xl, xh) ← packedElems sf v
  let el ← widenElem (cvtPair8I sf 0 0) .bf16 FloatFmt.bf16.layout false xl
  let eh ← widenElem (cvtPair8I sf 0 0) .bf16 FloatFmt.bf16.layout false xh
  cvtPack .bf16 FloatFmt.bf16.layout el eh

set_option linter.unusedSimpArgs false in
theorem execLocal_cvtPair8 {t : TState} {sf : FType} {a d : Nat} {v : Value}
    (hsf : sf = .e4m3 ∨ sf = .ue8m0) (h : t.regs a = some v) :
    execLocal L g t (.cvt (cvtPair8I sf a d)) =
      (coreCvtPair8 sf v).map fun w => PTX.next (setReg t d w) := by
  have hr : (Op.cvt (cvtPair8I sf a d)).rule = some .threadCvt := by
    rcases hsf with rfl | rfl <;> simp [Op.rule, CvtInstr.rule, CvtInstr.exact, cvtPair8I]
  have hw : ∀ x, widenElem (cvtPair8I sf a d) .bf16 FloatFmt.bf16.layout false x =
      widenElem (cvtPair8I sf 0 0) .bf16 FloatFmt.bf16.layout false x := fun _ => rfl
  simp only [execLocal, hr]
  rcases hsf with rfl | rfl <;>
  · simp only [cvtPair8I] at hw
    change execCvt L g t (cvtPair8I _ a d) = _
    simp only [execCvt, cvtPair8I, readValue, readReg, h, FType.layout?, FType.fmt?, cvtScales,
      CvtRnd.mode?, Bind.bind, Except.bind, Pure.pure, Except.pure, reduceCtorEq, ↓reduceIte,
      Option.map, Option.bind, hw, coreCvtPair8, or_false, false_or, or_true]
    rcases packedElems _ v with e | ⟨xl, xh⟩
    · rfl
    simp only
    rcases widenElem _ FType.bf16 FloatFmt.bf16.layout false xl with e | el
    · rfl
    simp only
    rcases widenElem _ FType.bf16 FloatFmt.bf16.layout false xh with e | eh
    · rfl
    simp only
    rcases cvtPack FType.bf16 FloatFmt.bf16.layout el eh with e | w <;> rfl

/-- `mul.bf16x2 d, a, b`. -/
def mulBf16x2I (a b d : Nat) : FloatInstr where
  op := .mul
  ty := ⟨.bf16, 2⟩
  dsts := [some d]
  srcs := [.reg a, .reg b]

theorem mulBf16x2I_fields (a b d : Nat) : (mulBf16x2I a b d).op = .mul ∧
    (mulBf16x2I a b d).ty = ⟨.bf16, 2⟩ ∧ (mulBf16x2I a b d).srcTys = [] ∧
    (mulBf16x2I a b d).cmpTy = none ∧ (mulBf16x2I a b d).mode = .ieee ∧
    (mulBf16x2I a b d).dsts = [some d] ∧ (mulBf16x2I a b d).srcs = [.reg a, .reg b] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The Core rule's steps for `mul.bf16x2`. -/
syntax "bf_core" : tactic
macro_rules
  | `(tactic| bf_core) => `(tactic|
    simp [execLocal, Op.rule, FloatInstr.rule, execFloat, boolCombine, coreFloat,
      mulBf16x2I_fields, FloatFmt.bytes, floatLane, readValue, readReg, bind, Except.bind,
      Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, *])

/-- **Core's `mul.bf16x2`** of two registers: `coreFloat` of their values. -/
theorem execLocal_mulBf16x2 {t : TState} {a b d : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (.float (mulBf16x2I a b d)) =
      (coreFloat (mulBf16x2I 0 0 0) [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane (mulBf16x2I a b d) = FloatInstr.lane (mulBf16x2I 0 0 0) := rfl
  have h2 : List.range 2 = [0, 1] := rfl
  cases hxa : classify .bf16 (splitValue 32 va).1 with
  | error e => bf_core
  | ok xa =>
  cases hxb : classify .bf16 (splitValue 32 vb).1 with
  | error e => bf_core
  | ok xb =>
  cases hl0 : FloatInstr.lane (mulBf16x2I 0 0 0) [xa, xb] with
  | none => bf_core
  | some o =>
  cases hya : classify .bf16 (splitValue 32 va).2 with
  | error e => bf_core
  | ok ya =>
  cases hyb : classify .bf16 (splitValue 32 vb).2 with
  | error e => bf_core
  | ok yb =>
  cases hl1 : FloatInstr.lane (mulBf16x2I 0 0 0) [ya, yb] with
  | none => bf_core
  | some o' => cases o <;> cases o' <;> bf_core

end
end PTX.Flow
