-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Cvt

@[expose] public section

/-! # Conversions to a pair of `bf16`

A proof tool, the `bf16` counterpart of `Cvt.lean`'s pair of halves. A reading of
`cvt.rn.bf16x2.f32 d, a, b` that takes both operands as extended reals writes their pair of `bf16`
values (`b`'s in the low half); an operand without an `.f32` datum makes it fault; a NaN operand
makes such a reading decline, so that the Core conversion rule converts the two data
(`coreCvtBf`, `execLocal_cvtBf`). `cvtBfE` is that outcome on the operands' values; on two
`.f32` numbers it is the pair of the two numbers as `bf16` payloads (`cvtBfE_float`). -/

namespace PTX.Flow
open PTX

noncomputable section

variable {L : Launch} {g : Nat}

/-- `cvt.rn.bf16x2.f32 d, a, b`. -/
abbrev cvtBfInstr (d a b : Nat) : CvtInstr :=
  { dst := .packed (.float .bf16) 2, src := .float .f32, rnd := some .rn, d := d,
    srcs := [.reg a, .reg b] }

/-- The pair the Core rule of `cvt.rn.bf16x2.f32 d, a, b` (THREAD-CVT) writes for the value `va` of
`a` and `vb` of `b`: each operand's datum rounded to the nearest `.bf16`, `b`'s in the low half. -/
def coreCvtBf (va vb : Value) : Exec Value := do
  let xa ← classify .f32 va
  let xb ← classify .f32 vb
  let hi ← cvtNum (cvtBfInstr 0 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 xa
  let lo ← cvtNum (cvtBfInstr 0 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 xb
  pure (.pair (lo.toValue .bf16) (hi.toValue .bf16))

/-- **The Core rule of a conversion to a pair of `bf16`** writes the pair `coreCvtBf` of its
operands' values. -/
theorem execLocal_cvtBf {t : TState} {d a b : Nat} {va vb : Value} (ha : t.regs a = some va)
    (hb : t.regs b = some vb) :
    execLocal L g t (.cvt (cvtBfInstr d a b)) =
      (coreCvtBf va vb).map fun v => PTX.next (setReg t d v) := by
  have hr : (Op.cvt (cvtBfInstr d a b)).rule = some .threadCvt := by
    simp [Op.rule, CvtInstr.rule, CvtInstr.exact]
  have hc : cvtNum (cvtBfInstr d a b) = cvtNum (cvtBfInstr 0 0 0) := rfl
  simp only [execLocal, hr]
  simp [execCvt, readCvtFloat, readReg, ha, hb, cvtScales, FType.layout?, FType.fmt?, cvtPack,
    CvtRnd.mode?, hc, coreCvtBf]
  generalize classify .f32 va = ca
  generalize classify .f32 vb = cb
  rcases ca with _ | xa
  · rfl
  rcases cb with _ | xb
  · rfl
  simp only [bind, Except.bind, Except.map, Functor.map]
  generalize cvtNum (cvtBfInstr 0 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 xa = ya
  generalize cvtNum (cvtBfInstr 0 0 0) .bf16 FloatFmt.bf16.layout .rn false 1 xb = yb
  rcases ya with _ | ya <;> rcases yb with _ | yb <;> rfl

/-- What `cvt.rn.bf16x2.f32 d, a, b` writes for the values `va`, `vb` of its operands under a
reading of both operands as extended reals: the pair of their `bf16` values, `vb`'s in the low
half; the fault of the first operand the reading rejects; and the Core rule's pair when it declines
a NaN operand. -/
def cvtBfE (va vb : Value) : Exec Value :=
  match Assumption.readEReal .f32 va with
  | some (.error e) => .error e
  | some (.ok x) => match Assumption.readEReal .f32 vb with
    | some (.error e) => .error e
    | some (.ok y) => .ok (.pair (Assumption.erealValue .bf16 y) (Assumption.erealValue .bf16 x))
    | none => coreCvtBf va vb
  | none => coreCvtBf va vb

theorem erealValue_bf16_coe (z : ℝ) :
    Assumption.erealValue .bf16 (z : EReal) = .float .bf16 z := by
  unfold Assumption.erealValue
  rw [ite_eq_right (EReal.coe_ne_top z), ite_eq_right (EReal.coe_ne_bot z)]
  rfl

/-- **Two single-precision numbers convert to the pair of their `bf16` payloads.** -/
theorem cvtBfE_float (x y : ℝ) :
    cvtBfE (.float .f32 x) (.float .f32 y) = .ok (.pair (.float .bf16 y) (.float .bf16 x)) := by
  simp [cvtBfE, Assumption.readEReal, erealValue_bf16_coe, pure, Except.pure]

theorem toValue_bf16_bytes (x : FVal) : (x.toValue .bf16).bytes = 2 := by
  rcases x with neg | q | neg | p
  · cases neg <;> rfl
  · rfl
  · rfl
  · cases p <;> rfl

theorem erealValue_bf16_bytes (x : EReal) : (Assumption.erealValue .bf16 x).bytes = 2 := by
  unfold Assumption.erealValue
  split_ifs <;> rfl

theorem pair_bf16_bytes (x y : FVal) :
    (Value.pair (x.toValue .bf16) (y.toValue .bf16)).bytes = 4 := by
  show (x.toValue .bf16).bytes + (y.toValue .bf16).bytes = 4
  rw [toValue_bf16_bytes, toValue_bf16_bytes]

/-- **A converted pair has four bytes.** -/
theorem cvtBfE_four {va vb v : Value} (h : cvtBfE va vb = .ok v) : v.bytes = 4 := by
  have hc : ∀ w, coreCvtBf va vb = .ok w → w.bytes = 4 := by
    intro w hw
    simp only [coreCvtBf, bind, Except.bind, pure, Except.pure] at hw
    repeat' split at hw
    all_goals first
      | (cases hw; exact pair_bf16_bytes _ _)
      | cases hw
  unfold cvtBfE at h
  repeat' split at h
  all_goals first
    | exact hc v h
    | (cases h
       show (Assumption.erealValue .bf16 _).bytes + (Assumption.erealValue .bf16 _).bytes = 4
       rw [erealValue_bf16_bytes, erealValue_bf16_bytes])
    | cases h

end
end PTX.Flow
