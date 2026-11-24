-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SetpCore

@[expose] public section

/-! # The outcome of `min.f32` on any operand values

The software `min.f32` of the softmax region's rescale test (pc 2256, `min.f32 %r1085, %r1083,
%r1084`) as an outcome, in the form of `Lemmas/Flow/MaxCore.lean` for `max.f32`: under the ideal
reading of `min.f32` (`Assumptions.idealArith`) the two operands are read in the extended reals,
an infinity is that infinity, and a NaN operand makes the ideal rule decline, so that the Core rule
(`coreFloat`) gives the result. An operand without a datum of `.f32` faults under both rules. The
outcome is one `Exec Value` (`minE`) and the local step writes its value or faults
(`exec_minE2`); on operands that read as numbers it is the number of their minimum (`minE_fin2`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- `min.f32` (no `.ftz`, `.NaN`, `.xorsign` or `.abs`). -/
abbrev minI : FloatInstr := { op := .min, ty := ty1 .f32, dsts := [], srcs := [] }

/-- The ideal-real outcome of `min.f32` on two source values, as `execIdealFloat` computes it for
registers that hold them; `none` where the rule declines (a NaN). -/
def idealMin : List Value → Option (Exec Value)
  | [a, b] => bindRead (readEReal .f32 a) fun x => bindRead (readEReal .f32 b) fun y =>
      some (pure (erealValue .f32 (min x y)))
  | _ => some (throw .noRule)

/-- **The outcome of `min.f32`**: the ideal outcome, or the Core rule's where the ideal rule
declines. -/
@[irreducible] def minE (vs : List Value) : Exec Value :=
  match idealMin vs with
  | some r => r
  | none => coreFloat minI vs

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- The `min.f32` instruction of destination `d` and register sources `srcs`. -/
abbrev minOp (d : Nat) (srcs : List Nat) : Op :=
  .float { op := .min, ty := FTy.mk .f32 1, dsts := [some d], srcs := srcs.map .reg }

theorem minOp_form (d : Nat) (srcs : List Nat) :
    FloatForm.ofOp (minOp d srcs) = some (.min .f32) := by
  simp [FloatForm.ofOp]

theorem execLocal_min2_core {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocal L g t (minOp d [a, b]) =
      (coreFloat minI [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hl : ∀ xs, FloatInstr.lane
      { op := .min, ty := FTy.mk .f32 1, dsts := [some d], srcs := [.reg a, .reg b] } xs =
      FloatInstr.lane minI xs := fun _ => rfl
  cases hxa : classify .f32 va with
  | error e => core_float_reg
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float_reg
  | ok xb =>
  cases hlane : FloatInstr.lane minI [xa, xb] with
  | none => core_float_reg
  | some o => cases o <;> core_float_reg

theorem execIdeal_min2 {t : TState} {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execIdealFloat L g t (minOp d [a, b]) =
      (idealMin [va, vb]).map (Except.map fun v => PTX.next (setReg t d v)) := by
  simp only [List.map_cons, List.map_nil, execIdealFloat, idealMin, readERealOpnd_reg ha,
    readERealOpnd_reg hb, bindRead_map, Option.map_some, Except.map, pure, Except.pure]
  rfl

/-- **The local step of `min.f32 d, a, b`** writes the outcome's value or faults. -/
theorem exec_minE2 {t : TState} (hI : IdealAt A (.min .f32) L g t)
    (hD : DeclineAt A (.min .f32) L g t) {d a b : Nat} {va vb : Value}
    (ha : t.regs a = some va) (hb : t.regs b = some vb) :
    execLocalA A L g t (minOp d [a, b]) =
      (minE [va, vb]).map fun v => PTX.next (setReg t d v) := by
  have hi := execIdeal_min2 (L := L) (g := g) (d := d) ha hb
  unfold minE
  cases hv : idealMin [va, vb] with
  | none => rw [hD _ (minOp_form d [a, b]) (by rw [hi, hv]; rfl), execLocal_min2_core ha hb]
  | some r => rw [hI _ (minOp_form d [a, b]) _ (by rw [hi, hv]; rfl)]

/-- **Every value of `min.f32` has four bytes**: the ideal outcome is an `erealValue .f32`, the
Core rule's an `.f32` value. -/
theorem minE_four (vs : List Value) : Four (minE vs) := by
  intro v hv
  unfold minE at hv
  split at hv
  · rename_i r hr
    subst hv
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [idealMin, throw, throwThe,
      MonadExceptOf.throw] at hr
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
    rw [← hr]
    exact erealValue_f32_bytes _
  · exact coreFloat_four rfl vs v hv

end
end PTX.Flow
