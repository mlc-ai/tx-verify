-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SetpCore

@[expose] public section

/-! The ideal and fallback Core outcomes of a scalar minimum on two register operands. -/

namespace PTX.Flow.MinCore
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

end
end PTX.Flow.MinCore
