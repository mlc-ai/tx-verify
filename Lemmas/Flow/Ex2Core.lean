-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RcpCore

@[expose] public section

/-! # The outcome of an approximate power of two on any operand value

A proof tool. Under an approximate-as-exact assumption (ASM-APPROX) that names
`ex2.approx.f32`, `ex2.approx{.ftz}.f32 d, a` reads its operand as a finite real `x` and writes
the exact `2 ^ x`; an operand without a datum of `.f32` faults, and an infinite or NaN operand
makes the rule decline, so that the Core rule (THREAD-FLOAT-APPROX, the table of `ex2.approx`)
gives the result. The outcome on the operand's value is one `Exec Value` (`ex2E`): the exact
power where the rule applies, the Core rule's where it declines. Its local step writes the
outcome or faults (`exec_ex2E`); on a finite operand the outcome is the exact power
(`ex2E_fin`), and every value of it has four bytes (`ex2E_four`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `ex2.approx{.ftz}.f32`. -/
abbrev ex2I (fz : Bool) : FloatInstr :=
  { op := .ex2, ty := ty1 .f32, mode := .approx, ftz := fz, dsts := [], srcs := [] }

theorem execLocal_ex2_core {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { ex2I fz with dsts := [some d], srcs := [a] }) =
      (coreFloat (ex2I fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { ex2I fz with dsts := [some d], srcs := [a] } =
      FloatInstr.lane (ex2I fz) := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane (ex2I fz) [xa] with
  | none => core_float
  | some o => cases o <;> core_float

/-- The exact power of two of a finite operand (ASM-APPROX), `none` where the operand is infinite
or NaN. -/
def ex2Val (va : Value) : Option (Exec Value) :=
  bindRead (finiteVal va) fun x => some (pure (.float .f32 (Real.rpow 2 x)))

/-- **The outcome of an approximate power of two** read as its exact function: the exact value,
or the Core table's where the rule declines. -/
@[irreducible] def ex2E (fz : Bool) (va : Value) : Exec Value :=
  match ex2Val va with
  | some r => r
  | none => coreFloat (ex2I fz) [va]

/-- **The local step of an approximate power of two** writes the outcome `ex2E` or faults. -/
theorem exec_ex2E {t : TState} (hA : ApproxAt A (.ex2 .f32) L g t)
    (hD : ApproxDeclineAt A (.ex2 .f32) L g t) {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA A L g t (.float { ex2I fz with dsts := [some d], srcs := [a] }) =
      (ex2E fz va).map fun v => PTX.next (setReg t d v) := by
  have hf : ApproxForm.ofOp (.float { ex2I fz with dsts := [some d], srcs := [a] }) =
      some (.ex2 .f32) := by simp [ApproxForm.ofOp]
  have hI : execApproxExact t (.float { ex2I fz with dsts := [some d], srcs := [a] }) =
      (ex2Val va).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execApproxExact, ex2Val, readFinite_of ha.2, bindRead_map]
    rcases finiteVal va with _ | (e | x)
    · rfl
    · rfl
    rfl
  unfold ex2E
  cases hv : ex2Val va with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_ex2_core ha]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- **The power of two of a number** is the exact one. -/
theorem ex2E_fin {fz : Bool} {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) :
    ex2E fz va = .ok (.float .f32 (Real.rpow 2 x)) := by
  simp [ex2E, ex2Val, finiteVal_of hx, bindRead, pure, Except.pure]

/-- Every value of the outcome has four bytes. -/
theorem ex2E_four (fz : Bool) (va : Value) : Four (ex2E fz va) := by
  intro v hv
  unfold ex2E at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    cases hr; rfl
  · exact coreFloat_four rfl [va] v hv

end
end PTX.Flow
