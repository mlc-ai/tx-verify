-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatOutcome

@[expose] public section

/-! # The outcome of an approximate reciprocal on any operand value

A proof tool. Under an approximate-as-exact assumption (ASM-APPROX) that names `rcp.approx.f32`,
`rcp.approx{.ftz}.f32 d, a` reads its operand as a finite real and writes the exact `1 / x`; a
zero operand faults, and an infinite or NaN operand makes the rule decline, so that the Core rule
(THREAD-FLOAT-APPROX, the table of `rcp.approx`) gives the result. The outcome on the operand's
value is one `Exec Value` (`rcpE`): the exact reciprocal where the rule applies, the Core rule's
where it declines. Its local step writes the outcome or faults (`exec_rcpE`); on a nonzero
finite operand the outcome is the exact reciprocal (`rcpE_fin`), and every value of it has four
bytes (`rcpE_four`).

`ApproxAt` and `ApproxDeclineAt` are the state-wise forms of `ApproxFor` and `ApproxDecline`. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `A` reads the approximate form `f` as its exact function at the state `t`. -/
def ApproxAt (A : List Assumption) (f : ApproxForm) (L : Launch) (g : Nat) (t : TState) :
    Prop :=
  ∀ op, ApproxForm.ofOp op = some f → ∀ e, execApproxExact t op = some e →
    execLocalA A L g t op = e

/-- `A` leaves an approximation of the form `f` whose operand is infinite or NaN to the Core
rule at the state `t`. -/
def ApproxDeclineAt (A : List Assumption) (f : ApproxForm) (L : Launch) (g : Nat)
    (t : TState) : Prop :=
  ∀ op, ApproxForm.ofOp op = some f → execApproxExact t op = none →
    execLocalA A L g t op = execLocal L g t op

/-- `rcp.approx{.ftz}.f32`. -/
abbrev rcpI (fz : Bool) : FloatInstr :=
  { op := .rcp, ty := ty1 .f32, mode := .approx, ftz := fz, dsts := [], srcs := [] }

theorem execLocal_rcp_core {t : TState} {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocal L g t (.float { rcpI fz with dsts := [some d], srcs := [a] }) =
      (coreFloat (rcpI fz) [va]).map fun v => PTX.next (setReg t d v) := by
  have hl : FloatInstr.lane { rcpI fz with dsts := [some d], srcs := [a] } =
      FloatInstr.lane (rcpI fz) := rfl
  obtain ⟨ha, -⟩ := ha
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hlane : FloatInstr.lane (rcpI fz) [xa] with
  | none => core_float
  | some o => cases o <;> core_float

/-- The exact reciprocal of a finite operand (ASM-APPROX), `none` where the operand is infinite
or NaN. -/
def rcpVal (va : Value) : Option (Exec Value) :=
  bindRead (finiteVal va) fun x =>
    some (if x = 0 then throw .badValue else pure (.float .f32 (1 / x)))

/-- **The outcome of an approximate reciprocal** read as its exact function: the exact value, or
the Core table's where the rule declines. -/
@[irreducible] def rcpE (fz : Bool) (va : Value) : Exec Value :=
  match rcpVal va with
  | some r => r
  | none => coreFloat (rcpI fz) [va]

/-- **The local step of an approximate reciprocal** writes the outcome `rcpE` or faults. -/
theorem exec_rcpE {t : TState} (hA : ApproxAt A (.rcp .f32) L g t)
    (hD : ApproxDeclineAt A (.rcp .f32) L g t) {fz : Bool} {d : Nat} {a : Opnd} {va : Value}
    (ha : OpndIs L g t a va) :
    execLocalA A L g t (.float { rcpI fz with dsts := [some d], srcs := [a] }) =
      (rcpE fz va).map fun v => PTX.next (setReg t d v) := by
  have hf : ApproxForm.ofOp (.float { rcpI fz with dsts := [some d], srcs := [a] }) =
      some (.rcp .f32) := by simp [ApproxForm.ofOp]
  have hI : execApproxExact t (.float { rcpI fz with dsts := [some d], srcs := [a] }) =
      (rcpVal va).map (Except.map fun v => PTX.next (setReg t d v)) := by
    simp only [execApproxExact, rcpVal, readFinite_of ha.2, bindRead_map]
    rcases finiteVal va with _ | (e | x)
    · rfl
    · rfl
    simp only [bindRead]
    split_ifs <;> rfl
  unfold rcpE
  cases hv : rcpVal va with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_rcp_core ha]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- **The reciprocal of a nonzero number** is the exact one. -/
theorem rcpE_fin {fz : Bool} {va : Value} {x : ℝ} (hx : valFloat .f32 va = .ok x) (h0 : x ≠ 0) :
    rcpE fz va = .ok (.float .f32 (1 / x)) := by
  simp [rcpE, rcpVal, finiteVal_of hx, bindRead, h0, pure, Except.pure]

/-- Every value of the outcome has four bytes. -/
theorem rcpE_four (fz : Bool) (va : Value) : Four (rcpE fz va) := by
  intro v hv
  unfold rcpE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    split_ifs at hr
    · cases hr
    · cases hr; rfl
  · exact coreFloat_four rfl [va] v hv

end
end PTX.Flow
