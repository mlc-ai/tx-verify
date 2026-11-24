-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MaxCore

@[expose] public section

/-! # The outcome of a floating comparison on any operand values

A proof tool. Under an ideal-real assumption (ASM-IDEAL) that names `setp.f32`, the comparison
`setp.cmp{.ftz}.f32 p, a, b` (ordered or unordered, one destination, no Boolean operation) reads
its operands in the extended reals: an operand without a value of the format faults, an infinity
is that infinity, and a NaN operand makes the rule decline, so that the Core rule (THREAD-FLOAT)
compares the operands' data. The outcome on the operands' values is one `Exec Bool`
(`setpE`): the comparison of the extended reals where the ideal rule applies, the Core rule's
where it declines. Its local step writes the outcome to `p` or faults (`exec_setpE`); on finite
operands the outcome is the comparison of the reals (`setpE_fin`).

`DeclineAt` (`Lemmas/Flow/MaxCore.lean`) states, at one state, that an assumption list leaves a
declined form to the Core rule. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- `setp.c{.ftz}.f32` with one destination and no Boolean operation. -/
abbrev setpI (c : FCmp) (fz : Bool) : FloatInstr :=
  { op := .setp c none, ty := ty1 .f32, ftz := fz, dsts := [], srcs := [] }

/-- The Boolean the Core rule (THREAD-FLOAT) of a one-lane comparison `f` writes, from the values
`va`, `vb` of its sources: the comparison of their data. -/
def coreSetp (f : FloatInstr) (va vb : Value) : Exec Bool := do
  let xa ← classify f.ty.fmt va
  let xb ← classify f.ty.fmt vb
  match f.lane [xa, xb] with
  | some (.pred r) => pure r
  | _ => throw .noRule

theorem execLocal_setp_core {t : TState} {c : FCmp} {fz : Bool} {p : Nat} {a b : Opnd}
    {va vb : Value} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocal L g t (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      (coreSetp (setpI c fz) va vb).map fun r => PTX.next (setReg t p (.pred r)) := by
  have hl : FloatInstr.lane { setpI c fz with dsts := [some p], srcs := [a, b] } =
      FloatInstr.lane (setpI c fz) := rfl
  obtain ⟨ha, -⟩ := ha; obtain ⟨hb, -⟩ := hb
  unfold coreSetp
  cases hxa : classify .f32 va with
  | error e => core_float
  | ok xa =>
  cases hxb : classify .f32 vb with
  | error e => core_float
  | ok xb =>
  cases hlane : FloatInstr.lane (setpI c fz) [xa, xb] with
  | none => core_float
  | some o =>
    cases o with
    | pred r => core_float
    | val v => simp [FloatInstr.lane, FloatInstr.rule] at hlane

/-- The comparison operator of an ordered or unordered floating comparison. -/
def fcmpBase : FCmp → Option Cmp
  | .ord c | .unord c => some c
  | _ => none

/-- The ideal-real outcome (ASM-IDEAL) of the comparison `c` on source values, as
`execIdealFloat` computes it for operands that hold them; `none` where the rule declines (a NaN
operand). -/
def idealSetp (c : FCmp) (va vb : Value) : Option (Exec Bool) :=
  match fcmpBase c with
  | some cmp => bindRead (readEReal .f32 va) fun x => bindRead (readEReal .f32 vb) fun y =>
      some (pure (erealCompare cmp x y))
  | none => some (throw .noRule)

/-- **The outcome of a comparison** under an ideal-real assumption that leaves its declines to
the Core rule: the ideal outcome, or the Core rule's where the ideal rule declines. -/
@[irreducible] def setpE (c : FCmp) (fz : Bool) (va vb : Value) : Exec Bool :=
  match idealSetp c va vb with
  | some r => r
  | none => coreSetp (setpI c fz) va vb

theorem bindRead_map_bool {α : Type} (x : Option (Exec α)) (k : α → Option (Exec Bool))
    (F : Bool → TState) :
    (bindRead x k).map (Except.map F) = bindRead x fun a => (k a).map (Except.map F) := by
  rcases x with _ | (e | a) <;> rfl

/-- **The local step of a comparison** with operands that hold `va` and `vb` and no infinite
constant operand: it writes the outcome `setpE` or faults. -/
theorem exec_setpE {t : TState} (hA : IdealAt A (.setp .f32) L g t)
    (hD : DeclineAt A (.setp .f32) L g t) {c : FCmp} {cmp : Cmp} {fz : Bool} {p : Nat}
    {a b : Opnd} {va vb : Value} (hc : c = .ord cmp ∨ c = .unord cmp)
    (hinfa : isInfConst a = false) (hinfb : isInfConst b = false)
    (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) :
    execLocalA A L g t (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      (setpE c fz va vb).map fun r => PTX.next (setReg t p (.pred r)) := by
  have hf : FloatForm.ofOp (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      some (.setp .f32) := by
    rcases hc with rfl | rfl <;> simp [FloatForm.ofOp, hinfa, hinfb]
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  have hI : execIdealFloat L g t (.float { setpI c fz with dsts := [some p], srcs := [a, b] }) =
      (idealSetp c va vb).map (Except.map fun r => PTX.next (setReg t p (.pred r))) := by
    rw [idealSetp, hbase]
    rcases hc with rfl | rfl <;>
    · simp only [execIdealFloat, ha.2, hb.2, bindRead_map_bool]
      rcases readEReal .f32 va with _ | (e | x)
      · rfl
      · rfl
      rcases readEReal .f32 vb with _ | (e | y) <;> rfl
  unfold setpE
  cases hv : idealSetp c va vb with
  | none => rw [hD _ hf (by rw [hI, hv]; rfl), execLocal_setp_core ha hb]
  | some r => rw [hA _ hf _ (by rw [hI, hv]; rfl)]

/-- **A comparison of numbers** is the comparison of the reals. -/
theorem setpE_fin {c : FCmp} {cmp : Cmp} {fz : Bool} {va vb : Value} {x y : ℝ}
    (hc : c = .ord cmp ∨ c = .unord cmp) (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) :
    setpE c fz va vb = .ok (erealCompare cmp (x : EReal) (y : EReal)) := by
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  simp only [setpE, idealSetp, hbase, readEReal_of_valFloat hx, readEReal_of_valFloat hy,
    bindRead, pure, Except.pure]

/-- A comparison faults where the first operand's read faults. -/
theorem setpE_error {c : FCmp} {cmp : Cmp} {fz : Bool} {va vb : Value} {f : Fault}
    (hc : c = .ord cmp ∨ c = .unord cmp) (hx : readEReal .f32 va = some (.error f)) :
    setpE c fz va vb = .error f := by
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  simp only [setpE, idealSetp, hbase, hx, bindRead]

/-- A value that `classify` reads as an `.f32` datum has four bytes. -/
theorem classify_f32_bytes {v : Value} {x : FVal} (h : classify .f32 v = .ok x) :
    v.bytes = 4 := by
  cases v with
  | nan f =>
    by_cases hf : f = .f32
    · subst hf; rfl
    · simp [classify, hf, throw, throwThe, MonadExceptOf.throw] at h
  | _ =>
    simp only [classify] at h
    split at h
    · split_ifs at h with hb
      exact hb
    · cases h

/-- A value that the ideal rule reads as an `.f32` operand has four bytes. -/
theorem readEReal_f32_bytes {v : Value} {x : EReal} (h : readEReal .f32 v = some (.ok x)) :
    v.bytes = 4 := by
  have hd : ∀ {e : Exec FVal}, readEReal.ofDatum e = some (.ok x) → ∃ y, e = .ok y := by
    intro e he
    rcases e with e | y
    · simp [readEReal.ofDatum] at he
    · exact ⟨y, rfl⟩
  cases v with
  | float f y =>
    by_cases hf : f = .f32
    · subst hf; rfl
    · simp only [readEReal, hf, ↓reduceIte] at h
      obtain ⟨y, hy⟩ := hd h
      exact classify_f32_bytes hy
  | _ =>
    simp only [readEReal] at h
    obtain ⟨y, hy⟩ := hd h
    exact classify_f32_bytes hy

/-- **A comparison that does not fault reads a four-byte first operand.** -/
theorem setpE_bytes {c : FCmp} {cmp : Cmp} {fz : Bool} {va vb : Value} {r : Bool}
    (hc : c = .ord cmp ∨ c = .unord cmp) (h : setpE c fz va vb = .ok r) : va.bytes = 4 := by
  have hbase : fcmpBase c = some cmp := by rcases hc with rfl | rfl <;> rfl
  unfold setpE at h
  split at h
  · rename_i e he
    subst h
    simp only [idealSetp, hbase] at he
    obtain ⟨x, hx, -⟩ := bindRead_ok he
    exact readEReal_f32_bytes hx
  · unfold coreSetp at h
    obtain ⟨x, hx, -⟩ := exec_bind_ok h
    exact classify_f32_bytes hx

end
end PTX.Flow
