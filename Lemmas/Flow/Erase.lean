-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Roles
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # A value machine over a control machine

A proof tool, generic over the kernel. A value (data) machine `C'` follows a thread as a
control machine `C` does, with more in its states (the words a role read, the values its float
runs computed). `Erases C' C er`: the erasure `er` maps the first state to the first state and
every followed step of `C'` to a step of `C` (a value machine may stop following, `some none`,
where its control machine goes on). Erasure is kept by the glue (`Erases.glue`), the stubs
(`Erases.withStubs`), the ledger (`Erases.counted`) and so by a role thread whose roles each
erase (`Erases.roleThread`); along a trace a followed value state erases to the control state
on the same prefix (`Erases.stateAt`). -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- `C'` erases to `C` by `er`. -/
structure Erases (C' C : Code K A L g) (er : C'.D → C.D) : Prop where
  init : er C'.init = C.init
  next : ∀ {d e d'}, C'.next d e = some (some d') → C.next (er d) e = some (some (er d'))

/-- A machine erases to itself. -/
theorem Erases.rfl' (C : Code K A L g) : Erases C C id := ⟨rfl, fun h => h⟩

/-- Along a list of events, a followed state erases to a followed state. -/
theorem Erases.after {C' C : Code K A L g} {er : C'.D → C.D} (h : Erases C' C er) :
    ∀ (es : List Event) (a : C'.D) {s : C'.D},
      C'.toMachine.after (some a) es = some (some s) →
      C.toMachine.after (some (er a)) es = some (some (er s)) := by
  intro es
  induction es with
  | nil => intro a s hs; cases hs; rfl
  | cons e es ih =>
    intro a s hs
    change (C'.next a e).bind _ = _ at hs
    change (C.next (er a) e).bind _ = _
    rcases hn : C'.next a e with _ | _ | b
    · rw [hn] at hs; cases hs
    · rw [hn] at hs
      have dead : ∀ l, C'.toMachine.after none l = some none := by
        intro l
        induction l with
        | nil => rfl
        | cons _ _ ih => exact ih
      change C'.toMachine.after none es = _ at hs
      rw [dead] at hs
      cases hs
    · rw [hn] at hs
      rw [h.next hn]
      exact ih _ hs

/-- The erasure of a glued state: the first fragment's states stay, a role's state erases. -/
def eraseSum {P : Code K A L g} {ι : Type} {R' R : ι → Code K A L g}
    (er : ∀ i, (R' i).D → (R i).D) : P.D ⊕ (Σ i, (R' i).D) → P.D ⊕ (Σ i, (R i).D)
  | .inl d => .inl d
  | .inr ⟨i, d⟩ => .inr ⟨i, er i d⟩

/-- **The glue keeps erasure**: the same first fragment and exits, roles that erase. -/
theorem Erases.glue {P : Code K A L g} {ι : Type} {R' R : ι → Code K A L g}
    {exit : P.D → Option ι} {er : ∀ i, (R' i).D → (R i).D} (h : ∀ i, Erases (R' i) (R i) (er i)) :
    Erases (Code.glue P R' exit) (Code.glue P R exit) (eraseSum er) := by
  have hen : ∀ d, eraseSum er (enter P R' exit d) = enter P R exit d := by
    intro d
    unfold enter
    cases exit d with
    | none => rfl
    | some i => simp only [eraseSum, (h i).init]
  refine ⟨hen P.init, fun {d e d'} hn => ?_⟩
  cases d with
  | inl d =>
    change (P.next d e).map (Option.map (enter P R' exit)) = _ at hn
    change (P.next d e).map (Option.map (enter P R exit)) = _
    rcases hp : P.next d e with _ | _ | b
    · rw [hp] at hn; cases hn
    · rw [hp] at hn; cases hn
    · rw [hp] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      simp only [Option.map_some, hen]
  | inr a =>
    obtain ⟨i, d⟩ := a
    change ((R' i).next d e).map
      (Option.map fun d' => (Sum.inr ⟨i, d'⟩ : P.D ⊕ (Σ i, (R' i).D))) = _ at hn
    change ((R i).next (er i d) e).map
      (Option.map fun d' => (Sum.inr ⟨i, d'⟩ : P.D ⊕ (Σ i, (R i).D))) = _
    rcases hp : (R' i).next d e with _ | _ | b
    · rw [hp] at hn; cases hn
    · rw [hp] at hn; cases hn
    · rw [hp] at hn
      simp only [Option.map_some, Option.some.injEq] at hn
      subst hn
      rw [(h i).next hp]
      rfl

/-- **The ledger keeps erasure.** -/
theorem Erases.counted {C' C : Code K A L g} {er : C'.D → C.D} (h : Erases C' C er) {κ : Type}
    (cls : κ → Event → Bool) :
    Erases (C'.counted cls) (C.counted cls) (fun d => (er d.1, d.2)) := by
  refine ⟨by simp only [Code.counted, h.init], fun {d e d'} hn => ?_⟩
  change (C'.next d.1 e).map _ = _ at hn
  change (C.next (er d.1) e).map _ = _
  rcases hp : C'.next d.1 e with _ | _ | b
  · rw [hp] at hn; cases hn
  · rw [hp] at hn; cases hn
  · rw [hp] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    subst hn
    rw [h.next hp]
    rfl

/-- The erasure of a fragment with stubs: a stub's state stays. -/
def eraseStubs {ι E : Type} {R' R : ι → Code K A L g} {pcOf : E → Nat}
    (er : ∀ i, (R' i).D → (R i).D) : ∀ j, (withStubs R' pcOf j).D → (withStubs R pcOf j).D
  | .inl i => er i
  | .inr _ => id

/-- **Stubs keep erasure.** -/
theorem Erases.withStubs {ι E : Type} {R' R : ι → Code K A L g} {pcOf : E → Nat}
    {er : ∀ i, (R' i).D → (R i).D} (h : ∀ i, Erases (R' i) (R i) (er i)) :
    ∀ j, Erases (Code.withStubs R' pcOf j) (Code.withStubs R pcOf j) (eraseStubs er j)
  | .inl i => h i
  | .inr _ => Erases.rfl' _

/-- **A role thread whose roles erase erases** to the role thread of the control roles. -/
theorem Erases.roleThread {P : Code K A L g} {ι E : Type} {R' R : ι → Code K A L g}
    {pcOf : E → Nat} {enterOf : P.D → Option E} {sel : E → P.D → Option ι} {κ : Type}
    {cls : κ → Event → Bool} {er : ∀ i, (R' i).D → (R i).D}
    (h : ∀ i, Erases (R' i) (R i) (er i)) :
    Erases (Code.roleThread P R' pcOf enterOf sel cls) (Code.roleThread P R pcOf enterOf sel cls)
      (fun d => (eraseSum (eraseStubs er) d.1, d.2)) :=
  (Erases.glue (Erases.withStubs h)).counted cls

end
end PTX.Flow.Code

namespace PTX.Frame
open PTX PTX.Flow

/-- **Before every event a followed value state erases to the control state** on the same prefix
of the thread's trace. -/
theorem stateAt_erase {K : Kernel} {A : List Assumption} {L : Launch}
    {C' C : (g : Nat) → Flow.Code K A L g} {er : ∀ g, (C' g).D → (C g).D}
    (h : ∀ g, Code.Erases (C' g) (C g) (er g)) {X : Execution} {g k : Nat} {s : (C' g).D}
    (hs : stateAt C' X g k = some (some s)) : stateAt C X g k = some (some (er g s)) := by
  unfold stateAt at hs ⊢
  rw [← (h g).init]
  exact (h g).after _ _ hs

end PTX.Frame
