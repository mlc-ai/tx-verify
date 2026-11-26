-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Roles
public import Lemmas.Flow.CodeU

@[expose] public section

/-! # The strict glue: a thread machine whose roles stop at their first event

A thread machine with UB-tolerant roles (`Code.SoundU`) follows a thread through a final undefined
behaviour at any state, so an event at a state of its first fragment (the startup) may a priori be
undefined behaviour away from the fragment's sites. The first fragment itself is strict
(`Code.StepAt`): the **strict glue** `strictThread` is the thread machine whose roles (and stubs)
stop at their first event. It is `Code.Sound` from the first fragment's strict steps, the roles'
site obligations (`StepAtU.site`) and the hand-off (`strictThread_sound`); its states after a
prefix of events agree with the thread machine's on the first fragment's states
(`strict_recover`), so every event at such a state is its site's event (the pattern of the tml-fa4
proof's `Common/SharedSites.lean`, generic over the kernel). -/

namespace PTX.Flow.Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A family of codes whose members stop at their first event. -/
@[reducible] def firstOnly {ι : Type} (W : ι → Code K A L g) (j : ι) : Code K A L g :=
  { W j with next := fun _ _ => some none }

/-- **The strict glue**: the thread machine `roleThread` whose roles and stubs stop at their first
event. -/
@[reducible] def strictThread (P : Code K A L g) {ι E : Type} (R : ι → Code K A L g)
    (pcOf : E → Nat) (enterOf : P.D → Option E) (sel : E → P.D → Option ι) {κ : Type}
    (cls : κ → Event → Bool) : Code K A L g :=
  (glue P (firstOnly (withStubs R pcOf)) (gatedExit enterOf sel)).counted cls

variable {P : Code K A L g} {ι E : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
  {enterOf : P.D → Option E} {sel : E → P.D → Option ι} {κ : Type} {cls : κ → Event → Bool}

/-- **The strict glue is sound**, from the first fragment's strict steps, the roles' (UB-tolerant)
step obligations and the hand-off. -/
theorem strictThread_sound
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ P.AtD P.init t ∧ P.inv P.init)
    (hP : ∀ d, gatedExit enterOf sel d = none → P.StepAt d)
    (hW : ∀ j d, (withStubs R pcOf j).StepAtU d)
    (hglue : Handoff P (withStubs R pcOf) (gatedExit enterOf sel)) :
    (strictThread P R pcOf enterOf sel cls).Sound :=
  counted_sound (glue_sound hstart hP
    (fun j d => ⟨(hW j d).site, fun _ _ _ _ _ => .inl (.inl rfl)⟩) hglue)

/-- The states of the first fragment among the abstract states after some events. -/
def firstPart {D N : Type} (s : Option (Option ((D ⊕ N) × (κ → Nat)))) :
    Option ((D ⊕ N) × (κ → Nat)) :=
  s.join.filter fun σ => σ.1.isLeft

/-- One step: the strict glue and the thread machine advance the first fragment's states alike. -/
theorem advance (e : Event) (s : Option (Option (roleThread P R pcOf enterOf sel cls).D))
    (cut : Bool) :
    firstPart (s.bind fun d =>
      if cut then (strictThread P R pcOf enterOf sel cls).toMachine.next d e
      else (roleThread P R pcOf enterOf sel cls).toMachine.next d e) =
      (firstPart s).bind
        (fun d => firstPart ((roleThread P R pcOf enterOf sel cls).toMachine.next (some d) e)) := by
  rcases s with _ | _ | ⟨s | ⟨j, d⟩, n⟩
  · cases cut <;> rfl
  · cases cut <;> rfl
  · cases cut <;> rfl
  · cases cut
    · change firstPart ((((withStubs R pcOf j).next d e).map (Option.map fun d' =>
        (Sum.inr ⟨j, d'⟩ : (glue P (withStubs R pcOf) (gatedExit enterOf sel)).D))).map
          (Option.map fun d' => (d', bump cls n e))) = none
      rcases (withStubs R pcOf j).next d e with _ | _ | d' <;> rfl
    · rfl

/-- **The strict glue agrees with the thread machine on the first fragment's states.** -/
theorem strict_agree (es : List Event) :
    firstPart ((roleThread P R pcOf enterOf sel cls).toMachine.after
        (some (roleThread P R pcOf enterOf sel cls).init) es) =
      firstPart ((strictThread P R pcOf enterOf sel cls).toMachine.after
        (some (strictThread P R pcOf enterOf sel cls).init) es) := by
  change firstPart ((roleThread P R pcOf enterOf sel cls).toMachine.after
    (roleThread P R pcOf enterOf sel cls).toMachine.init es) =
      firstPart ((strictThread P R pcOf enterOf sel cls).toMachine.after
        (strictThread P R pcOf enterOf sel cls).toMachine.init es)
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    rw [Machine.after_snoc, Machine.after_snoc]
    exact (advance e _ false).trans ((congrArg (·.bind fun d =>
      firstPart ((roleThread P R pcOf enterOf sel cls).toMachine.next (some d) e)) ih).trans
        (advance e _ true).symm)

/-- **A state of the first fragment of the thread machine is one of the strict glue.** -/
theorem strict_recover {es : List Event} {d : P.D} {n : κ → Nat}
    (h : (roleThread P R pcOf enterOf sel cls).toMachine.after
      (some (roleThread P R pcOf enterOf sel cls).init) es = some (some (.inl d, n))) :
    (strictThread P R pcOf enterOf sel cls).toMachine.after
      (some (strictThread P R pcOf enterOf sel cls).init) es = some (some (.inl d, n)) := by
  have ha := strict_agree (P := P) (R := R) (pcOf := pcOf) (enterOf := enterOf) (sel := sel)
    (cls := cls) es
  rw [h] at ha
  rcases hd : (strictThread P R pcOf enterOf sel cls).toMachine.after
    (some (strictThread P R pcOf enterOf sel cls).init) es with _ | _ | ⟨s | s, n'⟩ <;>
    rw [hd] at ha <;> cases ha
  rfl

end Code
end PTX.Flow
