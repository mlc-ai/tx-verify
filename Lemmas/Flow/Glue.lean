-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code

@[expose] public section

/-! # A thread's machine glued from fragments

A proof tool, generic over the kernel. A thread runs a first fragment `P` (a prologue) and then,
from an exit state of `P`, one of the fragments `R i` (a role). `Code.glue P R exit` is one site
machine for the whole thread: its states are the states of `P` that are not exits and the states
of the roles; an exit state of `P` is replaced by its role's first state (`Code.enter`). It
obeys the step obligations when `P` does at its states that are not exits, every role does at
every state, and a concrete state of an exit of `P` is a concrete state of its role's first state
(`glue_steps`); with a start of `P` it is sound (`glue_sound`). Layers above then use one frame
(`Frame.stateAt`) for every thread: no offset into the trace and no hand-off lemma per role.
Glue nests, so a role with phases can itself be glued. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

/-- The state of the glued machine for a state of the first fragment: the role's first state at
an exit. -/
def enter (P : Code K A L g) {ι : Type} (R : ι → Code K A L g) (exit : P.D → Option ι)
    (d : P.D) : P.D ⊕ (Σ i, (R i).D) :=
  match exit d with
  | some i => .inr ⟨i, (R i).init⟩
  | none => .inl d

/-- One machine from a first fragment and the roles its exits enter. -/
@[reducible] def glue (P : Code K A L g) {ι : Type} (R : ι → Code K A L g) (exit : P.D → Option ι) :
    Code K A L g where
  D := P.D ⊕ (Σ i, (R i).D)
  init := enter P R exit P.init
  pc := fun | .inl d => P.pc d | .inr ⟨i, d⟩ => (R i).pc d
  facts := fun | .inl d => P.facts d | .inr ⟨i, d⟩ => (R i).facts d
  sub := fun | .inl d => P.sub d | .inr ⟨i, d⟩ => (R i).sub d
  acc := fun | .inl d => P.acc d | .inr ⟨i, d⟩ => (R i).acc d
  inv := fun | .inl d => P.inv d ∧ exit d = none | .inr ⟨i, d⟩ => (R i).inv d
  next := fun
    | .inl d, e => (P.next d e).map (Option.map (enter P R exit))
    | .inr ⟨i, d⟩, e => ((R i).next d e).map (Option.map fun d' => .inr ⟨i, d'⟩)

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem enter_none {d : P.D} (h : exit d = none) : enter P R exit d = .inl d := by
  unfold enter; rw [h]

theorem enter_some {d : P.D} {i : ι} (h : exit d = some i) :
    enter P R exit d = .inr ⟨i, (R i).init⟩ := by
  unfold enter; rw [h]

/-- The hand-off at the exits of the first fragment: a concrete state of an exit state is a
concrete state of its role's first state. -/
def Handoff (P : Code K A L g) {ι : Type} (R : ι → Code K A L g) (exit : P.D → Option ι) :
    Prop :=
  ∀ d i t, exit d = some i → P.AtD d t → P.inv d → (R i).AtD (R i).init t ∧ (R i).inv (R i).init

/-- A concrete state of a state of the first fragment is one of its state in the glued machine,
given the hand-off at the exits. -/
theorem good_enter (hglue : Handoff P R exit) {d : P.D} {t : TState} (h : P.AtD d t ∧ P.inv d) :
    (glue P R exit).Good (some (enter P R exit d)) t := by
  cases hx : exit d with
  | none =>
    rw [enter_none hx]
    exact ⟨h.1, h.2, hx⟩
  | some i =>
    rw [enter_some hx]
    exact hglue d i t hx h.1 h.2

/-- **The step obligations of the glued machine.** -/
theorem glue_steps (hP : ∀ d, exit d = none → P.StepAt d) (hR : ∀ i d, (R i).StepAt d)
    (hglue : Handoff P R exit) : ∀ d, (glue P R exit).StepAt d := by
  intro d
  cases d with
  | inl d =>
    by_cases hx : exit d = none
    · have hs := hP d hx
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show (P.next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl,
          hl, good_enter hglue hg⟩)
      · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩
    · -- an exit state of the first fragment is no state of the glued machine's runs: its
      -- invariant is false
      exact ⟨fun hinv => absurd hinv.2 hx, fun _ _ hinv => absurd hinv.2 hx⟩
  | inr s =>
    obtain ⟨i, d⟩ := s
    have hs := hR i d
    refine ⟨hs.site, ?_⟩
    intro t e u ins hat hinv hc hf
    rcases hs.step ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
    · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
    · exact .inl (.inr ⟨.inr ⟨i, d'⟩, t', by show ((R i).next d e).map _ = _; rw [hn]; rfl,
        hl, hg⟩)
    · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

/-- **The glued machine is sound.** -/
theorem glue_sound
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ P.AtD P.init t ∧ P.inv P.init)
    (hP : ∀ d, exit d = none → P.StepAt d) (hR : ∀ i d, (R i).StepAt d)
    (hglue : Handoff P R exit) : (glue P R exit).Sound where
  start := by
    obtain ⟨t, hl, ha, hi⟩ := hstart
    exact ⟨t, hl, good_enter hglue ⟨ha, hi⟩⟩
  steps := glue_steps hP hR hglue

/-- **An event the glued machine fires from a role's state is one the role fires from it**
(promoted from the tml-fa4 output warp's proof). -/
theorem glue_fired {i : ι} {d : (R i).D} {e : Event} {o : Option TState} :
    (glue P R exit).toMachine.Fired (some (.inr ⟨i, d⟩)) e o ↔
      (R i).toMachine.Fired (some d) e o :=
  Iff.rfl

theorem glue_next_inr (i : ι) (d : (R i).D) (e : Event) :
    (glue P R exit).next (.inr ⟨i, d⟩) e =
      ((R i).next d e).map (Option.map fun d' => .inr ⟨i, d'⟩) :=
  rfl

end Code
end
end PTX.Flow
