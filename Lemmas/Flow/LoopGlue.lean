-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Glue

@[expose] public section

/-! # A dispatcher whose roles return to it

A proof tool, generic over the kernel: `Code.glue` with returns. A thread runs a dispatching
fragment `P`; from an exit state of `P` it runs the role `R i` the exit selects; from a state of
the role that `back` maps to a state `p` of `P` (the role jumped back to the dispatcher's loop
head) it runs `P` again from `p`, which may select another role. So the dispatcher runs as often
as its roles return (Inkling's workers: the role byte, then the exit byte), and a role that never
returns is a role of `Code.glue` (`back` is `none`); a dispatcher reached at a shared entry by
several warps that each choose their role by a word they read (FlashMLA's warpgroup 1) is the
same construction with no return.

`Code.loopGlue P R exit back`: the states are `P`'s states that are not exits and the roles'
states that do not return; an exit state of `P` is its role's first state (`Code.enter`), a
returning state of a role is the dispatcher's state it returns to, entered in turn (`backEnter`).
Its step obligations (`loopGlue_steps`) follow from `P`'s at its states that are not exits, every
role's at its states that do not return, the hand-off at `P`'s exits (`Code.Handoff`), the hand-off
at the returns (`Back`: a concrete state of a returning state is a concrete state of the state of
`P` it returns to), and that no role's first state returns; with a start of `P` it is sound
(`loopGlue_sound`). The dispatcher's states carry what the rounds need (a round count, the
words of earlier rounds): `back` chooses the state of `P`, so a role passes what it knows. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

namespace Code

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

/-- The state of the loop glue after a role's state: the dispatcher's state it returns to, entered
(a role's first state when that state is an exit), or the role's state. -/
def backEnter (P : Code K A L g) {ι : Type} (R : ι → Code K A L g) (exit : P.D → Option ι)
    (back : (i : ι) → (R i).D → Option P.D) (i : ι) (d : (R i).D) : P.D ⊕ (Σ i, (R i).D) :=
  match back i d with
  | some p => enter P R exit p
  | none => .inr ⟨i, d⟩

/-- **One machine from a dispatcher and roles that may return to it.** -/
@[reducible] def loopGlue (P : Code K A L g) {ι : Type} (R : ι → Code K A L g)
    (exit : P.D → Option ι) (back : (i : ι) → (R i).D → Option P.D) : Code K A L g where
  D := P.D ⊕ (Σ i, (R i).D)
  init := enter P R exit P.init
  pc := fun | .inl d => P.pc d | .inr ⟨i, d⟩ => (R i).pc d
  facts := fun | .inl d => P.facts d | .inr ⟨i, d⟩ => (R i).facts d
  sub := fun | .inl d => P.sub d | .inr ⟨i, d⟩ => (R i).sub d
  acc := fun | .inl d => P.acc d | .inr ⟨i, d⟩ => (R i).acc d
  inv := fun | .inl d => P.inv d ∧ exit d = none | .inr ⟨i, d⟩ => (R i).inv d ∧ back i d = none
  next := fun
    | .inl d, e => (P.next d e).map (Option.map (enter P R exit))
    | .inr ⟨i, d⟩, e => ((R i).next d e).map (Option.map (backEnter P R exit back i))

/-- The hand-off at the returns: a concrete state of a role's state that returns is a concrete
state of the dispatcher's state it returns to. -/
def Back (P : Code K A L g) {ι : Type} (R : ι → Code K A L g)
    (back : (i : ι) → (R i).D → Option P.D) : Prop :=
  ∀ i d p t, back i d = some p → (R i).AtD d t → (R i).inv d → P.AtD p t ∧ P.inv p

variable {back : (i : ι) → (R i).D → Option P.D}

/-- A concrete state of a dispatcher's state is one of its state in the loop glue. -/
theorem good_enter_loop (hglue : Handoff P R exit) (hinit : ∀ i, back i (R i).init = none)
    {d : P.D} {t : TState} (h : P.AtD d t ∧ P.inv d) :
    (loopGlue P R exit back).Good (some (enter P R exit d)) t := by
  cases hx : exit d with
  | none =>
    rw [enter_none hx]
    exact ⟨h.1, h.2, hx⟩
  | some i =>
    rw [enter_some hx]
    obtain ⟨h1, h2⟩ := hglue d i t hx h.1 h.2
    exact ⟨h1, h2, hinit i⟩

/-- A concrete state of a role's state is one of its state in the loop glue. -/
theorem good_backEnter (hglue : Handoff P R exit) (hback : Back P R back)
    (hinit : ∀ i, back i (R i).init = none) {i : ι} {d : (R i).D} {t : TState}
    (h : (R i).AtD d t ∧ (R i).inv d) :
    (loopGlue P R exit back).Good (some (backEnter P R exit back i d)) t := by
  unfold backEnter
  cases hb : back i d with
  | none => exact ⟨h.1, h.2, hb⟩
  | some p => exact good_enter_loop hglue hinit (hback i d p t hb h.1 h.2)

/-- **The step obligations of the loop glue.** -/
theorem loopGlue_steps (hP : ∀ d, exit d = none → P.StepAt d)
    (hR : ∀ i d, back i d = none → (R i).StepAt d) (hglue : Handoff P R exit)
    (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    ∀ d, (loopGlue P R exit back).StepAt d := by
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
          hl, good_enter_loop hglue hinit hg⟩)
      · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hx, fun _ _ hinv => absurd hinv.2 hx⟩
  | inr s =>
    obtain ⟨i, d⟩ := s
    by_cases hb : back i d = none
    · have hs := hR i d hb
      refine ⟨fun hinv => hs.site hinv.1, ?_⟩
      intro t e u ins hat hinv hc hf
      rcases hs.step ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
      · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
      · exact .inl (.inr ⟨backEnter P R exit back i d', t',
          by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl,
          good_backEnter hglue hback hinit hg⟩)
      · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩
    · exact ⟨fun hinv => absurd hinv.2 hb, fun _ _ hinv => absurd hinv.2 hb⟩

/-- **The loop glue is sound.** -/
theorem loopGlue_sound
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ P.AtD P.init t ∧ P.inv P.init)
    (hP : ∀ d, exit d = none → P.StepAt d) (hR : ∀ i d, back i d = none → (R i).StepAt d)
    (hglue : Handoff P R exit) (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    (loopGlue P R exit back).Sound where
  start := by
    obtain ⟨t, hl, ha, hi⟩ := hstart
    exact ⟨t, hl, good_enter_loop hglue hinit ⟨ha, hi⟩⟩
  steps := loopGlue_steps hP hR hglue hback hinit

end Code
end
end PTX.Flow
