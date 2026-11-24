-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Glue
public import Lemmas.Flow.LoopGlue
public import Lemmas.Flow.Counted
public import Lemmas.Kernel.CodeCheck

@[expose] public section

/-! # The roles of a kernel and its thread machine, as declarations

A proof tool, generic over the kernel (the kernel-independent part of the tml-fa4 thread
machine, `Proof2/Common/Roles.lean` and `Proof2/Common/Sound.lean`). Every thread runs a first
fragment `P` (the startup) and then the role its exit selects. A kernel declares:

* **Roles as data**: per fragment a region of the code (half-open intervals) and the pcs where
  control may leave it (`RoleDecl`); `RoleDecl.closed` and `RoleDecl.sites` are the `Bool` checks
  of `Lemmas/Kernel/CodeCheck.lean` on the decoded program (closed up to the exits; the event
  instructions, to compare with the machine's site table).
* **Entries and gates**: `enterOf d` is the entry `r : E` an exit state `d` of `P` passes to (an
  entry is where the compiled dispatch jumps; `pcOf r` is its first pc), and `sel r d` the
  migrated role `i : ι` that state enters, or `none`. A kernel lets `sel` test the words the
  role's first state relies on (the gate); when the gate fails, or the entry has no migrated role
  yet, the thread enters the entry's stub, a fragment that stops at its first event
  (`Code.stop`). No followed thread reaches a stub of a migrated role, because the gate holds on
  every thread by the first fragment's reference invariant.
* **The thread machine**: `Code.roleThread P R pcOf enterOf sel cls` is the glue of `P` and
  `withStubs R pcOf` along `gatedExit enterOf sel`, with the ghost ledger of the classes `cls`.

It is sound (`roleThread_sound`) from: the start of `P`, the steps of `P` at its states that are
not exits, the steps of every role, that every entry's first instruction is an unguarded event
instruction (`StubSite`, decidable), that an exit state sits at its entry's first pc
(`hstub`), and one hand-off per migrated role (`hrole`): a concrete state of an exit state whose
gate holds is a concrete state of the role's first state. A new role adds a constructor to `ι`,
its fragment to `R`, its case to `sel` and its hand-off; nothing else changes.

A role that dispatches again (warps of one warpgroup sharing an entry and choosing their role
by a word a collective returns), or a dispatch loop whose roles return to it and which runs again
(workers that read a role byte, run the role, and read the exit byte), is a `roleLoop`
(`roleLoop_steps`, over `Code.loopGlue`): its dispatching fragment follows the code's dispatch
(no stop on the word), its exit selects the sub-role, and a sub-role's jump back to the loop head
returns to it. -/

namespace PTX.Flow

noncomputable section

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A fragment's region of the code (half-open intervals) and the pcs where control may leave
it. -/
structure RoleDecl where
  region : List (Nat × Nat)
  exits : List Nat

/-- The region is closed up to its exits: every instruction of it other than an exit continues
inside it. -/
def RoleDecl.closed (K : Kernel) (d : RoleDecl) : Bool :=
  CodeCheck.closedFrom d.region d.exits 0 K.code

/-- The region's event instructions: the sites of its machine and the exits that are events. -/
def RoleDecl.sites (K : Kernel) (d : RoleDecl) : List Nat :=
  CodeCheck.sitesFrom d.region 0 K.code

/-- The first instruction of an entry is an unguarded event instruction: a stub there fires its
event and stops. -/
def StubSite (K : Kernel) (pc : Nat) : Bool :=
  match K.code[pc]? with
  | some ins => !ins.op.isLocal && ins.guard.isNone
  | none => false

namespace Code

/-- A fragment that stops at its first event, at `pc`: an entry with no migrated role, or whose
gate fails. -/
@[reducible] def stop (K : Kernel) (A : List Assumption) (L : Launch) (g pc : Nat) :
    Code K A L g where
  D := Unit
  init := ()
  pc := fun _ => pc
  facts := fun _ => []
  inv := fun _ => True
  next := fun _ _ => some none

/-- **A stub obeys its step obligations** when its pc is an unguarded event instruction. -/
theorem stop_steps {pc : Nat} (h : StubSite K pc = true) (d : Unit) :
    (stop K A L g pc).StepAt d where
  site := fun _ => by
    unfold StubSite at h
    split at h
    · rename_i ins hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        Option.isNone_iff_eq_none] at h
      refine ⟨ins, hc, h.1, ?_⟩
      rw [h.2]
      trivial
    · exact absurd h Bool.false_ne_true
  step := fun _ _ _ _ _ => .inl (.inl rfl)

/-- The roles of a glue with stubs: a migrated role `i` is its fragment, an entry `r` is the stub
at its first pc. -/
@[reducible] def withStubs {ι E : Type} (R : ι → Code K A L g) (pcOf : E → Nat) :
    ι ⊕ E → Code K A L g
  | .inl i => R i
  | .inr r => stop K A L g (pcOf r)

/-- The exits of the first fragment with gates: an exit state with entry `r` enters the migrated
role `sel r d` when there is one, else the stub of `r`. -/
def gatedExit {P : Code K A L g} {ι E : Type} (enterOf : P.D → Option E)
    (sel : E → P.D → Option ι) (d : P.D) : Option (ι ⊕ E) :=
  (enterOf d).map fun r => match sel r d with
    | some i => .inl i
    | none => .inr r

/-- **The thread machine of a kernel with roles**: the first fragment, then the role its exit
selects (or a stub), with the ghost ledger of the classes `cls`. -/
@[reducible] def roleThread (P : Code K A L g) {ι E : Type} (R : ι → Code K A L g)
    (pcOf : E → Nat) (enterOf : P.D → Option E) (sel : E → P.D → Option ι) {κ : Type}
    (cls : κ → Event → Bool) : Code K A L g :=
  (glue P (withStubs R pcOf) (gatedExit enterOf sel)).counted cls

variable {P : Code K A L g} {ι E : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
  {enterOf : P.D → Option E} {sel : E → P.D → Option ι}

theorem gatedExit_none {d : P.D} : gatedExit enterOf sel d = none ↔ enterOf d = none := by
  simp [gatedExit]

/-- **The hand-offs of a glue with stubs and gates**, from one hand-off per migrated role. -/
theorem handoff_gated
    (hstub : ∀ d r, enterOf d = some r → P.inv d → P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [])
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init) :
    Handoff P (withStubs R pcOf) (gatedExit enterOf sel) := by
  intro d j t hx hat hinv
  cases he : enterOf d with
  | none => simp [gatedExit, he] at hx
  | some r =>
    simp only [gatedExit, he, Option.map_some, Option.some.injEq] at hx
    cases hs : sel r d with
    | some i =>
      rw [hs] at hx
      subst hx
      exact hrole d r i t he hs hat hinv
    | none =>
      rw [hs] at hx
      subst hx
      obtain ⟨hpc, hsub, hacc⟩ := hstub d r he hinv
      obtain ⟨h1, h2, h3, h4, -⟩ := hat
      exact ⟨⟨h1.trans hpc, h2.trans hsub, h3.trans hacc, h4, trivial⟩, trivial⟩

/-- **The thread machine of a kernel with roles is sound.** -/
theorem roleThread_sound {κ : Type} (cls : κ → Event → Bool)
    (hstart : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ P.AtD P.init t ∧ P.inv P.init)
    (hP : ∀ d, enterOf d = none → P.StepAt d) (hR : ∀ i d, (R i).StepAt d)
    (hpcs : ∀ r, StubSite K (pcOf r) = true)
    (hstub : ∀ d r, enterOf d = some r → P.inv d → P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [])
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init) :
    (roleThread P R pcOf enterOf sel cls).Sound :=
  counted_sound (glue_sound hstart (fun d hx => hP d (gatedExit_none.mp hx))
    (fun j d => match j with
      | .inl i => hR i d
      | .inr r => stop_steps (hpcs r) d)
    (handoff_gated hstub hrole))

/-- A stub stops at its first event: a thread at a stub state is no longer followed after it. -/
theorem roleThread_stub {κ : Type} {cls : κ → Event → Bool} (r : E) (u : Unit) (n : κ → Nat)
    (e : Event) :
    (roleThread P R pcOf enterOf sel cls).next (.inr ⟨.inr r, u⟩, n) e = some none :=
  rfl


/-! ### A second dispatch level -/

/-- A stub whose invariant says its pc is an unguarded event instruction (`StubSite`): its step
obligations hold at any pc (`stopAt_steps`), so the entries of a dispatch may be any pcs (a
function of the launch, say); the hand-off into it carries the check. -/
@[reducible] def stopAt (K : Kernel) (A : List Assumption) (L : Launch) (g pc : Nat) :
    Code K A L g where
  D := Unit
  init := ()
  pc := fun _ => pc
  facts := fun _ => []
  inv := fun _ => StubSite K pc = true
  next := fun _ _ => some none

theorem stopAt_steps {pc : Nat} (d : Unit) : (stopAt K A L g pc).StepAt d where
  site := fun h => (stop_steps (A := A) (L := L) (g := g) h d).site trivial
  step := fun _ _ _ _ _ => .inl (.inl rfl)

/-- The roles of a dispatch with stubs at their entries' pcs. -/
@[reducible] def withStubsAt {ι E : Type} (R : ι → Code K A L g) (pcOf : E → Nat) :
    ι ⊕ E → Code K A L g
  | .inl i => R i
  | .inr r => stopAt K A L g (pcOf r)

/-- **A dispatch level without a ledger, whose roles may return to it**: a fragment `P` (a role's
shared entry, or a dispatch loop: its setup and the code's dispatch, following every value it
reads), then the sub-role its exit selects, or the stub of the exit's entry; a sub-role state that
`back` maps to a state of `P` (the code jumped back to the dispatch loop's head) runs `P` again from
there (`Code.loopGlue`). It is a role of `roleThread` (whose ledger counts every event):

* a role that dispatches once more by a word a collective returned (FlashMLA's warpgroup 1 at its
  shared entry) is `roleLoop` with `back` everywhere `none`;
* a dispatch loop whose roles return and which runs again (Inkling's workers: the role byte, then
  the exit byte) is `roleLoop` with `back` at the roles' jumps to the loop head; `P`'s states carry
  the round, so its exit selects the next round's role.

An entry's pc may depend on the launch (the stubs are `Code.stopAt`). -/
@[reducible] def roleLoop (P : Code K A L g) {ι E : Type} (R : ι → Code K A L g)
    (pcOf : E → Nat) (enterOf : P.D → Option E) (sel : E → P.D → Option ι)
    (back : (i : ι) → (R i).D → Option P.D) : Code K A L g :=
  loopGlue P (withStubsAt R pcOf) (gatedExit enterOf sel) fun
    | .inl i => back i
    | .inr _ => fun _ => none

/-- **Every state of a dispatch level obeys its step obligations**, from the steps of its first
fragment at its states that are not exits, those of its sub-roles at their states that do not
return, that an exit state sits at an unguarded event instruction, its entry's pc (`hstub`), one
hand-off per sub-role (`hrole`), the hand-off at the returns (`hback`: a concrete state of a
returning state is one of the state of `P` it returns to) and that no sub-role's first state
returns (`hinit`). The hand-off into the level itself is the outer role's (`roleThread_sound`'s
`hrole`, with the level's first state that of `P`). -/
theorem roleLoop_steps {P : Code K A L g} {ι E : Type} {R : ι → Code K A L g} {pcOf : E → Nat}
    {enterOf : P.D → Option E} {sel : E → P.D → Option ι} {back : (i : ι) → (R i).D → Option P.D}
    (hP : ∀ d, enterOf d = none → P.StepAt d) (hR : ∀ i d, back i d = none → (R i).StepAt d)
    (hstub : ∀ d r, enterOf d = some r → P.inv d →
      P.pc d = pcOf r ∧ P.sub d = 0 ∧ P.acc d = [] ∧ StubSite K (pcOf r) = true)
    (hrole : ∀ d r i t, enterOf d = some r → sel r d = some i → P.AtD d t → P.inv d →
      (R i).AtD (R i).init t ∧ (R i).inv (R i).init)
    (hback : ∀ i d p t, back i d = some p → (R i).AtD d t → (R i).inv d → P.AtD p t ∧ P.inv p)
    (hinit : ∀ i, back i (R i).init = none) :
    ∀ d, (roleLoop P R pcOf enterOf sel back).StepAt d := by
  refine loopGlue_steps (fun d hx => hP d (gatedExit_none.mp hx))
    (fun j => match j with
      | .inl i => fun d hb => hR i d hb
      | .inr _ => fun d _ => stopAt_steps d) ?_ ?_ ?_
  · intro d j t hx hat hinv
    cases he : enterOf d with
    | none => simp [gatedExit, he] at hx
    | some r =>
      simp only [gatedExit, he, Option.map_some, Option.some.injEq] at hx
      cases hs : sel r d with
      | some i =>
        rw [hs] at hx
        subst hx
        exact hrole d r i t he hs hat hinv
      | none =>
        rw [hs] at hx
        subst hx
        obtain ⟨hpc, hsub, hacc, hsite⟩ := hstub d r he hinv
        obtain ⟨h1, h2, h3, h4, -⟩ := hat
        exact ⟨⟨h1.trans hpc, h2.trans hsub, h3.trans hacc, h4, trivial⟩, hsite⟩
  · rintro (i | r) d p t hb hat hinv
    · exact hback i d p t hb hat hinv
    · cases hb
  · rintro (i | r)
    · exact hinit i
    · rfl

end Code

end

end PTX.Flow
