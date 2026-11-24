-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Lemmas.Flow.SegFree
public meta import Lean

@[expose] public section

/-! # Assumption lists that select no hook site

A proof tool. The hooks of ASM-INTERFACE are off unless an assumption selects a site. For an
assumption list written out in a proof, `hooks_off` proves that it selects none of a hook's sites
(`NoSegments`, `NoCommitOrder`, or a load wait selector equal to false), each element by `rfl`; the
lemmas that rely on such a fact take it as an automatically proved argument.

A kernel whose assumptions do take segments (`segmentExact`, `pairEvenAt`) has none at the other
positions. The local-step lemmas take `SegFreePc A pc` (`Lemmas.Flow.SegFree`) as an
automatically proved argument: `seg_free_pc` proves it for a literal `pc` element by element
(`seg_free_elem` finds each assumption's constructor and evaluates its site list), `seg_free`
also for `t.pc` given a hypothesis `t.pc = n` or `At t n F`, and both follow from `NoSegments`.
`no_segments` and `seg_sites` prove `NoSegments A` and `SegSites A S` the same way, and
`seg_free_bra` proves `SegFreeBra A K` (no segment at a branch) from `NoSegments`.

A `tcgen05.ld` performs THREAD-TC's load, or, at a site an assumption selects with `tcLdWait`,
the same load continuing at sub-step 1 or the implicit wait at sub-step 1
(`eventTmpl_tcLd_cases`). The load event and its address are the same in both
(`fires_thenWaitLd`); with no site selected only THREAD-TC's load remains
(`eventTmpl_tcLd_noWait`). -/

namespace PTX.Assumption

/-- No assumption of `A` takes a straight-line segment as one step (`segmentRule`). -/
def NoSegments (A : List Assumption) : Prop := ∀ a ∈ A, ∀ L g t, a.segmentRule L g t = none

/-- No assumption of `A` orders commit arrive-ons (`commitInOrder`). -/
def NoCommitOrder (A : List Assumption) : Prop := ∀ a ∈ A, ∀ pc, a.commitInOrder pc = false

theorem noSegments_nil : NoSegments [] := nofun

theorem NoSegments.cons {a : Assumption} {A : List Assumption}
    (ha : ∀ L g t, a.segmentRule L g t = none) (hA : NoSegments A) : NoSegments (a :: A) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact hA b hb

theorem NoSegments.tail {a : Assumption} {A : List Assumption} (h : NoSegments (a :: A)) :
    NoSegments A := fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- Without segments, no segment at any state. -/
theorem NoSegments.segFreeAt {A : List Assumption} (hA : NoSegments A) {L : Launch} {g : Nat}
    {t : TState} : SegFreeAt A L g t :=
  fun a ha => hA a ha L g t

/-- Without segments, no segment at any position. -/
theorem NoSegments.segFreePc {A : List Assumption} (hA : NoSegments A) {pc : Nat} :
    SegFreePc A pc :=
  fun a ha L g t _ => hA a ha L g t

/-- Without segments, no segment off any site list. -/
theorem NoSegments.segSites {A : List Assumption} (hA : NoSegments A) {S : List Nat} :
    SegSites A S :=
  fun a ha L g t _ => hA a ha L g t

/-- Without segments, the local step is the local rule. -/
theorem NoSegments.exec {A : List Assumption} (hA : NoSegments A) {L : Launch}
    {g : Nat} {t : TState} {op : Op} : execLocalA A L g t op = execLocalRule A L g t op :=
  execLocalA_noSegment fun a ha => hA a ha L g t

end PTX.Assumption

/-- Proves that an assumption list written out in the goal selects no site of a hook: each
element by `rfl`. -/
macro "hooks_off" : tactic => `(tactic| first
  | assumption
  | rfl
  | (simp only [PTX.Assumption.NoSegments, PTX.Assumption.NoCommitOrder, List.forall_mem_cons,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
     repeat' constructor
     all_goals (intros; rfl)))

open Lean Meta Elab Tactic in
/-- Proves that one assumption `a` takes no segment: `∀ L g t, t.pc = pc → a.segmentRule L g t =
none` for a literal `pc`, `∀ L g t, t.pc ∉ S → …` for a literal list `S`, or `∀ L g t, …`. The
constructor of `a` is found by unfolding its head constant: a `segmentExact` or `pairEvenAt` by
evaluating its site list, any other assumption by `rfl`. -/
elab "seg_free_elem" : tactic => withMainContext do
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  let a? ← forallTelescope ty fun _ body => do
    let some (_, lhs, _) := (← whnfR body).eq? | return none
    unless lhs.isAppOf ``PTX.Assumption.segmentRule do return none
    return lhs.getAppArgs[0]?
  let some a := a? |
    throwError "seg_free_elem: expected ∀ L g t, t.pc = pc → a.segmentRule … = none"
  let mut e := a
  let mut kind := 0
  for _ in [0:8] do
    if e.isAppOf ``PTX.Assumption.segmentExact then kind := 1; break
    if e.isAppOf ``PTX.Assumption.pairEvenAt then kind := 2; break
    match ← delta? e with
    | some e' => e := e'.headBeta
    | none => break
  match kind with
  | 1 => evalTactic (← `(tactic| first
    | (refine PTX.Assumption.segmentExact_segFreePc ?_; decide)
    | (refine PTX.Assumption.segmentExact_segSites ?_; decide)))
  | 2 => evalTactic (← `(tactic| first
    | (refine PTX.Assumption.pairEvenAt_segFreePc ?_; decide)
    | (refine PTX.Assumption.pairEvenAt_segSites ?_; decide)))
  | _ => evalTactic (← `(tactic| (intros; rfl)))

/-- Proves `NoSegments A` for an assumption list written out in the goal (or a constant that
unfolds to one), element by element (`seg_free_elem`). -/
macro "no_segments" : tactic => `(tactic| first
  | assumption
  | (repeat' (first
      | exact PTX.Assumption.noSegments_nil
      | refine PTX.Assumption.NoSegments.cons ?_ ?_)
     all_goals seg_free_elem))

/-- Proves `SegFreePc A pc` for a literal `pc`: from `NoSegments A`, or element by element
(`seg_free_elem`). -/
macro "seg_free_pc" : tactic => `(tactic| first
  | assumption
  | (refine PTX.Assumption.NoSegments.segFreePc ?_; no_segments)
  | (repeat' (first
      | exact PTX.Assumption.SegFreePc.nil
      | refine PTX.Assumption.SegFreePc.cons ?_ ?_)
     all_goals seg_free_elem))

/-- Proves `SegSites A S` for a literal list `S`, element by element (`seg_free_elem`). -/
macro "seg_sites" : tactic => `(tactic| first
  | assumption
  | (refine PTX.Assumption.NoSegments.segSites ?_; no_segments)
  | (repeat' (first
      | exact PTX.Assumption.SegSites.nil
      | refine PTX.Assumption.SegSites.cons ?_ ?_)
     all_goals seg_free_elem))

/-- Proves `SegFreePc A pc` where `pc` need not be a literal (typically `t.pc`): by
`seg_free_pc`, or by `seg_free_pc` at the position read from a hypothesis `pc = n` or
`At t n F`. -/
macro "seg_free" : tactic => `(tactic| first
  | seg_free_pc
  | (refine PTX.Assumption.SegFreePc.of_eq (by assumption) ?_; seg_free_pc)
  | (refine PTX.Assumption.SegFreePc.of_eq (And.left (by assumption)) ?_; seg_free_pc))

/-- Proves `SegFreeBra A K`: from `NoSegments A`. A kernel with segments uses
`SegFreeBra.of_sites` with `seg_sites` and `decide`. -/
macro "seg_free_bra" : tactic => `(tactic| first
  | assumption
  | (intro _ _ _ _ _; refine PTX.Assumption.NoSegments.segFreePc ?_; no_segments))

namespace PTX.Flow

/-- The three templates of a `tcgen05.ld`. -/
theorem eventTmpl_tcLd_cases {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ds : List Nat} {ta : Nat} {sh : TcShape} :
    eventTmpl A L g t (.tcLd ds ta sh) = tcTmpl L g t (.tcLd ds ta sh) ∨
      eventTmpl A L g t (.tcLd ds ta sh) = (tcTmpl L g t (.tcLd ds ta sh)).thenWaitLd t.pc ∨
      eventTmpl A L g t (.tcLd ds ta sh) = .tc .waitLd { next t with sub := 0 } := by
  simp only [eventTmpl, tcLdTmpl]
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)
  · exact .inl rfl

/-- A property of templates that a load continued at sub-step 1 and the implicit wait keep holds
of a load's template whenever it holds of THREAD-TC's. -/
theorem tcLdTmpl_pres {P : Tmpl → Prop} (hw : ∀ m pc, P m → P (m.thenWaitLd pc))
    (hwait : ∀ t, P (.tc .waitLd t)) {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} (h : P (tcTmpl L g t op)) : P (tcLdTmpl A L g t op) := by
  unfold tcLdTmpl
  split
  · split
    · exact hw _ _ h
    · exact hwait _
  · exact h

/-- A property true of both the implicit wait and ordinary stores is true of the store template. -/
theorem tcStTmpl_pres {P : Tmpl → Prop} (hwait : ∀ t, P (.tc .waitLd t))
    (hub : P (.ub .noRule)) {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (h : ∀ u, P (tcTmpl L g u (.tcSt ta ss sh))) : P (tcStTmpl A L g t ta ss sh) := by
  unfold tcStTmpl
  split
  · split
    · split
      · exact hwait _
      · exact hub
    · exact h _
  · exact h _

/-- Invert a store event to the Core store template, ignoring any preceding load wait. -/
theorem fires_tcSt_core {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ta pc : Nat} {ss : List Opnd} {sh : TcShape} {k : TcKind}
    {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc k) (hw : k ≠ .waitLd) :
    ∃ u, u.regs = t.regs ∧ Fires pc (tcTmpl L g u (.tcSt ta ss sh)) e o := by
  simp only [eventTmpl, tcStTmpl] at hf
  split at hf
  · split at hf
    · split at hf
      · rw [hf.1] at hk
        exact False.elim (hw (Kind.tc.inj hk).symm)
      · rw [hf.1] at hk
        cases hk
    · exact ⟨{ t with sub := 0 }, rfl, hf⟩
  · exact ⟨t, rfl, hf⟩

/-- A property of templates that does not look at a load's continuation is kept by continuing a
load at sub-step 1. -/
theorem thenWaitLd_of {P : Tmpl → Prop}
    (htc : ∀ a n sh k k', P (.tcLd a n sh k) → P (.tcLd a n sh k')) :
    ∀ m pc, P m → P (m.thenWaitLd pc) := by
  intro m pc h
  cases m with
  | tcLd a n sh k => exact htc a n sh k _ h
  | _ => exact h

/-- An event of a load continued at sub-step 1 is an event of the load. -/
theorem fires_thenWaitLd {pc q : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (h : Fires pc (m.thenWaitLd q) e o) : ∃ o', Fires pc m e o' := by
  cases m with
  | tcLd a n k =>
    obtain ⟨vals, hl, he, -⟩ := h
    exact ⟨_, vals, hl, he, rfl⟩
  | _ => exact ⟨o, h⟩

/-- Continuing a template at sub-step 1 keeps it defined. -/
theorem thenWaitLd_ne_ub {q : Nat} {m : Tmpl} {f : Fault} (h : m ≠ .ub f) :
    m.thenWaitLd q ≠ .ub f := by
  cases m <;> simp_all [Tmpl.thenWaitLd]

end PTX.Flow
