-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Polls
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.NotObject

@[expose] public section

/-! # Invariants along a code's run

A proof tool. An invariant of a thread's abstract states and its event prefix holds after
every prefix of the run when it holds at the start and every step fired at a state's site
keeps it (`Code.run_inv`); the steps into a dead state need nothing. An event of an
instruction that uses no mbarrier object changes none of the object counts (`quiet`). -/

namespace PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An invariant of the abstract states holds after every prefix of a run when every step
fired at a state's site keeps it. -/
theorem Code.run_inv {C : Code K A L g} (hC : C.Sound) {es : List Event}
    (htr : C.toMachine.Trace (some C.init) es) (J : C.D → List Event → Prop)
    (h0 : J C.init [])
    (hs : ∀ {d d' : C.D} {pre : List Event} {e : Event} {t : TState} {ins : Instr}
      {o : Option TState}, J d pre → C.AtD d t → C.inv d → K.code[C.pc d]? = some ins →
      Fires (C.pc d) (eventTmpl A L g t ins.op) e o → C.next d e = some (some d') →
      J d' (pre ++ [e])) :
    ∀ j d, C.toMachine.after (some C.init) (es.take j) = some (some d) → J d (es.take j) := by
  have h := Machine.Trace.prefix_induction htr (fun σ es => ∀ d, σ = some d → J d es)
    (fun d hd => by cases hd; exact h0) ?_
  · exact fun j d hd => h j _ hd d rfl
  intro σ pre e σ' o hq hf hn d' hd'
  subst hd'
  cases σ with
  | none => cases hn
  | some d =>
    obtain ⟨t, ins, hat, hinv, hc, hfire⟩ := Code.fired_site hC hf
    exact hs (hq d rfl) hat hinv hc hfire hn

/-- Whether event `e` is a cancellation request completing on its own CTA's barrier `m`. -/
def clcIssuesTo (m : Loc) (e : Event) : Bool := match e.kind with
  | .clcIssue sp _ => decide (sp.mbar = m)
  | _ => false

theorem clcIssues_snoc (m : Loc) (es : List Event) (e : Event) :
    (es ++ [e]).countP (clcIssuesTo m) =
      es.countP (clcIssuesTo m) + if clcIssuesTo m e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

/-- An event that uses no mbarrier object is no poll, arrival, commit, copy or cancellation
request on any object. -/
theorem quiet_of_kind {e : Event} (h : ¬ ObjectKind e.kind) (m : Loc) :
    okPoll m e = false ∧ arrivesOn m e = false ∧ commitsTo m e = false ∧
      issuesTo m e = false ∧ clcIssuesTo m e = false := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [ObjectKind, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive,
    commitsTo, issuesTo, clcIssuesTo]
  rename_i tk
  cases tk <;> simp_all

/-- An event of an instruction that uses no mbarrier object is no poll, arrival, commit, copy
or cancellation request on any object. -/
theorem quiet {t : TState} {op : Op} {pc : Nat} {e : Event} {o : Option TState}
    (hop : objectOp op = false) (hf : Fires pc (eventTmpl A L g t op) e o) (m : Loc) :
    okPoll m e = false ∧ arrivesOn m e = false ∧ commitsTo m e = false ∧
      issuesTo m e = false ∧ clcIssuesTo m e = false :=
  quiet_of_kind (notObject_of_op hop hf) m

/-- A successful poll is a successful wait on its object. -/
theorem okPoll_wait_form {m : Loc} {e : Event} (h : okPoll m e = true) :
    ∃ p acq sc, e.kind = .wait m p true acq sc := by
  obtain ⟨pc, kind⟩ := e
  cases kind
  case wait target p ok acq sc =>
    cases ok
    · simp [okPoll, sourceWaitSuccess] at h
    · simp only [okPoll, sourceWaitSuccess, decide_eq_true_eq] at h
      subst h
      exact ⟨p, acq, sc, rfl⟩
  all_goals simp [okPoll, sourceWaitSuccess] at h

/-- An arrival on an object is an arrival event on it. -/
theorem arrivesOn_form {m : Loc} {e : Event} (h : arrivesOn m e = true) :
    ∃ tx c rel sc, e.kind = .arrive m tx c rel sc := by
  obtain ⟨pc, kind⟩ := e
  cases kind
  case arrive target tx c rel sc =>
    simp only [arrivesOn, sourceArrive, decide_eq_true_eq] at h
    subst h
    exact ⟨tx, c, rel, sc, rfl⟩
  all_goals simp [arrivesOn, sourceArrive] at h

end
end PTX.Flow
