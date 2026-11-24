-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run

@[expose] public section

/-! # Site machines: an abstraction of one thread

A proof tool, not part of the model. A site machine abstracts the traces of one
thread. Each abstract state `σ` describes the concrete thread states that are
about to perform `σ`'s event (`Good σ t`), the event template performed there
(`tmpl σ t`) and, for each event that can fire, the abstract successor
(`next σ e`). `Sound` collects the per-state obligations: the template is the one
`out` computes, and after the event fires, local steps reach a concrete state of
the successor.

`Sound.trace` proves once that every trace of the thread is a run of the machine,
and `Trace.fired` names the abstract state each event of a trace fires from: it is
`after init` of the earlier events. Proofs above the thread layer then speak about
abstract states only, never about program counters or registers. -/

namespace PTX.Flow

/-- An abstraction of thread `g` of kernel `K`. -/
structure Machine (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) where
  St : Type
  init : St
  Good : St → TState → Prop
  tmpl : St → TState → Tmpl
  next : St → Event → Option St

namespace Machine

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} (M : Machine K A L g)

/-- Every state that local steps from `u` reach and that performs an event is a concrete
state of `σ`. -/
def Reach (σ : M.St) (u : TState) : Prop :=
  ∀ t, Relation.ReflTransGen (Tau K A L g) u t → Stops K A L g t → M.Good σ t

/-- A thread state whose local steps reach undefined behaviour (a faulted state): its next
event is undefined behaviour. -/
def Dead (u : TState) : Prop :=
  ∃ t f, Relation.ReflTransGen (Tau K A L g) u t ∧ out K A L g t = .ev (.ub f)

/-- Every state that local steps from a dead state reach and that performs an event performs
undefined behaviour. -/
theorem Dead.all {u : TState} (hd : Dead (K := K) (A := A) (L := L) (g := g) u) {t : TState}
    (ht : Relation.ReflTransGen (Tau K A L g) u t) (hs : Stops K A L g t) :
    ∃ f, out K A L g t = .ev (.ub f) := by
  obtain ⟨t', f, ht', hf⟩ := hd
  rw [stop_unique ht ht' hs ⟨_, hf⟩]
  exact ⟨f, hf⟩

/-- A state whose next event is undefined behaviour is dead. -/
theorem dead_of_ub {t : TState} {f : Fault} (h : out K A L g t = .ev (.ub f)) :
    Dead (K := K) (A := A) (L := L) (g := g) t :=
  ⟨t, f, .refl, h⟩

/-- A faulted state is dead. -/
theorem dead_of_fault {u : TState} {f : Fault} (h : u.fault = some f) :
    Dead (K := K) (A := A) (L := L) (g := g) u :=
  dead_of_ub (f := f) (by simp [out, h])

/-- A state whose local step leads to a dead state is dead. -/
theorem dead_of_tau {t t' : TState} (h : out K A L g t = .tau t')
    (hd : Dead (K := K) (A := A) (L := L) (g := g) t') :
    Dead (K := K) (A := A) (L := L) (g := g) t := by
  obtain ⟨s, f, hs, hf⟩ := hd
  exact ⟨s, f, .head h hs, hf⟩

/-- The per-state obligations of a machine. A continuation is either a concrete state of the
successor or dead, in which case the machine stops (`next = none`). -/
structure Sound : Prop where
  start : ∃ t, Relation.ReflTransGen (Tau K A L g) {} t ∧ M.Good M.init t
  out_eq : ∀ {σ t}, M.Good σ t → out K A L g t = .ev (M.tmpl σ t)
  step : ∀ {σ t e u}, M.Good σ t → Fires t.pc (M.tmpl σ t) e (some u) →
    (∃ σ', M.next σ e = some σ' ∧ M.Reach σ' u) ∨
      (M.next σ e = none ∧ Dead (K := K) (A := A) (L := L) (g := g) u)

/-- Event `e` fires from a concrete state of `σ`, continuing in `o`. -/
def Fired (σ : M.St) (e : Event) (o : Option TState) : Prop :=
  ∃ t, M.Good σ t ∧ Fires t.pc (M.tmpl σ t) e o

/-- Runs of the machine. -/
inductive Trace : M.St → List Event → Prop
  | nil (σ : M.St) : Trace σ []
  | step {σ σ' : M.St} {e : Event} {es : List Event} {u : TState} :
      M.Fired σ e (some u) → M.next σ e = some σ' → Trace σ' es → Trace σ (e :: es)
  | last {σ : M.St} {e : Event} : M.Fired σ e none → Trace σ [e]
  /-- An event into a dead state, followed at most by its undefined behaviour. -/
  | dead {σ : M.St} {e : Event} {es : List Event} {u : TState} :
      M.Fired σ e (some u) → M.next σ e = none → es.length ≤ 1 →
      (∀ e' ∈ es, ∃ pc f, e' = ⟨pc, .ub f⟩) → Trace σ (e :: es)

/-- The abstract state after a list of events. -/
def after : M.St → List Event → Option M.St
  | σ, [] => some σ
  | σ, e :: es => (M.next σ e).bind (fun σ' => after σ' es)

@[simp] theorem after_nil (σ : M.St) : M.after σ [] = some σ := rfl

@[simp] theorem after_cons (σ : M.St) (e : Event) (es : List Event) :
    M.after σ (e :: es) = (M.next σ e).bind (fun σ' => M.after σ' es) := rfl

theorem after_append (σ : M.St) (a b : List Event) :
    M.after σ (a ++ b) = (M.after σ a).bind (fun σ' => M.after σ' b) := by
  induction a generalizing σ with
  | nil => rfl
  | cons e a ih =>
    simp only [List.cons_append, after_cons]
    cases M.next σ e with
    | none => rfl
    | some σ' => exact ih σ'

theorem after_snoc (σ : M.St) (es : List Event) (e : Event) :
    M.after σ (es ++ [e]) = (M.after σ es).bind (fun τ => M.next τ e) := by
  rw [after_append]
  cases M.after σ es with
  | none => rfl
  | some τ => simp [after]

/-- Induction along the events of a run: a property of the abstract state and the events
so far that holds initially and is preserved by each machine step holds after every
prefix. -/
theorem after_induction {σ0 : M.St} (Q : M.St → List Event → Prop) (h0 : Q σ0 [])
    (hs : ∀ σ es e σ', Q σ es → M.next σ e = some σ' → Q σ' (es ++ [e])) :
    ∀ (es : List Event) (σ : M.St), M.after σ0 es = some σ → Q σ es := by
  intro es
  induction es using List.reverseRecOn with
  | nil => intro σ h; cases h; exact h0
  | append_singleton es e ih =>
    intro σ' h
    rw [after_snoc] at h
    cases ha : M.after σ0 es with
    | none => rw [ha] at h; cases h
    | some σ =>
      rw [ha] at h
      exact hs σ es e σ' (ih σ ha) h

variable {M}

/-- A concrete state reached by local steps that performs an event is the only one. -/
theorem reach_of (hout : ∀ {σ t}, M.Good σ t → out K A L g t = .ev (M.tmpl σ t)) {σ : M.St}
    {u t : TState} (hl : Relation.ReflTransGen (Tau K A L g) u t) (hg : M.Good σ t) :
    M.Reach σ u := by
  intro t1 hl1 hs1
  have hs : Stops K A L g t := ⟨_, hout hg⟩
  rw [stop_unique hl1 hl hs1 hs]
  exact hg

theorem Sound.reach_of (hM : M.Sound) {σ : M.St} {u t : TState}
    (hl : Relation.ReflTransGen (Tau K A L g) u t) (hg : M.Good σ t) : M.Reach σ u :=
  Machine.reach_of hM.out_eq hl hg

/-- A run from a dead state is at most its undefined behaviour. -/
theorem dead_run {u : TState} (hd : Dead (K := K) (A := A) (L := L) (g := g) u) {es : List Event}
    {o : Option TState} (hr : Run K A L g u es o) :
    es.length ≤ 1 ∧ (∀ e' ∈ es, ∃ pc f, e' = ⟨pc, .ub f⟩) ∧ (o = none ∨ es = []) := by
  cases hr with
  | nil => simp
  | step hl he _ =>
    obtain ⟨f, hf⟩ := hd.all hl (stops_of_estep he)
    obtain ⟨m, hm, hfire⟩ := he
    rw [hf] at hm
    cases hm
    simp [Fires] at hfire
  | last hl he =>
    obtain ⟨f, hf⟩ := hd.all hl (stops_of_estep he)
    obtain ⟨m, hm, hfire⟩ := he
    rw [hf] at hm
    cases hm
    obtain ⟨rfl, -⟩ := hfire
    simp

/-- Every trace from a state whose stopping states belong to `σ` is a run of the machine
from `σ`, by the machine's template and step obligations alone (no start state). -/
theorem trace_from_of (hout : ∀ {σ t}, M.Good σ t → out K A L g t = .ev (M.tmpl σ t))
    (hstep : ∀ {σ t e u}, M.Good σ t → Fires t.pc (M.tmpl σ t) e (some u) →
      (∃ σ', M.next σ e = some σ' ∧ M.Reach σ' u) ∨
        (M.next σ e = none ∧ Dead (K := K) (A := A) (L := L) (g := g) u))
    {es : List Event} {σ : M.St} {t : TState}
    {o : Option TState} (hreach : M.Reach σ t) (hr : Run K A L g t es o) : M.Trace σ es := by
  induction hr generalizing σ with
  | nil t => exact .nil σ
  | step hl he hrest ih =>
    have hg := hreach _ hl (stops_of_estep he)
    obtain ⟨m, hm, hf⟩ := he
    rw [hout hg] at hm
    cases hm
    rcases hstep hg hf with ⟨σ', hnext, hreach'⟩ | ⟨hnext, hdead⟩
    · exact .step ⟨_, hg, hf⟩ hnext (ih hreach')
    · obtain ⟨hlen, hub, -⟩ := dead_run hdead hrest
      exact .dead ⟨_, hg, hf⟩ hnext hlen hub
  | last hl he =>
    have hg := hreach _ hl (stops_of_estep he)
    obtain ⟨m, hm, hf⟩ := he
    rw [hout hg] at hm
    cases hm
    exact .last ⟨_, hg, hf⟩

/-- Every trace from a state whose stopping states belong to `σ` is a run of the machine
from `σ`. -/
theorem Sound.trace_from (hM : M.Sound) {es : List Event} {σ : M.St} {t : TState}
    {o : Option TState} (hreach : M.Reach σ t) (hr : Run K A L g t es o) : M.Trace σ es :=
  trace_from_of hM.out_eq hM.step hreach hr

/-- Every trace of the thread is a run of the machine from `init`. -/
theorem Sound.trace (hM : M.Sound) {es : List Event} {o : Option TState}
    (hr : Run K A L g {} es o) : M.Trace M.init es := by
  obtain ⟨t, hl, hg⟩ := hM.start
  exact hM.trace_from (hM.reach_of hl hg) hr

theorem Sound.produces (hM : M.Sound) {es : List Event} (hp : Produces K A L g es) :
    M.Trace M.init es := by
  obtain ⟨o, hr⟩ := hp
  exact hM.trace hr

/-- A run that has not ended stops in the abstract state reached by its events, or the
machine stopped at a dead state: every state from which the thread performs its next event
belongs to it. -/
theorem Sound.run_end (hM : M.Sound) {es : List Event} {σ : M.St} {t u : TState}
    (hreach : M.Reach σ t) (hr : Run K A L g t es (some u)) :
    (∃ τ, M.after σ es = some τ ∧ M.Reach τ u) ∨ M.after σ es = none := by
  generalize ho : some u = o at hr
  induction hr generalizing σ with
  | nil t =>
    cases ho
    exact .inl ⟨σ, rfl, hreach⟩
  | step hl he hrest ih =>
    have hg := hreach _ hl (stops_of_estep he)
    obtain ⟨m, hm, hf⟩ := he
    rw [hM.out_eq hg] at hm
    cases hm
    rcases hM.step hg hf with ⟨σ', hnext, hreach'⟩ | ⟨hnext, -⟩
    · rcases ih hreach' ho with ⟨τ, ha, hτ⟩ | ha
      · exact .inl ⟨τ, by simp only [after_cons, hnext, Option.bind_some, ha], hτ⟩
      · exact .inr (by simp only [after_cons, hnext, Option.bind_some, ha])
    · exact .inr (by simp only [after_cons, hnext, Option.bind_none])
  | last => cases ho

/-- The final state of a run from the initial thread state that has not ended. -/
theorem Sound.final (hM : M.Sound) {es : List Event} {u : TState}
    (hr : Run K A L g {} es (some u)) :
    (∃ τ, M.after M.init es = some τ ∧ M.Reach τ u) ∨ M.after M.init es = none := by
  obtain ⟨t, hl, hg⟩ := hM.start
  exact hM.run_end (hM.reach_of hl hg) hr

/-- A run that has not ended, along which the machine stopped, ends in a dead state. -/
theorem Sound.dead_end (hM : M.Sound) {es : List Event} {σ : M.St} {t u : TState}
    (hreach : M.Reach σ t) (hr : Run K A L g t es (some u)) (ha : M.after σ es = none) :
    Dead (K := K) (A := A) (L := L) (g := g) u := by
  generalize ho : some u = o at hr
  induction hr generalizing σ with
  | nil t => cases ha
  | step hl he hrest ih =>
    have hg := hreach _ hl (stops_of_estep he)
    obtain ⟨m, hm, hf⟩ := he
    rw [hM.out_eq hg] at hm
    cases hm
    rcases hM.step hg hf with ⟨σ', hnext, hreach'⟩ | ⟨-, hdead⟩
    · exact ih hreach' (by simpa only [after_cons, hnext, Option.bind_some] using ha) ho
    · obtain ⟨-, -, hnil⟩ := dead_run hdead hrest
      rcases hnil with rfl | rfl
      · cases ho
      · cases hrest
        cases ho
        exact hdead
  | last => cases ho

/-- A run from the initial thread state that has not ended, along which the machine stopped,
ends in a dead state. -/
theorem Sound.final_dead (hM : M.Sound) {es : List Event} {u : TState}
    (hr : Run K A L g {} es (some u)) (ha : M.after M.init es = none) :
    Dead (K := K) (A := A) (L := L) (g := g) u := by
  obtain ⟨t, hl, hg⟩ := hM.start
  exact hM.dead_end (hM.reach_of hl hg) hr ha

/-- Each event of a run fires from the abstract state reached by the earlier events, except
the undefined behaviour after a dead state, where the machine has stopped. -/
theorem Trace.fired {σ : M.St} {es : List Event} (h : M.Trace σ es) :
    ∀ {j : Nat} {e : Event}, es[j]? = some e →
      (∃ τ o, M.after σ (es.take j) = some τ ∧ M.Fired τ e o) ∨
        (M.after σ (es.take j) = none ∧ ∃ pc f, e = ⟨pc, .ub f⟩) := by
  induction h with
  | nil σ => intro j e hj; simp at hj
  | step hf hn _ ih =>
    intro j e hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact .inl ⟨_, _, rfl, hf⟩
    | succ j =>
      simp only [List.take_succ_cons, after_cons, hn, Option.bind_some]
      exact ih (by simpa using hj)
  | last hf =>
    intro j e hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact .inl ⟨_, _, rfl, hf⟩
    | succ j => simp at hj
  | dead hf hn _ hub =>
    intro j e hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact .inl ⟨_, _, rfl, hf⟩
    | succ j =>
      exact .inr ⟨by simp only [List.take_succ_cons, after_cons, hn, Option.bind_none],
        hub e (List.mem_of_getElem? (by simpa using hj))⟩

/-- The event at a position where the machine still follows the thread fired from the state
reached there. -/
theorem Trace.fired_at {σ : M.St} {es : List Event} (h : M.Trace σ es) {j : Nat} {e : Event}
    {τ : M.St} (hj : es[j]? = some e) (hτ : M.after σ (es.take j) = some τ) :
    ∃ o, M.Fired τ e o := by
  rcases h.fired hj with ⟨τ', o, ha, hf⟩ | ⟨ha, -⟩
  · rw [hτ] at ha
    cases ha
    exact ⟨o, hf⟩
  · rw [hτ] at ha
    cases ha

end Machine
end PTX.Flow
