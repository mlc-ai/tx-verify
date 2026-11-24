-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Run
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX

/-- Invert a nonempty thread trace from a determined, continuing event template. -/
theorem Next.continuing_event {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {a b : TState} {e : Event} {es : List Event}
    {o : Option TState} {m : Tmpl} (hn : Next K A l g a b m)
    (hContinue : ¬ Fires b.pc m e none) (hr : Run K A l g a (e :: es) o) :
    ∃ u, Fires b.pc m e (some u) ∧ Run K A l g u es o := by
  have hs : Stops K A l g b := ⟨_, hn.stop⟩
  cases hr with
  | step hlocal he hrest =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst b
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    exact ⟨_, hfire, hrest⟩
  | last hlocal he =>
    have heq := stop_unique hlocal hn.steps (stops_of_estep he) hs
    subst b
    obtain ⟨templ, htempl, hfire⟩ := he
    rw [hn.stop] at htempl
    obtain rfl := Out.ev.inj htempl
    exact (hContinue hfire).elim

/-- Advance a nonempty trace along an audited event-free local prefix, including
traces whose lane will suspend at their last event. -/
theorem Run.after_local_nonempty {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {t u : TState} {es : List Event} {o : Option TState}
    (hr : Run K A l g t es o)
    (ht : Relation.ReflTransGen (Tau K A l g) t u) (hne : es ≠ []) : Run K A l g u es o := by
  have advance {s : TState} {e : Event} {o : Option TState}
      (hs : Relation.ReflTransGen (Tau K A l g) t s) (he : EStep K A l g s e o) :
      Relation.ReflTransGen (Tau K A l g) u s := by
    rcases rtg_tau_total ht hs with h | h
    · exact h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_, hTau, _⟩
      · exact .refl
      · exact (not_tau_of_stops (stops_of_estep he) hTau).elim
  cases hr with
  | nil => exact (hne rfl).elim
  | step hs he hr => exact .step (advance hs he) he hr
  | last hs he => exact .last (advance hs he) he

/-- Advance the cursor of a terminated trace along a verified event-free local prefix. -/
theorem Run.after_local {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {t u : TState} {es : List Event} (hr : Run K A l g t es none)
    (ht : Relation.ReflTransGen (Tau K A l g) t u) : Run K A l g u es none :=
  hr.after_local_nonempty ht (fun h => by rw [h] at hr; cases hr)

/-- The event at a nonterminal index has a returning step and an actual suffix. -/
theorem Run.after_event {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {o : Option TState} (hr : Run K A l g s es o)
    {i : Nat} {e : Event} (he : es[i]? = some e) (hi : i+1 < es.length) :
    ∃ t u, EStep K A l g t e (some u) ∧ Run K A l g u (es.drop (i+1)) o := by
  induction hr generalizing i with
  | nil => simp at hi
  | last => simp at hi
  | step _ he' hr ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      exact ⟨_, _, he', hr⟩
    | succ i =>
      exact ih (by simpa using he) (by simpa using hi)

/-- The state about to perform an indexed event is reached by exactly its earlier events. -/
theorem Run.before_event {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {es : List Event} {o : Option TState} (hr : Run K A l g s es o)
    {i : Nat} {e : Event} (he : es[i]? = some e) :
    ∃ t q, Flow.TraceReach K A l g s (es.take i) t ∧ EStep K A l g t e q := by
  induction hr generalizing i with
  | nil => simp at he
  | step ht he' _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      exact ⟨_, _, Flow.TraceReach.of_local ht, he'⟩
    | succ i =>
      obtain ⟨t, q, hTrace, hE⟩ := ih (by simpa using he : _[i]? = some e)
      exact ⟨t, q, (Flow.TraceReach.of_local ht).append (.event he' hTrace), hE⟩
  | last ht he' =>
    have hi := (List.getElem?_eq_some_iff.mp he).1
    have h0 : i = 0 := by simp at hi; omega
    subst i
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he
    subst e
    exact ⟨_, _, Flow.TraceReach.of_local ht, he'⟩


/-- The only event a faulted state can reach is its terminating fault. -/
theorem Run.eventOfFault {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {o : Option TState} {k : Nat} {e : Event} {f : Fault}
    (hr : Run K A l g s events o) (hf : s.fault = some f) (he : events[k]? = some e) :
    e.kind = .ub f := by
  obtain ⟨u, _, hReach, hStep⟩ := hr.before_event he
  have hOut : out K A l g s = .ev (.ub f) := by simp [out, hf]
  have hSame : s = u := by
    generalize events.take k = before at hReach
    cases hReach with
    | refl => rfl
    | tau ht _ => rw [Tau, hOut] at ht; cases ht
    | event ht _ =>
      obtain ⟨_, hTempl, hFire⟩ := ht
      rw [hOut] at hTempl
      obtain rfl := Out.ev.inj hTempl
      exact False.elim (by cases hFire.2)
  subst u
  obtain ⟨_, hTempl, hFire⟩ := hStep
  rw [hOut] at hTempl
  obtain rfl := Out.ev.inj hTempl
  exact congrArg Event.kind hFire.1

end PTX
