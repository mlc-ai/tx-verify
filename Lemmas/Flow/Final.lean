-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Code

@[expose] public section

/-! # Where a run of a code machine ends

A proof tool. A run of a thread that has not ended stops, after local steps, in a concrete
state of the abstract state its events lead to (`Machine.Sound.final`). Progress proofs use
that state to extend an execution by the thread's next event. -/

namespace PTX.Flow

noncomputable section

namespace Code

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- From the pending fault the machine stays there. -/
theorem after_none (es : List Event) : C.toMachine.after none es = some none := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [Machine.after_cons, toMachine] using ih

end Code

/-- An event that ends the thread: undefined behaviour or the exit. -/
def Ends (e : Event) : Prop := (∃ f, e.kind = .ub f) ∨ e.kind = .exit

/-- An undefined behaviour or the exit does not continue the thread. -/
theorem fires_end_none {pc : Nat} {m : Tmpl} {e : Event} {o : Option TState}
    (hf : Fires pc m e o) (he : Ends e) : o = none := by
  obtain ⟨e, k⟩ := e
  cases m <;> simp only [Fires] at hf
  all_goals first | exact hf.2 | (rcases he with ⟨f, he⟩ | he <;> simp_all)

/-- An undefined behaviour or the exit is the last event of a run. -/
theorem Run.end_last {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {es : List Event} {o : Option TState} (hr : Run K A L g t es o) {j : Nat} {e : Event}
    (he : es[j]? = some e) (hk : Ends e) : j + 1 = es.length := by
  induction hr generalizing j with
  | nil => simp at he
  | step hl hs hrest ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      obtain ⟨m, -, hf⟩ := hs
      cases fires_end_none hf hk
    | succ j =>
      have := ih (by simpa using he)
      simp [this]
  | last hl hs =>
    cases j with
    | zero => rfl
    | succ j => simp at he

/-- An event after which the thread does not continue ends it. -/
theorem fires_none_ends {pc : Nat} {m : Tmpl} {e : Event} (hf : Fires pc m e none) : Ends e := by
  obtain ⟨e, k⟩ := e
  cases m <;> simp only [Fires] at hf
  all_goals first
    | (obtain ⟨he, -⟩ := hf; cases he; exact .inr rfl)
    | (obtain ⟨he, -⟩ := hf; cases he; exact .inl ⟨_, rfl⟩)
    | simp_all

/-- A run that has ended finishes with an event that ends the thread. -/
theorem Run.ended_last {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {es : List Event} (hr : Run K A L g t es none) : ∃ e, es.getLast? = some e ∧ Ends e := by
  generalize ho : (none : Option TState) = o at hr
  induction hr with
  | nil => cases ho
  | step hl hs hrest ih =>
    obtain ⟨e, he, hk⟩ := ih ho
    refine ⟨e, ?_, hk⟩
    rw [List.getLast?_cons, he]; rfl
  | last hl hs =>
    obtain ⟨m, -, hf⟩ := hs
    exact ⟨_, rfl, fires_none_ends hf⟩

end
end PTX.Flow
