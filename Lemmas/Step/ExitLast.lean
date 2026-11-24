-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Correct

@[expose] public section

/-! # An exit event is the last event of its thread

A proof tool. A thread's run goes on only through events that leave a next state; the exit
(and undefined behaviour) template leaves none. So an exit event of a consistent execution is the
last event of its thread (`Execution.exit_last`). -/

namespace PTX

noncomputable section

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An event that leaves a next state is not an exit. -/
theorem Fires.not_exit {pc : Nat} {m : Tmpl} {e : Event} {t : TState}
    (h : Fires pc m e (some t)) {pc' : Nat} : e ≠ ⟨pc', .exit⟩ := by
  intro he
  subst he
  cases m <;> simp [Fires] at h

/-- A run that leaves a next state performs no exit. -/
theorem Run.no_exit {t t' : TState} {l : List Event}
    (h : Run K A L g t l (some t')) {j pc : Nat} : l[j]? ≠ some ⟨pc, .exit⟩ := by
  generalize ho : (some t' : Option TState) = o at h
  induction h generalizing j with
  | nil => simp
  | @step t t1 t2 e rest o _ hs _ ih =>
    obtain ⟨m, -, hf⟩ := hs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, ne_eq, Option.some.injEq]
      exact hf.not_exit
    | succ j =>
      simp only [List.getElem?_cons_succ]
      exact ih ho
  | last _ _ => cases ho

/-- Only the last event of a run is an exit. -/
theorem Run.exit_last {t : TState} {o : Option TState} {l : List Event}
    (h : Run K A L g t l o) {j pc : Nat} (hj : l[j]? = some ⟨pc, .exit⟩) : j + 1 = l.length := by
  induction h generalizing j with
  | nil => simp at hj
  | @step t t1 t2 e rest o _ hs _ ih =>
    obtain ⟨m, -, hf⟩ := hs
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      exact absurd hj (hf.not_exit)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      simp [ih hj]
  | last _ _ =>
    cases j with
    | zero => rfl
    | succ j => simp at hj

end

/-- An exit event of a thread of a consistent execution is its last event. -/
theorem Execution.exit_last {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {g j pc : Nat} (hg : g < L.threads)
    (hj : X.get (g, j) = some ⟨pc, .exit⟩) : j + 1 = (X.tr g).length := by
  obtain ⟨o, hr⟩ := hX.thr g hg
  exact hr.exit_last hj

end

end PTX
