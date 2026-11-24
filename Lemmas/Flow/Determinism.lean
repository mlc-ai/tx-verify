-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Thread semantics: determinism

A thread is a function of the values its reads and shuffles return: the state after a
trace is unique (`Run.det`), and a trace can be extended by the next event (`Run.snoc`) or
cut to a prefix (`Run.prefix`).
-/

namespace PTX

section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem tau_det {t t1 t2 : TState} (h1 : Tau K A L g t t1) (h2 : Tau K A L g t t2) :
    t1 = t2 := by
  unfold Tau at h1 h2; rw [h1] at h2; exact Out.tau.inj h2

/-- A state that performs an event has no local step. -/
def Stops (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (t : TState) : Prop :=
  ∃ m, out K A L g t = .ev m

theorem not_tau_of_stops {t t' : TState} (hs : Stops K A L g t) : ¬ Tau K A L g t t' := by
  obtain ⟨m, hm⟩ := hs; intro h; unfold Tau at h; rw [hm] at h; cases h

theorem stops_of_estep {t : TState} {e : Event} {o : Option TState} (h : EStep K A L g t e o) :
    Stops K A L g t := by
  obtain ⟨m, hm, -⟩ := h; exact ⟨m, hm⟩

/-- Two local runs from one state: one extends the other. -/
theorem rtg_tau_total {t t1 t2 : TState} (h1 : Relation.ReflTransGen (Tau K A L g) t t1)
    (h2 : Relation.ReflTransGen (Tau K A L g) t t2) :
    Relation.ReflTransGen (Tau K A L g) t1 t2 ∨ Relation.ReflTransGen (Tau K A L g) t2 t1 := by
  induction h1 generalizing t2 with
  | refl => exact .inl h2
  | @tail b c hb hbc ih =>
    rcases ih h2 with h | h
    · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨d, hbd, hd⟩
      · exact .inr (.single hbc)
      · rw [tau_det hbc hbd]; exact .inl hd
    · exact .inr (h.tail hbc)

/-- The first state that performs an event is unique. -/
theorem stop_unique {t t1 t2 : TState} (h1 : Relation.ReflTransGen (Tau K A L g) t t1)
    (h2 : Relation.ReflTransGen (Tau K A L g) t t2) (s1 : Stops K A L g t1)
    (s2 : Stops K A L g t2) : t1 = t2 := by
  rcases rtg_tau_total h1 h2 with h | h
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨d, hd, -⟩
    · rfl
    · exact absurd hd (not_tau_of_stops s1)
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨d, hd, -⟩
    · rfl
    · exact absurd hd (not_tau_of_stops s2)

theorem fires_det {pc : Nat} {m : Tmpl} {e : Event} {o o' : Option TState}
    (h : Fires pc m e o) (h' : Fires pc m e o') : o = o' := by
  cases m <;> simp only [Fires] at h h'
  all_goals try exact h.2.trans h'.2.symm
  case read | readNC =>
    obtain ⟨bs, _, rfl, rfl⟩ := h
    obtain ⟨bs', _, he, rfl⟩ := h'
    cases he
    rfl
  case elect | shfl | match_ =>
    obtain ⟨r, k, rfl, rfl⟩ := h
    obtain ⟨r', k', he, rfl⟩ := h'
    cases he
    rfl
  case setMaxReg | warpBar | wait | vote | voteMode | redux | activemask =>
    obtain ⟨v, rfl, rfl⟩ := h
    obtain ⟨v', he, rfl⟩ := h'
    cases he
    rfl
  case tcAllocStore =>
    obtain ⟨_, -, -, rfl⟩ := h
    obtain ⟨_, -, -, rfl⟩ := h'
    rfl
  case tcLd =>
    obtain ⟨vs, _, rfl, rfl⟩ := h
    obtain ⟨vs', _, he, rfl⟩ := h'
    cases he
    rfl
  case rmw =>
    obtain ⟨old, -, he, ho⟩ := h
    obtain ⟨old', -, he', ho'⟩ := h'
    rw [he] at he'
    injection he' with _ hk
    injection hk with _ hr _
    subst hr
    rw [ho, ho']
  case matrix =>
    obtain ⟨r, he, ho⟩ := h
    obtain ⟨r', he', ho'⟩ := h'
    rw [he] at he'
    injection he' with _ hk
    injection hk with _ _ hr
    subst hr
    rw [ho, ho']
  case sreg =>
    obtain ⟨r, -, he, ho⟩ := h
    obtain ⟨r', -, he', ho'⟩ := h'
    rw [he] at he'
    injection he' with _ hk
    injection hk with _ hr
    subst hr
    rw [ho, ho']

theorem estep_det {t : TState} {e : Event} {o o' : Option TState} (h : EStep K A L g t e o)
    (h' : EStep K A L g t e o') : o = o' := by
  obtain ⟨m, hm, hf⟩ := h; obtain ⟨m', hm', hf'⟩ := h'
  rw [hm] at hm'; cases hm'; exact fires_det hf hf'

/-- The state after a trace is unique. -/
theorem Run.det {t : TState} {l : List Event} {o o' : Option TState}
    (h : Run K A L g t l o) (h' : Run K A L g t l o') : o = o' := by
  induction h generalizing o' with
  | nil => cases h'; rfl
  | @step t t1 t2 e rest o hl he hr ih =>
    cases h' with
    | step hl' he' hr' =>
      have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
      subst e1
      have e2 := estep_det he he'
      cases e2
      exact ih hr'
    | last hl' he' =>
      have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
      subst e1
      cases estep_det he he'
  | @last t t1 e hl he =>
    cases h' with
    | step hl' he' hr' =>
      have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
      subst e1
      cases estep_det he he'
    | last => rfl

/-- Extend a trace by the next event. -/
theorem Run.snoc {t t' t1 : TState} {l : List Event} {e : Event} {o : Option TState}
    (h : Run K A L g t l (some t')) (hl : Relation.ReflTransGen (Tau K A L g) t' t1)
    (he : EStep K A L g t1 e o) : Run K A L g t (l ++ [e]) o := by
  induction l generalizing t with
  | nil =>
    cases h
    cases o with
    | none => exact .last hl he
    | some t2 => exact .step hl he (.nil t2)
  | cons e0 rest ih =>
    cases h with
    | step hl0 he0 hr0 => exact .step hl0 he0 (ih hr0)

/-- A prefix of a trace is a trace. -/
theorem Run.prefix {t : TState} {l1 l2 : List Event} {o : Option TState}
    (h : Run K A L g t (l1 ++ l2) o) : ∃ o1, Run K A L g t l1 o1 := by
  induction l1 generalizing t with
  | nil => exact ⟨some t, .nil t⟩
  | cons e rest ih =>
    generalize hx : (e :: rest) ++ l2 = x at h
    cases h with
    | nil => simp at hx
    | step hl he hr =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨o1, h1⟩ := ih hr
      exact ⟨o1, .step hl he h1⟩
    | last hl he =>
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ⟨none, .last hl he⟩

/-- A trace that ended (`none`) cannot be extended. -/
theorem Run.ended {t : TState} {l l' : List Event} {o : Option TState}
    (h : Run K A L g t l none) (h' : Run K A L g t (l ++ l') o) : l' = [] := by
  induction l generalizing t with
  | nil => cases h
  | cons e rest ih =>
    generalize hx : (e :: rest) ++ l' = x at h'
    cases h with
    | step hl he hr =>
      cases h' with
      | nil => simp at hx
      | step hl' he' hr' =>
        simp only [List.cons_append, List.cons.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
        subst e1
        cases estep_det he he'
        exact ih hr hr'
      | last hl' he' =>
        simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
        subst e1
        cases estep_det he he'
    | last hl he =>
      cases h' with
      | nil => simp at hx
      | step hl' he' hr' =>
        simp only [List.cons_append, List.cons.injEq, List.nil_append] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have e1 := stop_unique hl hl' (stops_of_estep he) (stops_of_estep he')
        subst e1
        cases estep_det he he'
      | last hl' he' =>
        simp only [List.cons_append, List.cons.injEq, List.nil_append] at hx
        exact hx.2

end

end PTX
