-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FirstStopEvent

@[expose] public section
namespace PTX.Frame

open PTX.Flow

/-- It suffices to exclude UB at live sites and to show that the first loss of a site
ends the thread. The stop obligation sees only the prefix up through the stopping event. -/
theorem noUb_of_first_stop {K : Kernel} {A : List Assumption} {L : Launch}
    {C : ∀ g, Code K A L g} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}
    (hX : Consistent L K A m X)
    (safe : ∀ i d v, X.get (g, i) = some v → stateAt C X g i = some (some d) →
      ∀ f, v.kind ≠ .ub f)
    (stop : ∀ i d v, X.get (g, i) = some v → stateAt C X g i = some (some d) →
      (∀ j ≤ i, ∃ a, stateAt C X g j = some (some a)) →
      ((C g).next d v = none ∨ (C g).next d v = some none) → v.kind = .exit)
    (he : X.get (g, k) = some e) (f : Fault) : e.kind ≠ .ub f := by
  by_cases alive : ∃ d, stateAt C X g k = some (some d)
  · obtain ⟨d, hd⟩ := alive
    exact safe k d e he hd f
  have lost : stateAt C X g k = none ∨ stateAt C X g k = some none := by
    cases h : stateAt C X g k with
    | none => exact .inl rfl
    | some o =>
      cases o with
      | none => exact .inr rfl
      | some d => exact (alive ⟨d, h⟩).elim
  obtain ⟨i, hik, d, ⟨pc, kd⟩, hi, hd, hn, prefixLive⟩ := first_stop_event lost
  have hx := stop i d _ hi hd prefixLive hn
  change kd = .exit at hx
  subst kd
  obtain ⟨r, hr⟩ := hX.thr g (lt_of_get hX he)
  have hl := Flow.Run.end_last hr hi (.inr rfl)
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  omega

/-- At the first stop, a rejected read is impossible if its successor was not dropped. -/
theorem next_none_of_stop {K : Kernel} {A : List Assumption} {L : Launch}
    {C : ∀ g, Code K A L g} {X : Execution} {g k : Nat} {d e}
    (he : X.get (g, k) = some e) (hd : stateAt C X g k = some (some d))
    (h : (C g).next d e = none ∨ (C g).next d e = some none)
    (kept : stateAt C X g (k + 1) ≠ some none) : (C g).next d e = none := by
  rw [stateAt_succ he, hd] at kept
  exact h.resolve_right kept

end PTX.Frame
