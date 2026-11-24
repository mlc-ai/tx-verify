-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.FrameStop

@[expose] public section
namespace PTX.Frame

open PTX.Flow
variable {K : Kernel} {A : List Assumption} {L : Launch} {C : ∀ g, Code K A L g}
  {X : Execution} {g k : Nat}

/-- The event that first loses the concrete site in the prefix. It may give up on a returned
value or lead to a dead continuation. Every earlier site, including the source of this event,
is still available for a data invariant. -/
theorem first_stop_event
    (hk : stateAt C X g k = none ∨ stateAt C X g k = some none) :
    ∃ i < k, ∃ d e, X.get (g,i) = some e ∧ stateAt C X g i = some (some d) ∧
      ((C g).next d e = none ∨ (C g).next d e = some none) ∧
      ∀ j ≤ i, ∃ a, stateAt C X g j = some (some a) := by
  classical
  let bad (n : Nat) := stateAt C X g n = none ∨ stateAt C X g n = some none
  have hex : ∃ n, bad n := ⟨k,hk⟩
  let n := Nat.find hex
  have stop : bad n := Nat.find_spec hex
  have hmin : ∀ j < n, ¬ bad j := fun j hj => Nat.find_min hex hj
  have hle : n ≤ k := Nat.find_min' hex hk
  have alive (j : Nat) (hj : j < n) : ∃ d, stateAt C X g j = some (some d) := by
    cases hs : stateAt C X g j with
    | none => exact (hmin j hj (.inl hs)).elim
    | some o =>
      cases o with
      | none => exact (hmin j hj (.inr hs)).elim
      | some d => exact ⟨d,rfl⟩
  cases hn : n with
  | zero =>
    change stateAt C X g n = none ∨ stateAt C X g n = some none at stop
    simp only [hn,stateAt_zero,Option.some.injEq,reduceCtorEq,or_self] at stop
  | succ i =>
    obtain ⟨d,hs⟩ := alive i (by omega)
    change stateAt C X g n = none ∨ stateAt C X g n = some none at stop
    rw [hn] at stop
    have hi : i < (X.tr g).length := by
      by_contra! h
      have heq := (stateAt_of_le (C := C) (X := X) (g := g)
        (k := i+1) (by omega)).trans (stateAt_of_le h).symm
      simp only [heq,hs,Option.some.injEq,reduceCtorEq,or_self] at stop
    have he := List.getElem?_eq_getElem hi
    refine ⟨i,by omega,d,_,he,hs,?_,fun j hj => alive j (by omega)⟩
    rw [stateAt_succ he,hs] at stop
    exact stop

end PTX.Frame
