-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame

@[expose] public section

/-! # Invariants and closed-form counts along a thread's states

A proof tool, generic over the kernel (promoted from Inkling's `Proof/Lib/Count.lean`). Two facts
about `Frame.stateAt` of any machine family:

* `stateAt_inv`: an invariant of the position and the state that holds at the first state and is
  kept by each step of the machine along an event of the trace holds at every state the machine
  reaches;
* `count_closed`: the number of the thread's events before a state that satisfy `P` is a
  function `f` of the state when `f` is 0 at the first state and grows by 1 exactly at the steps
  on an event satisfying `P`. This is the ghost counter of `Code.counted` with its closed form
  stated once: the count is never a field of the state, so no statement about the states changes.
-/

namespace PTX.Frame
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- One more event in a prefix adds its count. -/
theorem countP_take_succ_ite (P : Event → Bool) {l : List Event} {k : Nat} {e : Event}
    (he : l[k]? = some e) :
    (l.take (k + 1)).countP P = (l.take k).countP P + (if P e = true then 1 else 0) := by
  rw [List.take_add_one, he]
  simp [List.countP_append]

/-- **An invariant along the thread's states.** -/
theorem stateAt_inv (I : Nat → (C g).D → Prop) (h0 : I 0 (C g).init)
    (hs : ∀ k e s s', (X.tr g)[k]? = some e → stateAt C X g k = some (some s) → I k s →
      (C g).next s e = some (some s') → I (k + 1) s') :
    ∀ k s, k ≤ (X.tr g).length → stateAt C X g k = some (some s) → I k s := by
  intro k
  induction k with
  | zero =>
    intro s _ h
    rw [stateAt_zero] at h
    cases h
    exact h0
  | succ k ih =>
    intro s' hk h
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [stateAt_succ he] at h
    cases hσ : stateAt C X g k with
    | none => rw [hσ] at h; cases h
    | some o =>
      cases o with
      | none => rw [hσ] at h; cases h
      | some s =>
        rw [hσ] at h
        exact hs k e s s' he hσ (ih s (by omega) hσ) h

/-- **A count with a closed form**: the thread's events before a state that satisfy `P` number
`f` of the state. -/
theorem count_closed (P : Event → Bool) (f : (C g).D → Nat) (h0 : f (C g).init = 0)
    (hs : ∀ k e s s', (X.tr g)[k]? = some e → stateAt C X g k = some (some s) →
      ((X.tr g).take k).countP P = f s → (C g).next s e = some (some s') →
      f s' = f s + (if P e = true then 1 else 0)) :
    ∀ k s, stateAt C X g k = some (some s) → ((X.tr g).take k).countP P = f s := by
  have key := stateAt_inv (C := C) (X := X) (g := g)
    (fun k s => ((X.tr g).take k).countP P = f s) (by simp [h0]) (by
      intro k e s s' he hσ hI hn
      rw [countP_take_succ_ite P he, hI, hs k e s s' he hσ hI hn])
  intro k s h
  by_cases hk : k ≤ (X.tr g).length
  · exact key k s hk h
  · rw [stateAt_of_le (by omega)] at h
    rw [List.take_of_length_le (by omega), ← List.take_length (l := X.tr g)]
    exact key _ s le_rfl h

end
end PTX.Frame
