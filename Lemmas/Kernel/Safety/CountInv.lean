-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.StateInv

@[expose] public section

/-! # A fact about the number of a thread's events of a class

`RoleTable.countInv` is `RoleTable.stateInv` with a counter: a predicate of the machine's state and
of the number of the thread's earlier events of a class, kept by every step, holds at every state
with the number read off the trace. The class need not be one of the machine's ghost ledger, so a
new count is a fact in a file of its own. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

/-- **A predicate of the state and of a count of earlier events, kept by every step of a followed
thread, holds at all its states.** -/
theorem RoleTable.countInv (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X)
    (hT : T.ShapeOk S) (hF : T.Followed X S) {g : Nat} (hg : S g) (c : Event → Bool)
    {P : (C g).D → Nat → Prop} (h0 : P (C g).init 0)
    (hstep : ∀ d e d' n, T.J g d → (C g).inv d → T.Ev g d e → P d n →
      (C g).next d e = some (some d') → T.J g d' → P d' (n + if c e then 1 else 0)) :
    ∀ k d, stateAt C X g k = some (some d) → P d (((X.tr g).take k).countP c) := by
  intro k
  induction k with
  | zero =>
    intro d hd
    rw [stateAt_zero] at hd
    cases hd
    simpa using h0
  | succ k ih =>
    intro d hd
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      have hd' := hd
      rw [stateAt_succ he] at hd
      cases hs : stateAt C X g k with
      | none => rw [hs] at hd; cases hd
      | some σ =>
        cases σ with
        | none => exact absurd hs (hF g hg k).1
        | some d0 =>
          rw [hs] at hd
          obtain ⟨hJ, hi, hev⟩ := RoleTable.ev_at hC hX hT hF hg (show X.get (g, k) = some e
            from he) hs
          have h := hstep d0 e d _ hJ hi hev (ih d0 hs) hd ((hF g hg (k + 1)).2 d hd')
          rw [List.take_add_one, he, List.countP_append]
          simpa [List.countP_cons] using h
    · rw [stateAt_of_le (by omega)] at hd
      have h := ih d (by rw [stateAt_of_le (by omega)]; exact hd)
      rw [List.take_of_length_le (by omega)] at h ⊢
      exact h

end PTX.Frame
