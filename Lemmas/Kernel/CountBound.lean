-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Followed
public import Lemmas.Kernel.FrameStop

@[expose] public section

/-! # A thread's counted events bounded by a measure of its machine's states

A proof tool for the bound obligation of `Correct` (`terminates_of_count`: every thread's events
that count toward the execution's size, `Event.counts`, are at most `n`). For a thread whose
machine follows it with an invariant `J`, a measure `μ` of the machine's states that never
decreases along a step, increases at every counted event, and is at most `B` under `J` bounds
the thread's counted events by `B + 1` (`counts_le_of_measure`): before the machine stops, the
counted events of a prefix are at most the measure of the state after it; the event at which it
stops or dies adds one, and no event follows a death when a death is the thread's exit, its last
event (`hlast`). A failed poll does not count, so a wait loop that returns to its own state needs
no measure increase. The step obligation is stated at a state of the run and its event, so a role
may use what the execution says of the event (its shape, that no undefined behaviour precedes
it). The measure of a role is typically its loop counters (the closed forms of its
reference invariant) weighted above the position of the site in the loop body. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- **The counted events before a state are at most its measure.** -/
theorem counts_le_measure (J : ∀ g, (C g).D → Prop) (μ : (C g).D → Nat)
    (hfol : ∀ k, FollowedAt C J X g k) (h0 : μ (C g).init = 0)
    (hstep : ∀ k d e d', stateAt C X g k = some (some d) → (X.tr g)[k]? = some e → J g d →
      (C g).next d e = some (some d') → μ d ≤ μ d' ∧ (e.counts = true → μ d < μ d')) :
    ∀ k d, stateAt C X g k = some (some d) → ((X.tr g).take k).countP Event.counts ≤ μ d := by
  intro k
  induction k with
  | zero => intro d hd; rw [stateAt_zero] at hd; cases hd; simp [h0]
  | succ k ih =>
    intro d hd
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [stateAt_succ he] at hd
      cases hs : stateAt C X g k with
      | none => rw [hs] at hd; cases hd
      | some σ =>
        cases σ with
        | none => exact absurd hs (hfol k).1
        | some d0 =>
          rw [hs] at hd
          change (C g).next d0 e = some (some d) at hd
          have hJ := (hfol k).2 d0 hs
          obtain ⟨hle, hlt⟩ := hstep k d0 e d hs he hJ hd
          have := ih d0 hs
          rw [List.take_add_one, he, Option.toList_some, List.countP_append]
          cases hc : e.counts
          · simp [hc]; omega
          · have := hlt hc; simp [hc]; omega
    · rw [stateAt_of_le (by omega)] at hd
      rw [List.take_of_length_le (by omega)]
      have := ih d (by rw [stateAt_of_le (by omega)]; exact hd)
      rw [List.take_of_length_le (by omega)] at this
      exact this

/-- **A followed thread's counted events are at most one more than the measure's bound**, when
its machine dies only at its last event. -/
theorem counts_le_of_measure (J : ∀ g, (C g).D → Prop) (μ : (C g).D → Nat) (B : Nat)
    (hfol : ∀ k, FollowedAt C J X g k) (h0 : μ (C g).init = 0)
    (hB : ∀ d, J g d → μ d ≤ B)
    (hstep : ∀ k d e d', stateAt C X g k = some (some d) → (X.tr g)[k]? = some e → J g d →
      (C g).next d e = some (some d') → μ d ≤ μ d' ∧ (e.counts = true → μ d < μ d'))
    (hlast : ∀ k, stateAt C X g (k + 1) = none → stateAt C X g k ≠ none →
      k + 1 = (X.tr g).length) :
    (X.tr g).countP Event.counts ≤ B + 1 := by
  cases hend : stateAt C X g (X.tr g).length with
  | some σ =>
    cases σ with
    | none => exact absurd hend (hfol _).1
    | some d =>
      have h1 := counts_le_measure J μ hfol h0 hstep _ d hend
      rw [List.take_length] at h1
      have := hB d ((hfol _).2 d hend)
      omega
  | none =>
    obtain ⟨i, d, hi, hd, hdie⟩ := first_stop_any (C := C) (X := X) (g := g) (.inl hend)
    rcases hdie with hdie | hdie
    · have hlen := hlast i hdie (by rw [hd]; simp)
      have h1 := counts_le_measure J μ hfol h0 hstep i d hd
      have hB' := hB d ((hfol i).2 d hd)
      have hsplit : ((X.tr g).take (i + 1)).countP Event.counts ≤
          ((X.tr g).take i).countP Event.counts + 1 := by
        rw [List.take_add_one]
        cases (X.tr g)[i]? <;> simp [List.countP_append]; split <;> omega
      rw [hlen, List.take_length] at hsplit
      omega
    · exact absurd hdie (hfol _).1

end
end PTX.Frame
