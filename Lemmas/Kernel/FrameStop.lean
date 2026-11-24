-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The first stop of a thread's machine

A thread whose machine has stopped by event `k`, into a dead state (`none`) or a state it does
not follow (`some none`), stopped at one event before `k`: the state before that event is
followed and the one after it is not (`first_stop_any`). Unlike `Frame.first_stop`, this needs no
`Tracked` premise, so it applies to machines that give up on a value they do not follow. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- **A thread whose machine has stopped by event `k` stopped at an event before `k`.** -/
theorem first_stop_any {k : Nat}
    (hk : stateAt C X g k = none ∨ stateAt C X g k = some none) :
    ∃ i d, i < k ∧ stateAt C X g i = some (some d) ∧
      (stateAt C X g (i + 1) = none ∨ stateAt C X g (i + 1) = some none) := by
  induction k with
  | zero => rw [stateAt_zero] at hk; simp at hk
  | succ k ih =>
    cases hs : stateAt C X g k with
    | none =>
      obtain ⟨i, d, hi, h1, h2⟩ := ih (.inl hs)
      exact ⟨i, d, by omega, h1, h2⟩
    | some σ =>
      cases σ with
      | none =>
        obtain ⟨i, d, hi, h1, h2⟩ := ih (.inr hs)
        exact ⟨i, d, by omega, h1, h2⟩
      | some d => exact ⟨k, d, by omega, hs, hk⟩

end
end PTX.Frame
