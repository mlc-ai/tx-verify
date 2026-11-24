-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.TmemPair

@[expose] public section

/-! # The replay of a recorded completion

A proof tool for `Step.EntryReady`. Appending a record to a history whose replay is not
blocked leaves it unblocked once the record's action is not blocked from the replayed state
(`run_append_ne_blocked`); only an allocation can block (`perform_ne_blocked`), and an empty
allocator never blocks one at column 0 (`perform_empty_alloc`). -/

namespace PTX.Tmem.Pair
open PTX
noncomputable section

/-- Replaying a history with one more record. -/
theorem runRequests_append (s : State) (h : List Requests) (r : Requests) :
    runRequests s (h ++ [r]) =
      match runRequests s h with
      | .done s' => Tmem.perform s' r.action
      | .blocked => .blocked
      | .fault reason => .fault reason := by
  induction h generalizing s with
  | nil =>
    simp only [List.nil_append, runRequests]
    cases Tmem.perform s r.action <;> rfl
  | cons x h ih =>
    simp only [List.cons_append, runRequests]
    cases Tmem.perform s x.action with
    | done next => exact ih next
    | blocked => rfl
    | fault reason => rfl

/-- One more record keeps a replay unblocked when its action is not blocked. -/
theorem run_append_ne_blocked {h : List Requests} {r : Requests}
    (hh : runRequests {} h ≠ .blocked)
    (hs : ∀ s, runRequests {} h = .done s → Tmem.perform s r.action ≠ .blocked) :
    runRequests {} (h ++ [r]) ≠ .blocked := by
  rw [runRequests_append]
  cases hr : runRequests {} h with
  | done s => exact hs s hr
  | blocked => exact absurd hr hh
  | fault reason => simp

/-- Only an allocation can block. -/
theorem perform_ne_blocked {s : Tmem.State} {a : Tmem.Action} (h : ∀ n c, a ≠ .alloc n c) :
    Tmem.perform s a ≠ .blocked := by
  cases a with
  | alloc n c => exact absurd rfl (h n c)
  | dealloc base n =>
    simp only [Tmem.perform]
    split
    · simp
    · split <;> simp
  | relinquish => simp [Tmem.perform]

/-- An empty allocator does not block an allocation at column 0. -/
theorem perform_empty_alloc (n : Nat) : Tmem.perform {} (.alloc n 0) ≠ .blocked := by
  unfold Tmem.perform
  by_cases hv : Tmem.validColumns n = true
  · have hn : n ≤ 512 := by
      simp only [Tmem.validColumns, Bool.or_eq_true, beq_iff_eq] at hv
      omega
    simp [hv, Tmem.available, hn]
  · simp [hv]

end
end PTX.Tmem.Pair
