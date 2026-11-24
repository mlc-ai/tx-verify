-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierHistory

namespace PTX.Tests.MBarrierHistory
open PTX.MBarrier

def ops : List (Nat × Action) := [
  (0, .init 1), (1, .arrive 1 16), (2, .completeTx 16), (3, .pollParity 0 true),
  (4, .arrive 1 16), (5, .completeTx 16), (6, .pollParity 1 true),
  (7, .arrive 1 16), (8, .completeTx 16), (9, .pollParity 0 true)]

def log : List (Record Nat) := match replay none ops with
  | .ok xs => xs
  | .error _ => []

theorem checked : CheckedLog log := checkedLog_of_replay (ops := ops) (by rfl) (by decide)

theorem get_id {i : Nat} {r : Record Nat} (h : log[i]? = some r) : r.id = i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 =>
    have hr := Option.some.inj h; subst r; rfl
  | k + 10 =>
    have hn : log[k + 10]? = none := List.getElem?_eq_none (by change 10 ≤ k + 10; omega)
    rw [hn] at h; cases h

theorem matched_indices {n w : Nat} (h : UpdateBeforeWait log n w) :
    ∃ key, phaseAt log n = some key ∧ observedAt log w = some key := by
  obtain ⟨i, j, r, s, p, hi, hn, _, hj, hw, _, _, _, hp, hq, -⟩ := h
  have hn' : n = i := hn.symm.trans (get_id hi)
  have hw' : w = j := hw.symm.trans (get_id hj)
  exact ⟨p, hn' ▸ hp, hw' ▸ hq⟩

example : UpdateBeforeWait log 2 3 :=
  ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl, SameLifetime.succ _ _⟩

example : UpdateBeforeWait log 5 6 :=
  ⟨5, 6, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl, SameLifetime.succ _ _⟩

example : UpdateBeforeWait log 8 9 :=
  ⟨8, 9, _, _, 2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl, SameLifetime.succ _ _⟩

-- The parity is 0 in both phases, but the phase-0 notification cannot publish phase 2.
example : ¬ UpdateBeforeWait log 2 9 := by
  intro h
  obtain ⟨p, hp, hq⟩ := matched_indices h
  change some 0 = some p at hp
  cases hp
  change some 2 = some 0 at hq
  cases hq

-- Replaying an invalid action reports the operation that fails, rather than omitting it.
example : replay none [(0, .init 1), (1, .init 1)] =
    .error (1, .alreadyInitialized) := by rfl

-- One physical completion cannot be counted twice merely by duplicating its record.
example (r : Record Nat) : ¬ CheckedLog [r, r] := by
  intro h
  simpa using h.1

end PTX.Tests.MBarrierHistory
