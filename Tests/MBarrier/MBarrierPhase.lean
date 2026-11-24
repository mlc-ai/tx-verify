-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierPhase

namespace PTX.Tests.MBarrierPhase
open PTX.MBarrier

def run (ops : List (Nat × Action)) : List (Record Nat) := match replay none ops with
  | .ok xs => xs
  | .error _ => []

/-! A TMA stage barrier: arrive.expect_tx, the copy's complete_tx, one consumer wait. -/
def fullOps : List (Nat × Action) := [
  (0, .init 1),
  (1, .arrive 1 64), (2, .pollParity 0 false), (3, .completeTx 64), (4, .pollParity 0 true),
  (5, .arrive 1 64), (6, .completeTx 64), (7, .pollParity 1 true),
  (8, .arrive 1 64), (9, .pollParity 0 false), (10, .completeTx 64), (11, .pollParity 0 true)]

def full : List (Record Nat) := run fullOps

theorem full_checked : CheckedLog full := checkedLog_of_replay (ops := fullOps) (by rfl) (by decide)
theorem full_alt : Alternates full 0 := alternates_sound (by decide)
theorem full_noInval : NoInval full := by decide

-- Each consumer round observes exactly its own phase; failed polls are not counted.
example : observedAt full 4 = some 0 := by
  rw [full_checked.poll_observes full_noInval full_alt (r := full[4]) rfl rfl]; decide
example : observedAt full 7 = some 1 := by
  rw [full_checked.poll_observes full_noInval full_alt (r := full[7]) rfl rfl]; decide
example : observedAt full 11 = some 2 := by
  rw [full_checked.poll_observes full_noInval full_alt (r := full[11]) rfl rfl]; decide

-- Producer arrivals belong to the round counted before them.
example : phaseAt full 8 = some 2 := by
  rw [full_checked.arrive_phase full_noInval full_alt (r := full[8]) rfl rfl rfl]; decide

-- Counter updates of round 2 are what the round-2 wait observes.
example : UpdateBeforeWait full 10 11 :=
  ⟨10, 11, _, _, 2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl, SameLifetime.succ _ _⟩

/-! An empty-slot barrier: the producer's first wait passes on the initial phase (δ = 1). -/
def emptyOps : List (Nat × Action) := [
  (0, .init 1), (1, .pollParity 1 true), (2, .arrive 1), (3, .pollParity 0 true),
  (4, .arrive 1), (5, .pollParity 1 true)]

def empty : List (Record Nat) := run emptyOps

theorem empty_checked : CheckedLog empty :=
  checkedLog_of_replay (ops := emptyOps) (by rfl) (by decide)
theorem empty_alt : Alternates empty 1 := alternates_sound (by decide)
theorem empty_noInval : NoInval empty := by decide

example : ∃ s, stateBefore empty 5 = some s ∧ s.phase + 1 = okBefore empty 5 + 1 :=
  empty_checked.poll_phase empty_noInval (Nat.le_refl 1) empty_alt (r := empty[5]) rfl rfl
-- The initial pass observes no completion; the third wait observes the second release.
example : observedAt empty 1 = none := by decide
example : observedAt empty 5 = some 1 := by decide

/-! The bound is the ISA's: completing a phase before observing the previous one faults. -/
example : perform (some ⟨1, 1, 1, 0, false⟩) (.arrive 1) = .error .precedingPhaseNotObserved := by
  rfl
example : replay none [(0, .init 1), (1, .arrive 1), (2, .arrive 1)] =
    .error (2, .precedingPhaseNotObserved) := by rfl
-- A failed poll does not count as an observation.
example : replay none [(0, .init 1), (1, .arrive 1), (2, .pollParity 1 true), (3, .arrive 1)] =
    .error (3, .precedingPhaseNotObserved) := by rfl
-- complete_tx alone cannot complete a phase whose arrivals are still pending.
example : CheckedLog (run [(0, .init 2), (1, .arrive 1 8), (2, .completeTx 8)]) ∧
    stateBefore (run [(0, .init 2), (1, .arrive 1 8), (2, .completeTx 8)]) 3 =
      some ⟨0, 2, 1, 0, true⟩ :=
  ⟨checkedLog_of_replay (ops := [(0, .init 2), (1, .arrive 1 8), (2, .completeTx 8)])
    (by rfl) (by decide), by decide⟩

/-! Parity is per object, not per thread. Thread 10 waits once with parity 0, but other
successful polls let the object advance: it observes phase 2, as the count predicts. -/
def sharedOps : List (Nat × Action) := [
  (0, .init 1), (1, .arrive 1), (2, .pollParity 0 true), (3, .arrive 1),
  (4, .pollParity 1 true), (5, .arrive 1), (10, .pollParity 0 true)]

def shared : List (Record Nat) := run sharedOps

theorem shared_checked : CheckedLog shared :=
  checkedLog_of_replay (ops := sharedOps) (by rfl) (by decide)

example : observedAt shared 6 = some 2 := by
  rw [shared_checked.poll_observes (by decide) (alternates_sound (by decide))
      (r := shared[6]) rfl rfl]
  decide

-- Without alternation the count is no longer the phase: a repeated parity skips one.
def skipOps : List (Nat × Action) := [
  (0, .init 1), (1, .arrive 1), (2, .pollParity 0 true), (3, .pollParity 0 true)]

example : alternates (run skipOps) 0 = false := by decide
example : observedAt (run skipOps) 3 = some 0 := by decide

-- The run-ahead bound itself, on every prefix of a concrete history.
example : ∀ j ≤ full.length, Bounded (stateBefore full j) (okBefore full j) :=
  fun _ hj => full_checked.bounded hj

/-! Arrival accounting needs no polls: the third producer arrival is in phase 2. -/
example : unitsBefore full 8 = 2 := by decide
example : ∃ s, stateBefore full 8 = some s ∧ unitsBefore full 8 = s.expected * s.phase := by
  have h := full_checked.full_arrival_phase full_noInval (i := 8) (r := full[8])
    (s := ⟨2, 1, 1, 0, true⟩) rfl (by decide) rfl rfl
  refine ⟨⟨2, 1, 1, 0, true⟩, by decide, ?_⟩
  have hi : incrementsBefore full 8 = 0 := by decide
  simp only [hi, Nat.sub_self, Nat.add_zero, Nat.one_mul] at h
  simpa using h

-- Every reachable state satisfies the accounting identity.
example : ∀ j ≤ full.length,
    Accounted (stateBefore full j) (unitsBefore full j) (incrementsBefore full j) :=
  fun _ hj => full_checked.accounted full_noInval hj

-- Two arrivers: units count arrivals, not phases; a third arrival in one phase underflows.
def pairOps : List (Nat × Action) := [
  (0, .init 2), (1, .arrive 1), (2, .arrive 1), (3, .pollParity 0 true), (4, .arrive 1)]

theorem pair_checked : CheckedLog (run pairOps) :=
  checkedLog_of_replay (ops := pairOps) (by rfl) (by decide)
example : unitsBefore (run pairOps) 4 = 2 ∧ phaseAt (run pairOps) 4 = some 1 := by decide
example : replay none [(0, .init 1), (1, .arrive 1 8), (2, .arrive 1)] =
    .error (2, .arrivalUnderflow) := by rfl

-- A faulting arrival is kept in the history but counts no units.
def faultLog : List (Record Nat) :=
  [⟨0, .init 1, ⟨some ⟨0, 1, 1, 0, true⟩, none, none⟩, none⟩,
   ⟨1, .arrive 2, ⟨some ⟨0, 1, 1, 0, true⟩, none, none⟩, some .arrivalUnderflow⟩]

example : CheckedLog faultLog :=
  ⟨by decide, _, .cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.nil _))⟩
example : arrivalUnits faultLog = 0 := by decide

end PTX.Tests.MBarrierPhase
