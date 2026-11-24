-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierRound

namespace PTX.Tests.MBarrierRound
open PTX.MBarrier

def run (ops : List (Nat × Action)) : List (Record Nat) := match replay none ops with
  | .ok xs => xs
  | .error _ => []

/-! Executable checks of the premises on concrete histories (test-only). -/

def arrivalsOk (log : List (Record Nat)) (round : Nat → Nat) (T : Nat → Nat) : Bool :=
  (List.range log.length).all fun k =>
    match log[k]? with
    | some r => match r.action, r.fault with
      | .arrive _ tx, none => phaseAt log k == some (round r.id) && tx == T (round r.id)
      | _, _ => true
    | none => true

def releaseOk (log : List (Record Nat)) (round : Nat → Nat) : Bool :=
  (List.range log.length).all fun k =>
    match log[k]? with
    | some r => match r.action, r.fault with
      | .completeTx _, none => round r.id == 0 || (List.range k).any fun j =>
          match log[j]? with
          | some q => q.reply.waited == some true && okBefore log j + 1 == round r.id
          | none => false
      | _, _ => true
    | none => true

def positiveOk (log : List (Record Nat)) : Bool :=
  log.all fun r => match r.action with
    | .completeTx n => decide (0 < n)
    | _ => true

theorem arrivalsOk_sound {log : List (Record Nat)} {round : Nat → Nat} {T : Nat → Nat}
    (h : arrivalsOk log round T = true) : ArrivalsInRound round log T := by
  intro k r n tx hk ha hf
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  simp only [hk, ha, hf, Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem releaseOk_sound {log : List (Record Nat)} {round : Nat → Nat}
    (h : releaseOk log round = true) : NotifiesAfterRelease round log := by
  intro k r n hk ha hf hpos
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  simp only [hk, ha, hf, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at this
  rcases this with h0 | ⟨j, hj, hq⟩
  · omega
  · cases hl : log[j]? with
    | none => simp [hl] at hq
    | some q =>
      simp only [hl, Bool.and_eq_true, beq_iff_eq] at hq
      exact ⟨j, q, hj, hl, hq.1, hq.2⟩

theorem positiveOk_sound {log : List (Record Nat)} (h : positiveOk log = true) :
    ∀ (k : Nat) (r : Record Nat) (n : Nat), log[k]? = some r → r.action = .completeTx n →
      r.fault = none → 0 < n := by
  intro k r n hk ha _
  have := List.all_eq_true.mp h r (List.mem_of_getElem? hk)
  simpa [ha] using this

/-- Rounds without notifications have no bytes; the others are checked one by one. -/
def bytesOk (log : List (Record Nat)) (round : Nat → Nat) (T : Nat → Nat) : Bool :=
  (List.range log.length).all fun k =>
    match log[k]? with
    | some r => decide (roundBytes log round (round r.id) ≤ T (round r.id))
    | none => true

theorem bytesOk_sound {log : List (Record Nat)} {round : Nat → Nat} {T : Nat → Nat}
    (h : bytesOk log round T = true) : ∀ c, roundBytes log round c ≤ T c := by
  intro c
  by_cases hz : roundBytes log round c = 0
  · rw [hz]; exact Int.natCast_nonneg _
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  cases hl : log[k]? with
  | none => simp [completeBytesAt, hl] at hne
  | some r =>
    have hc : round r.id = c := by
      by_contra hc; simp [completeBytesAt, hl, hc] at hne
    have := List.all_eq_true.mp h k hk
    simp only [hl, decide_eq_true_eq, hc] at this
    exact this

/-! A two-round TMA stage. Ids `100 c + x` are round-`c` operations. Each round expects
64 bytes delivered as two 32-byte copies, one of which completes before the producer's
`arrive.expect_tx` (the transaction count goes negative). -/
def round (id : Nat) : Nat := id / 100
def T (_ : Nat) : Nat := 64

def ops : List (Nat × Action) := [
  (1000, .init 1),
  (1, .completeTx 32), (2, .arrive 1 64), (3, .completeTx 32), (1001, .pollParity 0 true),
  (101, .completeTx 32), (102, .arrive 1 64), (1002, .pollParity 1 false),
  (103, .completeTx 32), (1003, .pollParity 1 true)]

def log : List (Record Nat) := run ops

theorem checked : CheckedLog log := checkedLog_of_replay (ops := ops) (by rfl) (by decide)

theorem rounds : ∀ c k r n, log[k]? = some r → r.action = .completeTx n → r.fault = none →
    round r.id = c → phaseAt log k = some c :=
  checked.complete_round round (by decide) T (alternates_sound (by decide))
    (arrivalsOk_sound (by decide)) (releaseOk_sound (by decide)) (positiveOk_sound (by decide))
    (bytesOk_sound (by decide))

-- The early copy of each round, issued before the producer's expect_tx, still belongs to it.
example : phaseAt log 1 = some 0 := rounds 0 1 log[1] 32 rfl rfl rfl rfl
example : phaseAt log 5 = some 1 := rounds 1 5 log[5] 32 rfl rfl rfl rfl
example : phaseAt log 8 = some 1 := rounds 1 8 log[8] 32 rfl rfl rfl rfl
-- Hence the round-1 wait (id 1003) is notified by round-1 copies, while round-0 copies
-- belong to the phase it does not observe.
example : UpdateBeforeWait log 101 1003 :=
  ⟨5, 9, _, _, 1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, by decide,
    NoInval.sameLifetime (by decide) _ _⟩
example : observedAt log 9 = some 1 ∧ phaseAt log 3 = some 0 := by decide

/-! Without the release premise the identity fails: a round-1 copy that completes before
the consumer has released round 0 is counted in phase 0, and a round-0 copy is left for
phase 1, where it would wrongly publish round-1 data. -/
def earlyOps : List (Nat × Action) := [
  (1000, .init 1), (2, .arrive 1 64), (1, .completeTx 32), (101, .completeTx 32),
  (3, .completeTx 32)]

def early : List (Record Nat) := run earlyOps

example : CheckedLog early := checkedLog_of_replay (ops := earlyOps) (by rfl) (by decide)
example : releaseOk early round = false := by decide
example : phaseAt early 3 = some 0 ∧ phaseAt early 4 = some 1 := by decide
-- All other premises still hold, so the release order is what excludes this history.
example : arrivalsOk early round T = true ∧ positiveOk early = true ∧
    bytesOk early round T = true ∧ alternates early 0 = true := by decide

end PTX.Tests.MBarrierRound
