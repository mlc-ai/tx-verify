-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncMBarrier
public import Lemmas.MBarrier.MBarrierHistory

@[expose] public section

namespace PTX.Tests.AsyncMBarrier
open PTX.AsyncCopy
noncomputable section

def src : Acc := { loc := ⟨.global, 0, 0⟩, size := 16 }
def dst : Acc := { loc := ⟨.shared, 0, 0⟩, size := 16 }
def mb : Loc := ⟨.shared, 0, 64⟩
def bytes : List Byte := List.replicate 16 (.bits 32 5, 0)

-- There is deliberately no synthetic destination-write event in the thread.
def thread : Execution where
  tr := fun g => if g = 0 then [⟨0, .mbInit mb 1⟩, ⟨1, .arrive mb 16⟩,
    ⟨2, .copy { src := src, dst := dst, completion := .mbarrier mb }⟩, ⟨3, .wait mb 0 true⟩,
    ⟨4, .exit⟩] else []
  rf := fun _ _ => none

def effects : Snapshot where
  copies := fun i => if i = (0, 2) then
    { readBytes := some bytes, writeBytes := some bytes, notified := true } else {}

def ops : List (Ref × MBarrier.Action) := [
  (.thread (0, 0), .init 1), (.thread (0, 1), .arrive 1 16),
  (.async (0, 2) (.notify .copy), .completeTx 16), (.thread (0, 3), .pollParity 0 true)]

def log : List (MBarrier.Record Ref) := match MBarrier.replay none ops with
  | .ok xs => xs
  | .error _ => []

def logs (m : Loc) : List (MBarrier.Record Ref) := if m = mb then log else []

theorem log_checked : MBarrier.CheckedLog log :=
  MBarrier.checkedLog_of_replay (ops := ops) (by rfl) (by decide)

theorem log_matches : MatchesObject thread effects mb log := by
  intro r hr
  change r ∈ [_, _, _, _] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals refine ⟨by rfl, ?_⟩
  all_goals intro p ok hp _
  all_goals cases hp
  all_goals rfl

/-- The execution with the copy's effects and the object history. -/
def full : Execution := { thread with async := effects, objects := logs }

theorem observes_actual_copy : AsyncObserved full (0, 2) (.notify .copy) (0, 3) true .cta := by
  refine ⟨_, mb, ⟨rfl, 16, { src := src, dst := dst, completion := .mbarrier mb }, rfl, rfl, rfl,
    rfl⟩, ⟨3, 0, rfl⟩, ?_⟩
  rw [show full.objects mb = log by simp [full, logs]]
  exact ⟨2, 3, _, _, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      fun _ _ _ h2 _ => absurd h2 (by omega)⟩

-- Same numeric count and phase at a different address do not authorize the copy.
example : objectAction thread effects ⟨.shared, 0, 128⟩ (.async (0, 2) (.notify .copy)) = none :=
    by rfl

-- A write without a notification does not decrement the object's counter.
example : objectAction thread
    { effects with copies := fun _ =>
      { readBytes := some bytes, writeBytes := some bytes, notified := false } }
    mb (.async (0, 2) (.notify .copy)) = none := by rfl

-- Completing an invented operation cannot be hidden in an otherwise valid log.
example : objectAction thread effects mb (.async (0, 9) (.notify .copy)) = none := by rfl

-- A counter trace produced by a hypothetical manual complete_tx cannot stand in for
-- the async completion, even though its arithmetic and wait result are identical.
def manualLog : List (MBarrier.Record Ref) :=
  log.map (fun r => if r.id = .async (0, 2) (.notify .copy) then { r with id :=
                                                                          .thread (1, 0) } else r)

example : ¬ AsyncObserved { thread with async := effects, objects := fun _ => manualLog }
    (0, 2) (.notify .copy) (0, 3) true .cta := by
  apply no_notification_not_observed
  intro m r hr
  change r ∈ [_, _, _, _] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

end
end PTX.Tests.AsyncMBarrier
