-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.BulkGroup

namespace PTX.Tests.BulkGroup
open PTX.BulkGroup

-- Two operations share one group; the next issue stays uncommitted.
private def batch : State Nat := run [.issue 10, .issue 11, .commit, .issue 12]
example : batch.groups = [[10, 11]] := rfl
example : batch.pending = [12] := rfl
example : ¬ Observes batch 0 12 := by
  simp [Observes, required, batch, run, step]

-- Empty commits still create groups, so they affect the most-recent-N boundary.
private def emptyTail : State Nat := run [.issue 10, .commit, .commit]
example : emptyTail.groups = [[10], []] := rfl
example : Observes emptyTail 1 10 := by
  simp [Observes, required, emptyTail, run, step]

private def pipeline : State Nat := run [.issue 10, .commit, .issue 11, .commit]
private def readOnly : Completion Nat := ⟨fun i => i = 10, fun _ => False⟩

-- read 1 permits reuse of the old source, without claiming destination completion.
example : WaitReady pipeline readOnly .read 1 := by
  simp [WaitReady, Observes, required, pipeline, readOnly, run, step, Done]
example : ¬ WaitReady pipeline readOnly .full 1 := by
  simp [WaitReady, Observes, required, pipeline, readOnly, run, step, Done]
example : ¬ WaitReady pipeline readOnly .read 0 := by
  simp [WaitReady, Observes, required, pipeline, readOnly, run, step, Done]

-- Completing only the newest group is insufficient: the older group must complete.
example : ¬ WaitReady pipeline ⟨fun i => i = 11, fun i => i = 11⟩ .full 1 := by
  simp [WaitReady, Observes, required, pipeline, run, step, Done]

-- Waiting does not discard group identities or accidentally commit a pending issue.
example : step batch (.wait .full 0) = batch := rfl
example : required (step batch .commit) 1 = required batch 0 := required_commit_succ batch 0

-- The group state belongs to one thread; another thread's empty groups observe none.
example : WaitReady ({} : State Nat) ⟨fun _ => False, fun _ => False⟩ .full 0 := by
  simp [WaitReady, Observes, required]

-- Full completion includes all reads; async-proxy-only waits have a distinct mode.
example (s : State Nat) (c : Completion Nat) (n : Nat) (h : WaitReady s c .full n) :
    WaitReady s c .read n := waitReady_read_of_full h
example : WaitMode.asyncProxy ≠ WaitMode.full := by decide

end PTX.Tests.BulkGroup
