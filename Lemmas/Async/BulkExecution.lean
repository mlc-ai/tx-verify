-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.BulkExecution
public import Lemmas.Async.BulkGroup

@[expose] public section

namespace PTX

private theorem action_issue_thread {g k : Nat} {kind : Kind} {i : EvId}
    (h : bulkAction g k kind = some (.issue i)) : i.1 = g := by
  cases kind <;> simp only [bulkAction] at h <;> try split at h
  all_goals cases h
  all_goals rfl

private theorem actions_issue_thread {g : Nat} {tr : List Event} {i : EvId}
    (h : BulkGroup.Action.issue i ∈ bulkActions g tr) : i.1 = g := by
  obtain ⟨⟨event, k⟩, _, he⟩ := List.mem_filterMap.mp h
  exact action_issue_thread he

/-- A bulk-group wait never acquires another thread's uncommitted or committed operation. -/
theorem BulkWaitsFor.same_thread {X : Execution} {mode : BulkGroup.WaitMode}
    {operation waiter : EvId} (h : BulkWaitsFor X mode operation waiter) :
    operation.1 = waiter.1 := by
  obtain ⟨pc, n, _, ho⟩ := h
  obtain ⟨group, hg, hi⟩ := BulkGroup.observes_committed ho
  have hm : operation ∈ (bulkStateBefore X waiter).groups.flatten :=
    List.mem_flatten.mpr ⟨group, hg, hi⟩
  have ha : operation ∈ (bulkStateBefore X waiter).groups.flatten ++
      (bulkStateBefore X waiter).pending := List.mem_append_left _ hm
  unfold bulkStateBefore at ha
  rw [BulkGroup.run_members] at ha
  obtain ⟨a, ham, he⟩ := List.mem_filterMap.mp ha
  cases a with
  | issue id => cases he; exact actions_issue_thread ham
  | commit => cases he
  | wait mode n => cases he

end PTX
