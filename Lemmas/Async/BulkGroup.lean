-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.BulkGroup

@[expose] public section

namespace PTX.BulkGroup

@[simp] theorem required_zero {ι : Type} (s : State ι) : required s 0 = s.groups := by
  simp [required]

theorem observes_zero {ι : Type} (s : State ι) (id : ι) :
    Observes s 0 id ↔ ∃ group ∈ s.groups, id ∈ group := by simp [Observes]

/-- A wait cannot observe an operation merely because it has been issued. -/
theorem observes_committed {ι : Type} {s : State ι} {n : Nat} {id : ι}
    (h : Observes s n id) : ∃ group ∈ s.groups, id ∈ group := by
  obtain ⟨group, hg, hi⟩ := h
  exact ⟨group, List.mem_of_mem_take hg, hi⟩

/-- A later commit followed by wait N+1 observes exactly the previous wait N prefix. -/
theorem required_commit_succ {ι : Type} (s : State ι) (n : Nat) :
    required (step s .commit) (n + 1) = required s n := by
  simp only [required, step, List.length_append, List.length_singleton]
  rw [Nat.add_sub_add_right]
  exact List.take_append_of_le_length (Nat.sub_le _ _)

/-- Grouping never drops an issued operation or introduces a new operation. -/
theorem step_members {ι : Type} (s : State ι) (a : Action ι) :
    (step s a).groups.flatten ++ (step s a).pending =
      s.groups.flatten ++ s.pending ++ (match a with | .issue id => [id] | _ => []) := by
  cases a <;> simp [step, List.flatten_append, List.append_assoc]

/-- Full completion suffices for a read wait; read completion alone is weaker. -/
theorem waitReady_read_of_full {ι : Type} {s : State ι} {c : Completion ι} {n : Nat}
    (h : WaitReady s c .full n) : WaitReady s c .read n := by
  intro id hi
  exact (h id hi).1

theorem waitReady_reads {ι : Type} {s : State ι} {c : Completion ι} {mode : WaitMode}
    {n : Nat} (h : WaitReady s c mode n) {id : ι} (hi : Observes s n id) : c.reads id := by
  cases mode with
  | read => exact h id hi
  | full => exact (h id hi).1
  | asyncProxy => exact (h id hi).1

/-- Folding grouping operations preserves exactly the issue identities in source order.
This list equality accounts for membership; it supplies no memory ordering. -/
theorem fold_members {ι : Type} (s : State ι) (as : List (Action ι)) :
    (as.foldl step s).groups.flatten ++ (as.foldl step s).pending =
      s.groups.flatten ++ s.pending ++
        as.filterMap (fun a => match a with | .issue id => some id | _ => none) := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    rw [ih, step_members]
    cases a <;> simp [List.append_assoc]

theorem run_members {ι : Type} (as : List (Action ι)) :
    (run as).groups.flatten ++ (run as).pending =
      as.filterMap (fun a => match a with | .issue id => some id | _ => none) := by
  simpa [run] using fold_members ({} : State ι) as

end PTX.BulkGroup
