-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace PTX.BulkGroup

/-! ## OBJ-BULK-GROUP — per-thread bulk async-group membership and waits
Statement: A thread's `cp.async.bulk.commit_group` closes the thread's uncommitted bulk operations
  into one group, also when there are none. `cp.async.bulk.wait_group N` covers every committed
  group except the N most recent, and it completes only when the covered operations have finished
  reading their sources (`.read`) or have completed entirely (otherwise). Operations that are not
  yet committed belong to no wait. `cp.async.commit_group` and `cp.async.wait_group N` do the same
  for the thread's `cp.async` operations, in groups of their own, and their wait is a full wait.

Defs: BulkGroup.WaitMode, BulkGroup.State, BulkGroup.Action, BulkGroup.step, BulkGroup.run,
  BulkGroup.required, BulkGroup.Observes, BulkGroup.Completion, BulkGroup.Done, BulkGroup.WaitReady,
  BulkGroup.waitReady_mono, BulkGroup.issue_of_foldl, BulkGroup.issue_of_observes

Source:
- §9.7.10.28.6.1 (commit_group)
- §9.7.10.28.6.2 (wait_group)
- §9.7.10.28.1.1: "The thread issuing the asynchronous operation must create separate async-groups
    for bulk and non-bulk asynchronous operations."
- §9.7.10.28.3.2: "cp.async.commit_group instruction creates a new cp.async-group per thread and
    batches all prior cp.async instructions initiated by the executing thread but not committed to
    any cp.async-group into the new cp.async-group . If there are no uncommitted cp.async
    instructions then cp.async.commit_group results in an empty cp.async-group."
- §9.7.10.28.3.3: "cp.async.wait_group instruction will cause executing thread to wait till only N
    or fewer of the most recent cp.async-group s are pending and all the prior cp.async-group s
    committed by the executing threads are complete."
- §9.7.10.28.3.3: "An empty cp.async-group is considered to be trivially complete."

Direction: reading

Applies: One thread's instructions using bulk-group or `cp.async`-group completion, commits and
  waits

Premises: Operation identities denote actual bulk-group issues by this thread. Completion
  predicates come from the operation's actual effects. The grouping state does not supply them.

Effect: Group membership and wait obligations only. Group list order does not impose memory
  order between operations. The state records source-level grouping. It does not record the
  physical completion order. All committed groups are retained, so group identities are stable
  across waits and later commits; any pipeline depth and any operation count per group is allowed.
  The async-proxy-only wait keeps a distinct mode, so it cannot grant generic-proxy visibility
  through the full-wait adapter. The bulk groups and the `cp.async` groups of a thread are two
  separate states (OBJ-BULK-GROUP-TRACE).
-/
/-- The form of a `cp.async.bulk.wait_group`: `read` waits for the covered operations to finish
reading their sources, `full` waits for them to complete, and `asyncProxy` requires the same
completion as `full` but grants no generic-proxy visibility. -/
inductive WaitMode where
  | read | full | asyncProxy
  deriving DecidableEq, Repr

/-- The grouping state of one thread: its issued operations that are not yet committed, and its
committed groups in commit order. -/
structure State (ι : Type) where
  pending : List ι := []
  groups : List (List ι) := []
  deriving Repr

/-- A bulk-group action of a thread: issuing an operation, `cp.async.bulk.commit_group`, or
`cp.async.bulk.wait_group` with its mode and the number of most recent groups it leaves out. -/
inductive Action (ι : Type) where
  | issue (id : ι)
  | commit
  | wait (mode : WaitMode) (remaining : Nat)
  deriving Repr

/-- The state after one action: an issue adds to the pending operations, a commit closes them into
a new group, and a wait leaves the state unchanged. -/
def step {ι : Type} (s : State ι) : Action ι → State ι
  | .issue id => { s with pending := s.pending ++ [id] }
  | .commit => ⟨[], s.groups ++ [s.pending]⟩
  | .wait _ _ => s

/-- The state after a list of actions, starting from no pending operations and no groups. -/
def run {ι : Type} (actions : List (Action ι)) : State ι := actions.foldl step {}

/-- The groups that a wait leaving out `remaining` groups covers: all committed groups except the
`remaining` most recent. -/
def required {ι : Type} (s : State ι) (remaining : Nat) : List (List ι) :=
  s.groups.take (s.groups.length - remaining)

/-- Membership among the committed groups that this wait observes. -/
def Observes {ι : Type} (s : State ι) (remaining : Nat) (id : ι) : Prop :=
  ∃ group ∈ required s remaining, id ∈ group

/-- The completion state of bulk operations, as predicates on operation identities. -/
structure Completion (ι : Type) where
  /-- All source and (if applicable) tensormap reads have finished. -/
  reads : ι → Prop
  /-- The complete operation has finished, including its destination writes. -/
  full : ι → Prop

/-- The operation `id` is finished for a wait mode: a read wait needs its reads finished, and a
full or async-proxy wait needs its reads finished and the operation complete. -/
def Done {ι : Type} (c : Completion ι) : WaitMode → ι → Prop
  | .read, id => c.reads id
  | .full, id | .asyncProxy, id => c.reads id ∧ c.full id

/-- A wait can complete: every operation it covers is done for its mode. -/
def WaitReady {ι : Type} (s : State ι) (c : Completion ι) (mode : WaitMode)
    (remaining : Nat) : Prop := ∀ id, Observes s remaining id → Done c mode id

/-- A wait that is ready for one completion state is ready for any state in which at least the
same operations have finished. -/
theorem waitReady_mono {ι : Type} {s : State ι} {c c' : Completion ι} {mode : WaitMode}
    {remaining : Nat} (hr : ∀ i, c.reads i → c'.reads i) (hf : ∀ i, c.full i → c'.full i)
    (h : WaitReady s c mode remaining) : WaitReady s c' mode remaining := by
  intro id hid
  have hd := h id hid
  cases mode with
  | read => exact hr id hd
  | full => exact ⟨hr id hd.1, hf id hd.2⟩
  | asyncProxy => exact ⟨hr id hd.1, hf id hd.2⟩

/-- An operation in a group or pending after a list of actions was in a group or pending before,
or was issued by one of the actions. -/
theorem issue_of_foldl {ι : Type} (id : ι) : ∀ (acts : List (Action ι)) (s : State ι),
    ((∃ g ∈ (acts.foldl step s).groups, id ∈ g) ∨ id ∈ (acts.foldl step s).pending) →
    (∃ g ∈ s.groups, id ∈ g) ∨ id ∈ s.pending ∨ Action.issue id ∈ acts
  | [], s, h => by
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | a :: acts, s, h => by
    rcases issue_of_foldl id acts (step s a) h with ⟨g, hg, hid⟩ | hp | hi
    · cases a with
      | issue x => exact Or.inl ⟨g, hg, hid⟩
      | commit =>
        simp only [step, List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact Or.inl ⟨g, hg, hid⟩
        · exact Or.inr (Or.inl hid)
      | wait => exact Or.inl ⟨g, hg, hid⟩
    · cases a with
      | issue x =>
        simp only [step, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact Or.inr (Or.inl hp)
        · exact Or.inr (Or.inr List.mem_cons_self)
      | commit => simp [step] at hp
      | wait => exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hi))

/-- An operation that a wait observes after a list of actions was issued by one of them. -/
theorem issue_of_observes {ι : Type} {actions : List (Action ι)} {remaining : Nat} {id : ι}
    (h : Observes (run actions) remaining id) : Action.issue id ∈ actions := by
  obtain ⟨g, hg, hid⟩ := h
  have hg' : g ∈ (run actions).groups := List.mem_of_mem_take hg
  rcases issue_of_foldl id actions {} (Or.inl ⟨g, hg', hid⟩) with ⟨_, h, _⟩ | h | h
  · simp at h
  · simp at h
  · exact h
end PTX.BulkGroup
