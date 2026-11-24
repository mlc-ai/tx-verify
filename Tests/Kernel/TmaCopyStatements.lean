-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Theorem

/-! The public theorems of `tma_copy`, the four goals `correct` combines as the proof states
them, and the protocol facts they rest on: the read of `buf` returns the copied word, every
successful poll observes the copy's completion, and a maximal execution has completed the
copy. -/
namespace PTX.Tests.TmaCopyStatements
open PTX PTX.Kernels.TmaCopy PTX.Kernels.TmaCopy.Proof

variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0}

/-- No consistent execution is unsafe. -/
example (hp : Pre L A B x mem0) : SafeGoal kernel [] L mem0 :=
  ⟨rfl, fun _ hX => safe hp (thread_facts hp hX) hX⟩

/-- Every maximal execution is complete. -/
example (hp : Pre L A B x mem0) : ProgressGoal kernel [] L mem0 :=
  progress_goal hp (fun _ hX => thread_facts hp hX)
    ⟨rfl, fun _ hX => safe hp (thread_facts hp hX) hX⟩

/-- Consistent executions have bounded size. -/
example (hp : Pre L A B x mem0) : BoundGoal kernel [] L mem0 :=
  bound_goal hp fun _ hX => thread_facts hp hX

/-- A complete execution leaves the first word of `A` in `B`. -/
example (hp : Pre L A B x mem0) : ResultGoal kernel [] L mem0 (Post B x mem0) :=
  fun _ _ hX hc hfin => result hp (thread_facts hp hX) hX hc hfin

/-- The four goals are `correct`'s fields. -/
example (hp : Pre L A B x mem0) : Correct kernel [] L mem0 (Post B x mem0) :=
  Kernels.TmaCopy.correct hp

/-- The read of `buf` returns the first word of `A`. -/
example (hp : Pre L A B x mem0) {X : Execution} (hX : Consistent L kernel [] mem0 X) {e : EvId}
    {a : Acc} {bs : List (Option Byte)} (hr : X.Reads e a bs) : bs = x.toBytes.map some :=
  read_bytes hp (thread_facts hp hX) hX hr

/-- Every successful wait observes the bulk copy's completion. -/
example (hp : Pre L A B x mem0) {X : Execution} (hX : Consistent L kernel [] mem0 X) {w : EvId}
    {m : Loc} (hw : X.AcquireWait w m) :
    ∃ ws, AsyncCopy.AsyncObserved X (0, 3) (.notify .copy) w true ws :=
  wait_observes_copy (thread_facts hp hX) hX hw

/-- A maximal execution has completed every bulk copy. -/
example (hp : Pre L A B x mem0) {X : Execution} (hm : Maximal L kernel [] mem0 X) :
    ∀ i s, X.Copy i s → (X.async.copies i).notified = true := fun _ _ hb => by
  obtain ⟨-, rfl⟩ := bulk_cases (thread_facts hp hm.1) hm.1 hb
  exact Maximal.bulk_notified wfFree hm (bulkSources hp (thread_facts hp hm.1) hm.1)
    (copyReadOk (thread_facts hp hm.1) hm.1) hb rfl

#print axioms PTX.Kernels.TmaCopy.correct
#print axioms PTX.Kernels.TmaCopy.completed_execution
#print axioms PTX.Kernels.TmaCopy.realizable_result

end PTX.Tests.TmaCopyStatements
