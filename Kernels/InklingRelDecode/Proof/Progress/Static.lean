-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Rank
public import Lemmas.Execution.NoTcCp
public import Lemmas.Flow.NotAsyncWait
public import Lemmas.Flow.NotBulkPrefetch
public import Lemmas.Flow.NotTcCp
public import Lemmas.Flow.NotTcShift
public import Lemmas.Flow.WriteBytes

@[expose] public section

/-!
# What the program text says for the progress layer

Facts about the decoded program that need no execution: the kernel's assumptions keep their
well-formedness constraints under every extension of a consistent execution that performs its
commit arrive-ons in issue order and adds no read (`asms_wfStep`), the kernel has no thread fence,
no release store, no atomic, no `tcgen05.cp` or `tcgen05.shift`, no bulk prefetch, no `cp.async`
wait and no bulk-group wait, and so none of the asynchronous obligations that such instructions
would open.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The kernel's assumptions but the read-only input assumption keep their constraints under
every extension that performs the commit arrive-ons in issue order.** Only the commit-order
assumption constrains executions among them (`Assumption.commitPerformedAt_extend`); the poll
agreement and setmaxnreg hooks are not well-formedness constraints. -/
theorem asms_wf_others {X Y : Execution} (hX : Consistent L kernel asms mem0 X) (hle : X.le Y)
    (hord : X.NotifiedInOrder (fun _ => true) Y) :
    ∀ a ∈ asms, a ≠ Assumptions.inputReadOnly → a.wf L mem0 Y := by
  intro a ha hne
  have hwf := hX.asm a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals first
    | trivial
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hwf hX.tcCommit hle hord

/-- **The kernel's assumptions keep their constraints under every extension that performs the
commit arrive-ons in issue order and adds no read**: the read-only input assumption constrains
only the reads at its sites (`Interface.inputReadOnly_wf_ext`). -/
theorem asms_wfStep : Assumption.WfStep (fun _ => true) L kernel mem0 asms := by
  intro X Y hX hle hord hr a ha
  by_cases hne : a = Assumptions.inputReadOnly
  · subst hne
    exact inputReadOnly_wf_ext (hX.asm _ ha) hr
  · exact asms_wf_others hX hle hord a ha hne

/-- The kernel has no thread fence (`fence.sc`, `fence.acq_rel`). -/
theorem kernel_noThreadFence : kernel.code.all (fun ins => !threadFenceOp ins.op) = true := by
  decide +kernel

/-- **The kernel makes no thread fence.** -/
theorem no_threadFence (hX : Consistent L kernel asms mem0 X) (e : EvId) (sem : FenceSem)
    (s : MbarScope) : ¬ X.ThreadFence e sem s := fun ⟨_, he⟩ =>
  no_kind_of_code hX threadFenceOp (fun k => ∃ sem s, k = .fence sem s)
    (fun _ ⟨_, _, h⟩ => by cases h) (fun hf ⟨_, _, hk⟩ => fires_threadFence_op hf hk)
    kernel_noThreadFence he ⟨_, _, rfl⟩

/-- The kernel has no release store. -/
theorem kernel_noRelease : kernel.code.all (fun ins => !releaseOp ins.op) = true := by
  decide +kernel

/-- **No thread's write releases**: the kernel has no release store. -/
theorem no_release (hX : Consistent L kernel asms mem0 X) :
    ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
      X.get e = some ⟨pc, .wr a bs⟩ → a.release = false := by
  intro e pc a bs he
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  · have hr : releaseOp ins.op = false := by
      have := List.all_eq_true.mp kernel_noRelease ins (List.mem_of_getElem? hc)
      simpa using this
    exact Flow.fires_write_release hf rfl hr

/-- **No atomic read-modify-write releases**: the kernel has no atomic. -/
theorem no_release_rmw (hX : Consistent L kernel asms mem0 X) :
    ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false :=
  fun _ _ _ _ _ he => (no_rmw hX he).elim

theorem kernel_noTcCp : kernel.NoTcCp = true := by decide +kernel

/-- **The kernel has no `tcgen05.cp`.** -/
theorem no_tcCp (hX : Consistent L kernel asms mem0 X) : ∀ e c, ¬ X.CpIssue e c :=
  noCp_of_consistent kernel_noTcCp hX

theorem kernel_noTcShift : kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no `tcgen05.shift`.** -/
theorem no_tcShift (hX : Consistent L kernel asms mem0 X) : ∀ e s, ¬ X.ShiftIssue e s :=
  fun _ _ ⟨_, he⟩ => no_kind_of_code hX tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_tcShift_op hf hk)
    kernel_noTcShift he ⟨_, rfl⟩

theorem kernel_noBulkPrefetch : kernel.code.all (fun ins => !bulkPrefetchOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no bulk prefetch.** -/
theorem no_bulkPrefetch (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc : Nat} {a : Acc}, X.get i ≠ some ⟨pc, .bulkPrefetch a⟩ :=
  fun he => no_kind_of_code hX bulkPrefetchOp (fun k => ∃ a, k = .bulkPrefetch a)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_bulkPrefetch_op hf hk)
    kernel_noBulkPrefetch he ⟨_, rfl⟩

theorem kernel_noAsyncWait : kernel.code.all (fun ins => !asyncWaitOp ins.op) = true := by
  decide +kernel

/-- **The kernel has no `cp.async.wait_group`.** -/
theorem no_asyncWait (hX : Consistent L kernel asms mem0 X) :
    ∀ {i : EvId} {pc n : Nat}, X.get i ≠ some ⟨pc, .asyncWait n⟩ :=
  fun he => no_kind_of_code hX asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
    (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_asyncWait_op hf hk)
    kernel_noAsyncWait he ⟨_, rfl⟩

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
