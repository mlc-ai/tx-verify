-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface
public import Kernels.FlashAttn4Fwd.Proof.Thread.Roles
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Base
public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Step.CommitOrderExtend

@[expose] public section

/-! # FA4's ranks and the steps at its waits

The progress descent ranks FA4's obligations by the library's ranks (`Sched.rank`) of the site
tables' time (`stateTime`, `Thread/Roles.lean`): a pending thread at twice the time of its next
event (`endTime`), plus one while its last event blocks. Every wait steps the same way, by the
library (`Sched.mbar_at_steps` at an mbarrier poll, `Sched.earlier_steps` and
`Sched.same_trace_steps` at a blocking last event); only its blocker differs. The extensions they
build perform no commit arrive-on, so FA4's assumptions keep their constraints
(`asms_wfInOrder`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX PTX.Flow MBarrier

noncomputable section

/-- FA4's assumptions keep their well-formedness constraints under every extension of a
consistent execution that performs its commit arrive-ons in issue order. Only the commit-order
assumption constrains executions (`Assumption.commitPerformedAt_extend`). -/
theorem asms_wfInOrder {L : Launch} {mem0 : Mem0} :
    Assumption.WfInOrder (fun _ => true) L kernel mem0 asms := by
  intro X Y hX hle hord a ha
  have hwf := hX.asm a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  repeat' rcases ha with rfl | ha
  all_goals first
    | trivial
    | exact Assumption.commitPerformedAt_extend (fun _ _ => rfl) hwf hX.tcCommit hle hord

/-- The step lemmas' form of `asms_wfInOrder`: the extensions that add no read. -/
theorem asms_wfStep {L : Launch} {mem0 : Mem0} :
    Assumption.WfStep (fun _ => true) L kernel mem0 asms :=
  asms_wfInOrder.step

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
