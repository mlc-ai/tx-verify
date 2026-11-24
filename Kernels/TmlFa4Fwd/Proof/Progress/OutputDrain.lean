-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Lemmas.Kernel.Progress.Blocked
import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # Progress at the output warp's read waits

The output warp's `cp.async.bulk.wait_group.read` (sites `drain st`) are the kernel's only
bulk-group waits. Released, such a wait is performed like any event that never blocks. Not ready
(`Sched.BulkWait`), it waits for the reads of the warp's tensor stores: the kernel issues no linear
bulk copy (its fourteen `cp.async.bulk.tensor` loads complete on mbarriers, its eight bulk-group
copies are tensor stores), so an issued tensor store is not done, the store obligation is open,
and it ranks below the thread (`drain_steps`, FA4's `bulkWait_steps`). The absence of linear
bulk copies is the premise `hc`, a fact of the code to be proved with the loader fragment (the
copies' shape table). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Progress at a bulk-group wait that is not ready.** -/
theorem drain_steps (hmax : Maximal L kernel Assumptions.all m X)
    (hc : ∀ i s, X.Copy i s → s.completion ≠ .bulkGroup) {g : Nat}
    (hrel : ¬ Step.Released L X g) (hw : Sched.BulkWait L X g) :
    Sched.Steps (timed p L) m X (.thread g) := by
  obtain ⟨pc, mode, n, hq, hr⟩ := hw
  refine .inr ⟨X, .store, hmax, fun hd => hr ?_, Sched.rank_store_lt hrel⟩
  exact Step.BulkWait.ready_of_drained hmax.1 hq hd fun i s hi hs => absurd hs (hc i s hi)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
