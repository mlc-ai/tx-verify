-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
public import Lemmas.Flow.NotAsyncWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Reg
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.BarSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TcSteps
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.TmemBlocked
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Bar.Group
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # Progress class: a blocked pending lane

A pending lane that is not released is blocked by its last event (`Sched.thread_cases`): a
cluster-barrier operation, a register request, a paired Tensor Memory operation, a `bar.sync`, a
warp-collective `tcgen05` event, a `bar.arrive` or a bulk-group wait (a `cp.async.wait_group` is
excluded by the premise `hna`). The template is tml-fa4's `Top/Prog/Blocked.lean`.

Proved here, from the code and the rows:

* the code has no `cp.async.wait_group` (`noAsyncWaitCode`) and no cluster operation
  (`noClusterEvent`);
* no barrier event is a `bar.arrive` (`bar_sync`, from the barrier rows `Inputs.bar`);
* a lane blocked at a `bar.sync` steps (`bar_steps`, `Common/Export/BarSteps.lean`: every
  barrier has its participant group, `bar_group`, and the time table's barrier facts);
* a lane blocked at a `setmaxnreg` steps (`reg_steps`, `Common/Export/Reg.lean`: the requests of
  a warp match, an `exit` follows a request, and the time table places a lane without a request
  no later than its warp's request);
* a lane blocked at a warp-collective `tcgen05` event steps (`tc_steps`,
  `Common/Export/TcSteps.lean`: the lanes of warps 0–3 make their collectives in one order up to
  the votes, which lanes of a warp receive alike, and the time table places a lane with fewer
  collectives no later);
* a lane blocked at a Tensor Memory resource operation steps (`Prog.tmem_steps`,
  `Prog/TmemBlocked.lean`);
* a bulk-group wait waits for the tensor stores' reads (`bulk_steps`): the code issues no
  bulk copy (`noCopy`), so a wait that is not ready has an undrained store, and the open store
  obligation ranks below the lane (`Sched.rank_store_lt`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem noAsyncWaitCode : kernel.code.all (fun ins => !asyncWaitOp ins.op) = true := by
  decide +kernel

/-- **A lane blocked at a bulk-group wait steps**: the code issues no bulk copy, so the wait
waits for the tensor stores, whose open obligation ranks below the lane. -/
theorem Prog.bulk_steps (hmax : Maximal L kernel Assumptions.all m X) {g : Nat}
    (hrel : ¬ Step.Released L X g) (hw : Sched.BulkWait L X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨pc, mode, n, hq, hr⟩ := hw
  refine .inr ⟨X, .store, hmax, fun hd => hr ?_, Sched.rank_store_lt hrel⟩
  exact Step.BulkWait.ready_of_drained hmax.1 hq hd fun i s hi _ => (noCopy hmax.1 hi).elim

/-- **A pending lane that is not released steps.** -/
theorem Prog.blocked (hp : Pre P L m) (hIn : Top.Inputs P L m) :
    Prog.BlockedSteps P L m := by
  intro hs X hmax hFw g hpd hrel
  have hX := hmax.1
  have hna : ∀ pc n, X.get (g, (X.tr g).length - 1) ≠ some ⟨pc, .asyncWait n⟩ :=
    fun pc n he => no_kind_of_code hX asyncWaitOp (fun k => ∃ n, k = .asyncWait n)
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_asyncWait_op hf hk)
      noAsyncWaitCode he ⟨n, rfl⟩
  rcases Sched.thread_cases hX hpd.1 hna hrel with h | h | h | h | h | h | h
  · obtain ⟨pc, op, he, -⟩ := h
    exact (noClusterEvent hX he).elim
  · exact reg_steps hp hs hmax hFw hpd hrel h
  · exact Prog.tmem_steps hp hIn hs hmax hFw hpd hrel h
  · have hR := Inputs.bar hIn hp X hX hFw
    exact bar_steps hp hs hmax hFw hR (bar_group hp hR) hpd hrel h
  · exact tc_steps hp hs hmax hFw hpd hrel h
  · obtain ⟨pc, id, cnt, he, -⟩ := h
    have := bar_sync (Inputs.bar hIn hp X hX hFw) hpd.1 he
    cases this
  · exact Prog.bulk_steps hmax hrel h

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
