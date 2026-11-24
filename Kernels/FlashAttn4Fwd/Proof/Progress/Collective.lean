-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveReg
public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveTc
public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveTmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits.Cluster
public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveBarGroup
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressWaits
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # Progress at the collective waits

A pending thread whose last event blocks (`Step.Released` fails) has one blocking part
(`Sched.thread_cases`). Each steps by its class, from the facts of `WaitInputs`:

* an unrecorded cluster-barrier operation (`Sched.clusterWait_steps`, at the cluster start
  barrier);
* a register request not every lane of its warp has matched (`reg_steps`);
* a paired Tensor Memory operation that cannot return (`tmemWait_steps`);
* a named-barrier `bar.sync` whose generation is not done (`bar_steps`);
* a warp-collective `tcgen05` event some lane of its warp has not reached (`tc_steps`);
* a `bar.arrive` without its record (`arrive_steps`);
* a bulk-group wait that is not ready (`bulkWait_steps`): an issued tensor store is not done, and
  the store obligation ranks below the thread (`Sched.rank_store_lt`).

`WaitInputs` holds the facts of one consistent execution these classes use: the thread layer's
interface structures (`ClusterFacts`, `TmemFacts`, `StatsFacts`, `TmemLifeFacts`,
`ProgressWaitFacts`) and the register
premises in the model's terms (`RegMatch`, `RegExit`, from the safety layer's
`Safety.RegFacts`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

/-- The facts of one consistent execution that the collective waits use. -/
structure WaitInputs (L : Launch) (X : Execution) : Prop where
  cluster : ClusterFacts L X
  tmem : TmemFacts L X
  stats : StatsFacts L X
  tmemLife : TmemLifeFacts L X
  /-- Two register requests of lanes of one warp match (`Safety.RegFacts.request`). -/
  regMatch : RegMatch L X
  /-- A thread exits after its register request (`Safety.RegFacts.exit`). -/
  regExit : RegExit L X
  waits : ProgressWaitFacts L X
  /-- FA4 issues no `cp.async.wait_group`. -/
  no_asyncWait : ∀ {i : EvId} {pc n : Nat}, X.get i ≠ some ⟨pc, .asyncWait n⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Progress at a bulk-group wait that is not ready.** FA4 issues no linear copy, so an issued
tensor store is not fully done: the store obligation is open and ranks below the thread. -/
theorem bulkWait_steps (hmax : Maximal L kernel asms mem0 X) (htm : TmemFacts L X) {g : Nat}
    (hrel : ¬ Step.Released L X g) (hw : Sched.BulkWait L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  obtain ⟨pc, mode, n, hq, hr⟩ := hw
  refine .inr ⟨X, .store, hmax, fun hd => hr ?_, Sched.rank_store_lt hrel⟩
  exact Step.BulkWait.ready_of_drained hmax.1 hq hd fun i s ⟨pci, hi⟩ _ =>
    (htm.no_bulk hi).elim

/-- **A pending thread whose last event blocks steps**, by the class of its blocking part. -/
theorem blocked_steps (hpre : Pre P L mem0) (hs : SafeGoal kernel asms L mem0)
    (htr : ∀ Y, Consistent L kernel asms mem0 Y → Frame.Tracked (code L) Y)
    (hW : ∀ Y, Consistent L kernel asms mem0 Y → WaitInputs L Y)
    (hNext : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : ¬ Step.Released L X g) :
    Sched.Steps (timed L) mem0 X (.thread g) := by
  have hmax := hNext.max
  have hX := hmax.1
  have hI := hW X hX
  have hst := fun Y hY => (hW Y hY).stats
  have htl := fun Y hY => (hW Y hY).tmemLife
  have hbw := fun Y hY => (hW Y hY).waits.bar
  rcases Sched.thread_cases hX hp.1 (fun _ _ => hI.no_asyncWait) hrel with
    hw | hw | hw | hw | hw | hw | hw
  · exact Sched.clusterWait_steps asms_wfInOrder hI.cluster.toStart hI.waits.cluster.toTimes hmax
      hp hrel hw
  · exact reg_steps hpre hs hI.regMatch hI.regExit hI.waits.reg hmax hp hrel hw
  · exact tmemWait_steps hpre (htr X hX) hI.tmem hI.waits.tmem hI.waits.tc hNext hp hrel hw
  · exact bar_steps hpre hs hst htl hbw (htr X hX) hmax hp hrel hw
  · exact tc_steps hpre hs (htr X hX) hI.waits.tc hmax hp hrel hw
  · exact arrive_steps hpre hs hst htl hbw (htr X hX) hmax hp hrel hw
  · exact bulkWait_steps hmax hI.tmem hrel hw

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
