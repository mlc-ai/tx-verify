-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.NextFire
public import Lemmas.Step.TcLoad
public import Lemmas.Step.BulkWaitReady

@[expose] public section

/-! # Progress at a Tensor Memory load or store, their waits and a bulk-group wait

* A released pending thread whose next event is a Tensor Memory load issues it, each slot
  returning the value the last write of its cell left (`Step.loadVals`): the MMAs' output
  layouts are injective, so that value is unique (`NextCtx.layout`), and every write leaves a
  4-byte word (`NextSafe.words`). The load's implicit wait, a Tensor Memory store and its
  wait are warp-collective `tcgen05` events appended as they are: they write no memory and keep
  the Tensor Core read obligation (`tcLoad_next_steps`, `tcStore_next_steps`).
* A store warp lane at a bulk-group wait performs the wait
  (`Step.BulkWait.bulk_wait_counted_extension`, `bulkWait_next_steps`); while a tensor store it
  observes is not complete, the wait is not ready and the thread is blocked (`bulkWait_steps` in
  `Progress/Collective.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a Tensor Memory load or its wait steps.** -/
theorem tcLoad_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .tcLoad) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, n, sh, k, rfl⟩ | ⟨u, rfl⟩
  · refine .inl (Step.tc_load_counted_extension hX hp.1 hne hrel hrun hl
      (o := some (k (Step.loadVals L asms X g sh a n)))
      ⟨_, hout, _, Step.loadVals_length, rfl, rfl⟩ ?_ (snoc_wf hX))
    intro j v hj hv
    rw [Step.loadVals_length] at hj
    refine ⟨Step.loadVals_spec hX hc.guard hc.layout hj hv, ?_⟩
    obtain ⟨s, hs, -⟩ := hv
    exact hc.whole.words _ _ _ hs
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      (snoc_wf hX))

/-- **A released pending thread at a Tensor Memory store or its wait steps.** -/
theorem tcStore_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .tcStore) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, vs, sh, u, rfl⟩ | ⟨u, rfl⟩
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      (snoc_wf hX))
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
      (snoc_wf hX))

/-- **A released pending thread at a bulk-group wait steps**: it performs the wait. -/
theorem bulkWait_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .bulkWait) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨mode, n, u, rfl⟩
  exact .inl (Step.BulkWait.bulk_wait_counted_extension hX hp.1 hne hrel (snoc_wf hX) hrun hl
    (u := u) ⟨_, hout, rfl, rfl⟩)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
