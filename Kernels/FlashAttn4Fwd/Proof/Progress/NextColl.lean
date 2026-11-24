-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.NextFire
public import Lemmas.Step.BarArrival
public import Lemmas.Step.RegIssue

@[expose] public section

/-! # Progress at a named barrier, a register request or a paired Tensor Memory operation

A released pending thread whose next event is one of these collective operations performs it:
each is appended to the thread's own trace, whether or not the operation can return yet. The
thread is then blocked at it, and that wait steps by its blocker (`blocked_steps`).

* A named-barrier arrival, `bar.sync` or `bar.arrive` (`bar_next_steps`,
  `Step.barArrival_counted_extension`).
* A register request (`reg_next_steps`, `Step.reg_issue_counted_extension`): the thread has made
  none and its last event is the prologue's cluster wait (`NextFacts.reg_entry`), which a
  released thread has recorded.
* An allocation request, relinquishment or deallocation (`tmem_next_steps`,
  `Step.tccoll_counted_extension`): a warp-collective `tcgen05` event, which writes no memory and
  is no Tensor Memory load. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a named-barrier arrival steps.** -/
theorem bar_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .bar) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨id, u, c, md, rfl⟩
  · exact .inl (Step.barArrival_counted_extension hX hp.1 (.inl hne) hrel (snoc_wf hX) hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩)

/-- **A released pending thread at a register request steps.** -/
theorem reg_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .reg) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  have hX := hc.max.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨⟨pc, op, hlast⟩, hno⟩ := hc.facts.reg_entry hp.1 hσ hk
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire hc hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨inc, n, u, rfl⟩
  · exact Descent.ub_steps_inOrder asms_wfStep hX hp.1 hne hrel hrun hl hout
  · exact .inl (Step.reg_issue_counted_extension (inst := 0) hX hp.1 hlast hrel.ready
      (fun j pc' inc' n' inst' => hno j pc' inc' n' inst') hrun hl (o := some u)
      ⟨_, hout, 0, rfl, rfl⟩ (snoc_wf hX))

/-- **A released pending thread at a paired Tensor Memory operation steps.** -/
theorem tmem_next_steps (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    {d : ThreadD} (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .tmem) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨grp, dst, act, u, rfl⟩
  · exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
      (hX.tcRead_snoc_tc fun _ _ _ h => by cases h) (snoc_wf hX))

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
