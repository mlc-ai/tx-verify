-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.NextFire

@[expose] public section

/-! # Progress at an mbarrier event, an issue or a cluster barrier operation

A released pending thread performs its next event when it is

* an mbarrier initialization or arrival, with the object's checked record of it
  (`init_next_steps`, `arrive_next_steps`, through `Descent.object_steps_inOrder`): the record
  carries the transition's reply or its fault, so no readiness of the object is needed;
* the issue of a tensor copy or a tensor store (`tensorLoad_next_steps`,
  `tensorStore_next_steps`, `Step.issue_counted_extension_reads`): the copy's effects are
  independent observations, none at issue;
* an MMA or a commit of one lane (`mma_next_steps`, `commit_next_steps`,
  `Step.tc_counted_extension_reads`): the completion and the deliveries are asynchronous
  obligations of their own;
* a cluster barrier operation (`cluster_next_steps`, `Step.cluster_counted_extension`).

The safe prefix these extensions need is the order of the conflicts at the bytes that are read
(`NextSafe.reads`); none of them performs a commit arrive-on. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hc : NextCtx L mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
include hc hp

/-- **A released pending thread at an mbarrier initialization steps.** -/
theorem init_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .init) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨l, c, u, rfl⟩
  · refine Descent.object_steps_inOrder asms_wfStep hX hc.whole.reads hc.guard
      hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
      (.inr ⟨l, c, rfl⟩) (mb := l)
      (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

/-- **A released pending thread at an mbarrier arrival steps.** -/
theorem arrive_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .arrive) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨l, tx, u, c, rl, sc, rfl⟩
  · refine Descent.object_steps_inOrder asms_wfStep hX hc.whole.reads hc.guard
      hc.no_release hc.no_release_rmw hc.no_fence hp.1 (.inl hne) hrel hrun hl hout ⟨rfl, rfl⟩
      (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
      fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

/-- **A released pending thread at a tensor copy issue steps.** -/
theorem tensorLoad_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .tensorLoad) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, s, u, rfl⟩
  · exact .inl (Step.issue_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (e := ⟨t1.pc, .tensorIssue a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩ (.inl ⟨a, s, rfl⟩)
      (snoc_wf hX)
      (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at a tensor store issue steps.** -/
theorem tensorStore_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .tensorStore) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨a, s, u, rfl⟩
  · exact .inl (Step.issue_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (e := ⟨t1.pc, .tensorStore a s⟩) (o := some u) ⟨_, hout, rfl, rfl⟩
      (.inr (.inl ⟨a, s, rfl⟩)) (snoc_wf hX)
      (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at an MMA steps.** -/
theorem mma_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .mma) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨dc, s, acc, ms, u, rfl⟩
  · exact .inl (Step.tc_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (snoc_wf hX)
      (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at a commit steps.** -/
theorem commit_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .commit) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨s, u, rfl⟩
  · exact .inl (Step.tc_counted_extension_reads hX hc.whole.reads hp.1 hne hrel hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (snoc_wf hX)
      (hc.guard.snoc hc.no_release hc.no_release_rmw hc.no_fence (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at a cluster barrier operation steps.** -/
theorem cluster_next_steps (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hk : nextKind d = .cluster) (hrel : Step.Released L X g) : ThreadSteps L mem0 X g := by
  refine next_class hc hp hσ hk (by decide) hrel fun hX hne t t1 m hrun hl hout hm => ?_
  rcases hm with ⟨op, u, rfl⟩
  · exact .inl (Step.cluster_counted_extension hX hp.1 hne hrel (snoc_wf hX) hrun hl
      (o := some u) ⟨_, hout, rfl, rfl⟩)

end

end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
