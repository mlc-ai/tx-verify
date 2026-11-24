-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextPlain

@[expose] public section

/-! # Progress at an MMA or a Tensor Core commit

A released pending thread whose next event is an MMA or a Tensor Core commit issues it: one lane
issues it alone, so it is appended in the safe execution (`Step.tc_counted_extension`). The MMA's
completion and the commit's deliveries are asynchronous obligations of their own. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at an MMA steps.** -/
theorem mma_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .mma)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨dc, s, acc, ms, u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
    (strongOrdered hpre hX) hg
      hne hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (prod_wf _)
      (hsg.snoc ht.no_release (rmw_no_release ht hX) (no_fence ht hX)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h)))

/-- **A released pending thread at a Tensor Core commit steps.** -/
theorem commit_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .commit)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨s, u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.tc_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
    (strongOrdered hpre hX) hg
      hne hrel hrun hl (o := some u) ⟨_, hout, rfl, rfl⟩ rfl (prod_wf _)
      (hsg.snoc ht.no_release (rmw_no_release ht hX) (no_fence ht hX)
        (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) (fun _ _ h => by cases h)
        (fun _ _ _ _ _ h => by cases h)))

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
