-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextPlain
public import Lemmas.Step.Object

@[expose] public section

/-! # Progress at an mbarrier initialization or arrival

A released pending thread whose next event initializes or arrives on an mbarrier performs it,
with the object's checked record of it (`Descent.object_steps`): the record carries the
transition's reply or its fault, so no readiness of the object is needed. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX AsyncCopy MBarrier

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at an mbarrier initialization steps.** -/
theorem init_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .init)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨l, c, u, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · refine Descent.object_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩
      (.inr ⟨l, c, rfl⟩) (mb := l) (act := .init c) (fun _ _ h => by cases h) fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

/-- **A released pending thread at an mbarrier arrival steps.** -/
theorem arrive_next_steps (hpre : Pre P L mem0) (ht : ThreadFacts L X)
    (hsg : SyncGuarded L kernel X) (hsafe : ¬ Unsafe L kernel Prod mem0 X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .arrive)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX (fun h => hsafe (.inl h)) hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨l, tx, u, c, rl, sc, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · refine Descent.object_steps prod_wfFree hX hsafe (strongOrdered hpre hX) hsg
      ht.no_release (rmw_no_release ht hX) (no_fence ht hX) hg (.inl hne) hrel hrun hl hout
      ⟨rfl, rfl⟩
      (.inl ⟨l, tx, c, rl, sc, rfl⟩) (mb := l) (act := .arrive c tx) (fun _ _ h => by cases h)
      fun l' => ?_
    by_cases h : l' = l
    · subst h
      simp [objectAction, snoc_get_new]
    · simp [objectAction, snoc_get_new, h, Ne.symm h]

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
