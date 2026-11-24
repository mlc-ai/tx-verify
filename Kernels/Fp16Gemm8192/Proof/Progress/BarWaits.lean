-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ClusterWaits

@[expose] public section

/-! # Progress at a named barrier

The named barriers of the kernel are the consumers': each warp group's CLC barrier and its output
barrier, passed twice per slice of the epilogue. A pending consumer at one of these sites, whose
last event is released, arrives on the barrier: a counted extension (`bar_next_steps`,
`Step.bar_counted_extension`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX PTX.Flow

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Progress at a named barrier site.** A pending consumer at its group's CLC barrier or at a
slice's output barrier, whose last event is released, arrives there: a counted extension. -/
theorem bar_next_steps (ht : ThreadFacts L X) (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {c : Consumer.D}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inr (.cons c))))
    (hs : c.site = .clcBar ∨ (∃ k, c.site = .barA k) ∨ ∃ k, c.site = .barB k)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨t1, u, id, hl, he⟩ := ht.bar_fire hp.1 hσ hs hrun
  have hne : X.tr g ≠ [] := by
    intro h0
    simp only [Frame.stateAt, h0, List.take_nil] at hσ
    cases hσ
  exact .inl (Step.bar_counted_extension hmax.1 hp.1 (.inl hne) hrel (prod_wf _) hrun hl he)

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
