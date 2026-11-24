-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.NextFire
public import Lemmas.Step.ReadSource

@[expose] public section

/-! # Progress at a read

A released pending thread whose next event reads shared memory (the CLC response, with acquire
semantics, or the Tensor Memory base) performs the read: every byte takes a source that no write
the read sees hides (`Step.read_source_counted_extension`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released pending thread at a read steps.** -/
theorem read_next_steps (ht : ThreadFacts L X) (hsg : SyncGuarded L kernel X)
    (hub : ¬ HasUb X)
    (hmax : Maximal L kernel Prod mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d = .read)
    (hrel : Step.Released L X g) : Descent.Steps L kernel Prod mem0 (Descent.Obl L)
      (rank L) X (.thread g) := by
  have hX := hmax.1
  have hg := hp.1
  have hne := ne_nil_of_kind hσ (by rw [hk]; decide)
  obtain ⟨t, t1, m, hrun, hl, -, hout, hm⟩ := next_fire ht hX hub hp hσ
  rw [hk] at hm
  rcases hm with ⟨f, rfl⟩ | ⟨a, k, rfl⟩
  · exact Descent.ub_steps prod_wfFree hX hg hne hrel hrun hl hout
  · exact .inl (Step.read_source_counted_extension hX hg hne hrel hrun hl hout
      (fun _ _ _ => prod_wf _) hsg)

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
