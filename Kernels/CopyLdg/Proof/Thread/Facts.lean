-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.CopyLdg.Proof.Interface

@[expose] public section

/-! # The thread facts of an execution

Every execution of the kernel has the per-thread facts the layers above use. -/

namespace PTX.Kernels.CopyLdg.Proof

open PTX PTX.Proof PTX.Flow

local notation "Nc" => [Assumptions.ncInput]

noncomputable section

variable {L : Launch} {A B N : Nat} {x : Nat → Value} {mem0 : Mem0} {X : Execution}

/-- The machine never gives up on a thread. -/
theorem tracked : Frame.Tracked (code L A B N) X := by
  refine Frame.tracked_of_next fun g d e => ?_
  cases d <;> simp only [code, next] <;> (try split) <;> (try split) <;> simp

/-- **Every execution of the kernel has the thread facts.** -/
theorem thread_facts (hpre : Pre L A B N x mem0)
    (hX : Consistent L kernel Nc mem0 X) : ThreadFacts L A B N X where
  tracked := tracked
  run_facts := by
    intro g k d hg hσ
    exact run_facts hpre hg (Frame.trace (sound_all hpre) hX hg) k d hσ
  site_event := by
    intro g k e d he hσ
    rcases Frame.fired (sound_all hpre) hX he with ⟨σ, o, hs, t, hgood, hf⟩ | ⟨hs, -⟩
    · have hd : σ = some d := Option.some.inj (hs.symm.trans hσ)
      subst hd
      exact site_event hpre hgood hf
    · exact absurd (hs.symm.trans hσ) (by simp)
  dead_ub := by
    intro g k e he hσ
    have hg := Frame.lt_of_get hX he
    rcases Frame.fired (sound_all hpre) hX he with ⟨σ, o, hs, -⟩ | ⟨-, pc, f, rfl⟩
    · exact absurd (hs.symm.trans hσ) (by simp)
    · obtain ⟨-, bs, hl, hv, ht, hgN⟩ := dead_trace hpre (Frame.trace (sound_all hpre) hX hg) k
        ⟨pc, .ub f⟩ he hσ
      exact ⟨⟨pc, f, rfl⟩, hgN, bs, hl, hv, ht⟩

end
end PTX.Kernels.CopyLdg.Proof
