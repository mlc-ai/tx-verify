-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Progress.CollectiveReg
public import Kernels.FlashAttn4Fwd.Proof.Safety.Resource

@[expose] public section

/-! # The register premises of the progress waits, from the safety layer's facts

This file sits at the top of the proof tree, outside the layer order. The progress layer states
what it needs of the register requests in the model's terms (`Progress.RegMatch`,
`Progress.RegExit`); both follow from the safety layer's `Safety.RegFacts`: every request of a
thread is its first, at its warp's site, with its warpgroup's direction and count, and a thread
exits after its request. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- Two register requests of lanes of one warp match. -/
theorem regMatch_of (hR : Safety.RegFacts L X) : Progress.RegMatch L X := by
  intro e f pc pc' n n' inst inst' inc inc' he hf hw hre hrf
  obtain ⟨o1, p1, r1⟩ := hR.request he hre
  obtain ⟨o2, p2, r2⟩ := hR.request hf hrf
  have hwo : warpOf L f.1 = warpOf L e.1 := hw.2.symm
  rw [hwo] at p2 r2
  have hpc : pc' = pc := p2.trans p1.symm
  have hin : (inc', n') = (inc, n) := r2.trans r1.symm
  simp only [Prod.mk.injEq] at hin
  obtain ⟨rfl, rfl⟩ := hin
  subst hpc
  exact ⟨hw, by simp only [o1, o2], pc', inc', n', inst, inst', hre, hrf⟩

/-- A thread exits after its register request. -/
theorem regExit_of (hR : Safety.RegFacts L X) : Progress.RegExit L X :=
  fun hh hk => hR.exit hh hk

end

end PTX.Kernels.FlashAttn4Fwd.Proof
