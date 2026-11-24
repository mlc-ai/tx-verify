-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The MMA warp's QK blocks (0, 1, 3, 5): the elections and the MMAs, by `mma_cases`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
  (hg : g < L.threads) (pro : Nat → Value) (i tr : Nat) (base : Value) (pr : Nat → Value)

include hpre hg

theorem stepAt_mma0 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 0 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_mma1 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 1 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_mma3 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 3 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_mma5 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 5 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_elM0 : (code asms L g pro).StepAt ⟨.elM 0, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM1 : (code asms L g pro).StepAt ⟨.elM 1, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM3 : (code asms L g pro).StepAt ⟨.elM 3, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM5 : (code asms L g pro).StepAt ⟨.elM 5, i, tr, base, pr⟩ := by
  mma_cases hpre hg

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
