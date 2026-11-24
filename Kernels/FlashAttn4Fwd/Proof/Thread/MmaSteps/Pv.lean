-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Cut

@[expose] public section

/-! The MMA warp's PV blocks (2, 4, 6, 7): the elections, the MMAs and the inner P-ready
polls, by `mma_cases` and the slot wrap after PV block 0 (`Cut.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
  (hg : g < L.threads) (pro : Nat → Value) (i tr : Nat) (base : Value) (pr : Nat → Value)

include hpre hg

theorem stepAt_mma2 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 2 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j except [.mma 2 7 => stepOk_mma2_7 hpre hg i tr base pr]

theorem stepAt_mma4 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 4 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_mma6 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 6 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_mma7 (j : Fin 8) :
    (code asms L g pro).StepAt ⟨.mma 7 j, i, tr, base, pr⟩ := by
  mma_cases hpre hg j

theorem stepAt_elM2 : (code asms L g pro).StepAt ⟨.elM 2, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM4 : (code asms L g pro).StepAt ⟨.elM 4, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM6 : (code asms L g pro).StepAt ⟨.elM 6, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_elM7 : (code asms L g pro).StepAt ⟨.elM 7, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_p2Wait (k : Fin 4) (ld : Bool) :
    (code asms L g pro).StepAt ⟨.p2Wait k ld, i, tr, base, pr⟩ := by
  mma_cases hpre hg k ld except [.p2Wait 0 false => stepOk_p2Wait0_false hpre hg i tr base pr]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
