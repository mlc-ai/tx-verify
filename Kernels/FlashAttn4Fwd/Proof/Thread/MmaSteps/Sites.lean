-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Ring6
public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Ring11

@[expose] public section

/-! The MMA warp's polls, broadcasts, commit elections and commits outside the asm blocks,
and its single sites, by `mma_cases` and the ring advances (`Ring*.lean`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
  (hg : g < L.threads) (pro : Nat → Value) (i tr : Nat) (base : Value) (pr : Nat → Value)

include hpre hg

theorem stepAt_shfl (k : Fin 14) : (code asms L g pro).StepAt ⟨.shfl k, i, tr, base, pr⟩ := by
  mma_cases hpre hg k

theorem stepAt_qWait (k : Fin 2) : (code asms L g pro).StepAt ⟨.qWait k, i, tr, base, pr⟩ := by
  mma_cases hpre hg k

theorem stepAt_kvWait (k : Fin 4) : (code asms L g pro).StepAt ⟨.kvWait k, i, tr, base, pr⟩ := by
  mma_cases hpre hg k

theorem stepAt_pWait (k : Fin 4) : (code asms L g pro).StepAt ⟨.pWait k, i, tr, base, pr⟩ := by
  mma_cases hpre hg k

theorem stepAt_elC (c : Fin 12) : (code asms L g pro).StepAt ⟨.elC c, i, tr, base, pr⟩ := by
  mma_cases hpre hg c except [.elC 2 => stepOk_elC2 hpre hg i tr base pr,
    .elC 6 => stepOk_elC6 hpre hg i tr base pr, .elC 11 => stepOk_elC11 hpre hg i tr base pr]

theorem stepAt_commit (c : Fin 12) :
    (code asms L g pro).StepAt ⟨.commit c, i, tr, base, pr⟩ := by
  mma_cases hpre hg c except [.commit 2 => stepOk_commit2 hpre hg i tr base pr,
    .commit 6 => stepOk_commit6 hpre hg i tr base pr,
    .commit 11 => stepOk_commit11 hpre hg i tr base pr]

theorem stepAt_setMaxReg : (code asms L g pro).StepAt ⟨.setMaxReg, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_bar0 : (code asms L g pro).StepAt ⟨.bar0, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_ldBase : (code asms L g pro).StepAt ⟨.ldBase, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_relinquish : (code asms L g pro).StepAt ⟨.relinquish, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_arrivePeer : (code asms L g pro).StepAt ⟨.arrivePeer, i, tr, base, pr⟩ := by
  mma_cases hpre hg

theorem stepAt_dealloc : (code asms L g pro).StepAt ⟨.dealloc, i, tr, base, pr⟩ := by
  mma_cases hpre hg

omit hpre hg in
theorem stepAt_exit : (code asms L g pro).StepAt ⟨.exit, i, tr, base, pr⟩ := by
  mma_cases hpre hg

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
