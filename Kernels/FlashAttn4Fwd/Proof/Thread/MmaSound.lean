-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps

@[expose] public section

/-! # The MMA warp's obligations as a code machine

`code` (`MmaSteps/Base.lean`) is the role as a code machine on its own (from `setmaxnreg`, item
0, with the prologue's registers `pro`), whose states carry the sub-step of the allocation's
address store (`Site.sub`), and `stepAt` its obligation for every state: every site is an event
instruction whose guard holds by its facts, and every event fired at a state other than the exit
steps to the state `next` gives, or stops the machine. The exit's `ret` ends the thread, so no
step follows it. The machine skeleton composes the role through `Site.pc`, `Site.sub`, `facts`,
`Inv`, `next` and `stepAt`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Every MMA state satisfies the code machine's obligation. -/
theorem stepAt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (pro : Nat → Value) (d : D) : (code asms L g pro).StepAt d := by
  obtain ⟨site, i, tr, base, pr⟩ := d
  mma_cases hpre hg site except [.setMaxReg => stepAt_setMaxReg hpre hg pro i tr base pr,
    .bar0 => stepAt_bar0 hpre hg pro i tr base pr,
    .ldBase => stepAt_ldBase hpre hg pro i tr base pr,
    .relinquish => stepAt_relinquish hpre hg pro i tr base pr,
    .arrivePeer => stepAt_arrivePeer hpre hg pro i tr base pr,
    .dealloc => stepAt_dealloc hpre hg pro i tr base pr,
    .exit => stepAt_exit pro i tr base pr,
    .alloc => stepOk_alloc i tr base pr,
    .allocWrite => stepOk_allocWrite i tr base pr, .shflQ => stepOk_shflQ hpre hg i tr base pr,
    .bar1 => stepOk_bar1 hpre hg i tr base pr,
    .waitDealloc => stepOk_waitDealloc hpre hg i tr base pr,
    .mma 0 _ => stepAt_mma0 hpre hg pro i tr base pr _,
    .mma 1 _ => stepAt_mma1 hpre hg pro i tr base pr _,
    .mma 2 _ => stepAt_mma2 hpre hg pro i tr base pr _,
    .mma 3 _ => stepAt_mma3 hpre hg pro i tr base pr _,
    .mma 4 _ => stepAt_mma4 hpre hg pro i tr base pr _,
    .mma 5 _ => stepAt_mma5 hpre hg pro i tr base pr _,
    .mma 6 _ => stepAt_mma6 hpre hg pro i tr base pr _,
    .mma 7 _ => stepAt_mma7 hpre hg pro i tr base pr _,
    .elM 0 => stepAt_elM0 hpre hg pro i tr base pr,
    .elM 1 => stepAt_elM1 hpre hg pro i tr base pr,
    .elM 2 => stepAt_elM2 hpre hg pro i tr base pr,
    .elM 3 => stepAt_elM3 hpre hg pro i tr base pr,
    .elM 4 => stepAt_elM4 hpre hg pro i tr base pr,
    .elM 5 => stepAt_elM5 hpre hg pro i tr base pr,
    .elM 6 => stepAt_elM6 hpre hg pro i tr base pr,
    .elM 7 => stepAt_elM7 hpre hg pro i tr base pr,
    .shfl _ => stepAt_shfl hpre hg pro i tr base pr _,
    .qWait _ => stepAt_qWait hpre hg pro i tr base pr _,
    .kvWait _ => stepAt_kvWait hpre hg pro i tr base pr _,
    .pWait _ => stepAt_pWait hpre hg pro i tr base pr _,
    .p2Wait _ _ => stepAt_p2Wait hpre hg pro i tr base pr _ _,
    .elC _ => stepAt_elC hpre hg pro i tr base pr _,
    .commit _ => stepAt_commit hpre hg pro i tr base pr _]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
