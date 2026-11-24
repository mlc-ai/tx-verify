-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Epilogue
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Loop
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Lse
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Mask
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Probability
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteInput

public section

/-! # Soundness of the softmax and output role -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Flow

/-- Every emitted softmax and output site has a local continuation under the launch contract. -/
theorem steps_of_pre {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hg : g < L.threads) (d : D) :
    (code P L g).StepAt d := by
  have hb : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  cases hs : d.site with
  | sink => exact step_sink hpre hb d hs
  | lenOrig => exact step_lenOrig hpre hb d hs
  | lenExtra => exact step_lenExtra hpre hb d hs
  | bulkWait => exact step_bulkWait hpre d hs
  | lastStore => exact step_lastStore hpre hb d hs
  | wg0Sync => exact step_wg0Sync hpre d hs
  | maskReady => exact step_maskReady hpre d hs
  | qkDone => exact step_qkDone hpre d hs
  | fenceLoad => exact step_fenceLoad d hs
  | scoreLoad a k => exact step_scoreLoad hpre d a k hs
  | scoreWait => exact step_scoreWait hpre d hs
  | fenceBefore => exact step_fenceBefore hpre d hs
  | maskRead => exact step_maskRead hpre d hs
  | exchStore i => exact step_exchangeStore hpre d i hs
  | pairBar => exact step_pairBar hpre d hs
  | peerRead i => exact step_peerRead hpre d hs
  | rowMax => exact step_rowMax hpre d hs
  | wg0Sync2 => exact step_wg0Sync2 hpre d hs
  | validFree => exact step_validFree hpre d hs
  | maxRead => exact step_maxRead hpre d hs
  | rescaleVote => exact step_rescaleVote d hs
  | pStore k => exact step_pStore hpre hb d k hs
  | rescaleFence => exact step_rescaleFence d hs
  | rescaleLoad j => exact step_rescaleLoad hpre d j hs
  | rescaleWait j => exact step_rescaleWait hpre d j hs
  | rescaleStore j => exact step_rescaleStore hpre d j hs
  | rescaleWaitSt j => exact step_rescaleWaitSt d j hs
  | rescaleFenceB => exact step_rescaleFenceB d hs
  | soFence => exact step_soFence hpre d hs
  | soReady => exact step_soReady hpre hb d hs
  | lseBar => exact step_lseBar hpre d hs
  | lseStore0 => exact step_lseStore0 hpre d hs
  | lseBar2 => exact step_lseBar2 hpre d hs
  | lseRead => exact step_lseRead hpre hb hq d hs
  | lseStore => exact step_lseStore hpre hb hq d hs
  | svDone => exact step_svDone hpre d hs
  | fenceEpilogue => exact step_fenceEpilogue hpre d hs
  | oLoad j => exact step_oLoad hpre d hs
  | oWait j => exact step_oWait hpre d hs
  | oStage j k => exact step_oStage hpre hg d hs
  | stageFence j => exact step_stageFence d hs
  | epiBar j => exact step_epiBar hpre d hs
  | elect j => exact step_electOutput hpre d hs
  | tmaStore j => exact step_tmaStore d hs
  | commit => exact step_commit d hs
  | everyone => exact step_everyone hpre d hs
  | exit => exact step_exit hpre d hs

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
open PTX PTX.Flow

/-- Every launched lane is simulated by the composed role machine. -/
theorem code_sound {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hg : g < L.threads) : (code P L g).Sound :=
  sound_of_role_steps hpre hg (Wg0.steps_of_pre hpre hg)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Machine
