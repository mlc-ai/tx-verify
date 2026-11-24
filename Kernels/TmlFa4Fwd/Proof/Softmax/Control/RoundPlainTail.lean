-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.RoundPlainGuard
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
public import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.WaitU
import Lemmas.Flow.BranchU
public import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc

set_option maxRecDepth 100000
set_option maxHeartbeats 900000

namespace PlainWait
open Epilogue (addi scmpi xor32 i32)
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

theorem tail (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 7466
      (Softmax.facts p L g ⟨.pwend .plain,v.scheduler,0,[]⟩) (dest v).site.pc
      (Softmax.facts p L g (dest v).scheduler) := by
  have hparams := params hp
  refine (toGuard v).comp ?_
  let F := factsFrom ((ctlLive 7604).erase 651)
      (valueOf p L g ⟨.pwend .plain,(dest v).v.scheduler,0,[]⟩)
  refine SegU.comp (b := 7604) (G := (651,.pred (cond v)) :: F) ?_ ?_
  · unfold F
    seg_ctl rules_frame, hooks_ok
  · refine (SegU.branch (cond v) Flow.code_7604 (fun t => braFree t.pc _ _ t rfl)
      (Epilogue.segFree (by decide))).comp ?_
    cases hc : cond v <;> simp only [dest,hc,Bool.false_eq_true,↓reduceIte]
    all_goals
      apply ofStrict
      unfold F
      seg_sym using (soft_seg)

end PlainWait

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
