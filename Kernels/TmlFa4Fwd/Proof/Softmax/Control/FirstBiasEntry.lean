-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.FirstBoundTest
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.NextPlain
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPwE
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailLoop
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
open Epilogue (i32 sub32 addi scmpi)
set_option maxRecDepth 100000
set_option maxHeartbeats 900000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

namespace FirstRound

theorem prepareBias (hp : Pre p L m) (v : V) :
    let u := loopV p L g v
    SegU kernel Assumptions.all L g 5025
      (mid p L g v (valueOf p L g (Softmax.D.mk' (.pwend .first) v.scheduler)))
      5032 (factsFrom ctlBE (valueOf p L g (pwB u.scheduler))) := by
  have hparams := params hp
  dsimp only
  let u := loopV p L g v
  let U := valueOf p L g (pwB u.scheduler)
  refine SegU.comp (b := 5025) (G := mid p L g v U) ?_ ?_
  · unfold mid U
    seg_ctl rules_frame, hooks_ok
  refine SegU.comp (b := 5031) (G := factsFrom ctlBE U) ?_ ?_
  · unfold mid U
    apply ofStrict
    seg_sym using (soft_seg)
  · seg_ctl rules_frame, hooks_ok

end FirstRound
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
