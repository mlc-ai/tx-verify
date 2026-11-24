-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.FirstBiasEntry
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

theorem skipToPlain (v : V) : SegU kernel Assumptions.all L g 6654
    (mid p L g v (valueOf p L g (Softmax.D.mk' (.pwend .first) v.scheduler)))
    6654 (entryFacts p L g 6654 (.pwend .bias) (bump v)) := by
  unfold mid entryFacts
  seg_ctl rules_frame, hooks_ok

end FirstRound
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
