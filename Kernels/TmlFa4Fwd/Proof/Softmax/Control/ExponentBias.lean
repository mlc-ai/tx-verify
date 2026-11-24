-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ExponentBiasBranch
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part090
import Kernels.TmlFa4Fwd.Flow.Code.Part093
import Lemmas.Flow.AdvanceU
import Lemmas.Flow.Step.TcSteps
import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow KernelHavoc
noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

open BiasExponent in
theorem stepAt_narr_biasU (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.narr .bias,v,0,[]⟩ := by
  refine Code.advanceU (dn := ⟨.pst .bias 0,v,0,[]⟩) Flow.code_5683 rfl
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  refine SegU.comp (b := 5815)
    (G := (634,.pred (pred p L g v)) :: factsFrom (ctlLive 6299) (before p L g v)) ?_ ?_
  · dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok
  · exact (ctl_branch v).comp (ctl_tail hp v)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
