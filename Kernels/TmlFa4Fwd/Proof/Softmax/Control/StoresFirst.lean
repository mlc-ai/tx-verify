-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part101
import Kernels.TmlFa4Fwd.Flow.Code.Part115
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.TensorStoreU
import Lemmas.Flow.Step.TcSteps
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

theorem stepAt_pst_first0U (v : V) : (code p L g).StepAtU ⟨.pst .first 0,v,1,[]⟩ := by
  refine Code.tensorStoreU (dn := ⟨.pst .first 1,v,0,[]⟩) true Flow.code_4826
    ((Assumptions.all_tcStWaitLd _).trans rfl) rfl rfl (fun _ => rfl) rfl rfl
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

theorem stepAt_pst_first1U (v : V) : (code p L g).StepAtU ⟨.pst .first 1,v,0,[]⟩ := by
  refine Code.tensorStoreU (dn := ⟨.pst .first 2,v,0,[]⟩) false Flow.code_4835
    ((Assumptions.all_tcStWaitLd _).trans rfl) rfl rfl (fun _ => rfl) rfl rfl
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

theorem stepAt_pst_first_waitU (v : V) : (code p L g).StepAtU ⟨.pst .first 0,v,0,[]⟩ := by
  apply Code.StepAt.toStepAtU
  refine Code.StepAt.of (fun _ => ⟨_,Flow.code_4826,rfl,trivial⟩) ?_
  exact Code.step_tcStWait (dn := ⟨.pst .first 0,v,1,[]⟩) Flow.code_4826
    ((Assumptions.all_tcStWaitLd _).trans rfl) rfl (fun _ => rfl) rfl rfl rfl rfl
    (fun _ => .inr ⟨rfl,rfl⟩)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
