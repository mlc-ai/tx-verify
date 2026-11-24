-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part068
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.AdvanceU
import Lemmas.Flow.Step.TcSteps
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow KernelHavoc

set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

/-- The first round's exponent stretch ends at its first probability store or at UB. -/
theorem stepAt_narr_firstU (v : V) : (code p L g).StepAtU ⟨.narr .first,v,0,[]⟩ := by
  refine Code.advanceU (dn := ⟨.pst .first 0,v,0,[]⟩) Flow.code_4397 rfl
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

/-- The plain round's exponent stretch ends at its plain probability store or at UB. -/
theorem stepAt_narr_plainU (v : V) : (code p L g).StepAtU ⟨.narr .plain,v,0,[]⟩ := by
  refine Code.advanceU (dn := ⟨.pst .plain 0,v,0,[]⟩) Flow.code_6891 rfl
    (fun hf => fires_barArrive_next hf) (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
