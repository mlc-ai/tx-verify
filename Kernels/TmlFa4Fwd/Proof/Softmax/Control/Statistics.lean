-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.StoreU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow KernelHavoc

set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

theorem stepAt_stat_biasU (v : V) : (code p L g).StepAtU ⟨.stat false,v,0,[]⟩ := by
  refine Code.scalarStoreU (dn := ⟨.narr .bias,v,0,[]⟩) Flow.code_5682 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

theorem stepAt_stat_plainU (v : V) : (code p L g).StepAtU ⟨.stat true,v,0,[]⟩ := by
  refine Code.scalarStoreU (dn := ⟨.narr .plain,v,0,[]⟩) Flow.code_6890 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

theorem stepAt_fin_sumU (v : V) : (code p L g).StepAtU ⟨.fin 0,v,0,[]⟩ := by
  refine Code.scalarStoreU (dn := ⟨.fin 1,v,0,[]⟩) Flow.code_7614 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

theorem stepAt_fin_maxU (v : V) : (code p L g).StepAtU ⟨.fin 1,v,0,[]⟩ := by
  refine Code.scalarStoreU (dn := ⟨.finarr,v,0,[]⟩) Flow.code_7615 rfl rfl rfl
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  dsimp only [code,Softmax.facts]
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
