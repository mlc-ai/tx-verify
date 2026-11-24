-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part116
import Lemmas.Flow.ArriveU
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

private theorem keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

theorem stepAt_parr_firstU (v : V) : (code p L g).StepAtU ⟨.parr .first,v,0,[]⟩ := by
  refine Code.arriveU (dn := ⟨.pst .first 3,v,0,[]⟩) Flow.code_4847 ?_
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_parr_biasU (v : V) : (code p L g).StepAtU ⟨.parr .bias,v,0,[]⟩ := by
  refine Code.arriveU (dn := ⟨.pst .bias 3,v,0,[]⟩) Flow.code_6532 ?_
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_parr_plainU (v : V) : (code p L g).StepAtU ⟨.parr .plain,v,0,[]⟩ := by
  refine Code.arriveU (dn := ⟨.pst .plain 3,v,0,[]⟩) Flow.code_7437 ?_
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
