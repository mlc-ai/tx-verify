-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Lemmas.Flow.ArriveU
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
set_option maxRecDepth 100000
set_option maxHeartbeats 900000
variable {p : Params} {L : Launch} {g : Nat}

private theorem keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

theorem barrBiasSpan {m} (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 5279
      (factsFrom (ctlLive 5279) (valueOf p L g ⟨.barr true,v.scheduler,0,[]⟩))
      (Site.pc (.stat false)) (Softmax.facts p L g ⟨.stat false,v.scheduler,0,[]⟩) := by
  have hparams := params hp
  refine SegU.comp (b := 5675)
    (G := factsFrom (ctlLive 5675) (valueOf p L g ⟨.barr true,v.scheduler,0,[]⟩)) ?_ ?_
  · seg_ctl rules_frame, hooks_ok
  · suffices h : ∃ n, Seg kernel Assumptions.all L g n 5675
        (factsFrom (ctlLive 5675) (valueOf p L g ⟨.barr true,v.scheduler,0,[]⟩)) 5682
        (Softmax.facts p L g ⟨.stat false,v.scheduler,0,[]⟩) from
      h.elim fun _ hs => SegU.of_seg hs
    seg_sym using (soft_seg)

theorem stepAt_barrBiasU {m} (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.barr true,v,0,[]⟩ := by
  refine Code.arriveU (dn := ⟨.stat false,v,0,[]⟩) Flow.code_5278 ?_
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · refine SegU.comp (b := 5279) ?_ (barrBiasSpan hp v)
    dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
