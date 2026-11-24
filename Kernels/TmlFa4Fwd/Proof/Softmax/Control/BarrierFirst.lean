-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBarr1
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

theorem barrFirstSpan {m} (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 3591
      (factsFrom (ctlLive 3591) (valueOf p L g ⟨.barr false,v.scheduler,0,[]⟩))
      (Site.pc (.narr .first)) (Softmax.facts p L g ⟨.narr .first,v.scheduler,0,[]⟩) := by
  have eqC (d : Softmax.D) (pc : Nat) : factsFrom (ctlLive pc) (valueOfD p L g d) =
      factsFrom (ctlLive pc) (valueOf p L g d) := by
    apply List.map_congr_left
    intro r hr
    rw [valueOfD_ctl _ (List.mem_filter.mp hr).2]
  obtain ⟨_,ld⟩ := ldp1 (g := g) hp v.scheduler
  rw [eqC] at ld
  refine (SegU.of_seg ld).comp ?_
  obtain ⟨_,mc⟩ := mcnt1 (g := g) hp v.scheduler
  refine SegU.comp ?_ ((SegU.of_seg mc).comp ?_)
  · seg_ctl rules_frame, hooks_ok
  · dsimp only [Softmax.facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_barrFirstU {m} (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.barr false,v,0,[]⟩ := by
  refine Code.arriveU (dn := ⟨.narr .first,v,0,[]⟩) Flow.code_3590 ?_
    (fun _ => rfl) rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
  · change _ ∉ (factsFrom _ _).map Prod.fst
    rw [keys]
    dsimp only [D.scheduler,livePc]
    decide +kernel
  · refine SegU.comp (b := 3591) ?_ (barrFirstSpan hp v)
    dsimp only [code,Softmax.facts]
    seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
