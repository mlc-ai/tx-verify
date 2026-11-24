-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part105
import Kernels.TmlFa4Fwd.Flow.Code.Part106
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Proof.Common.LdWait
import Lemmas.Flow.LandsU
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

private theorem waitStep {c : Fin 4} {v : V} {s : Site} {ds ta sh}
    (hc : kernel.code[(Site.sldw c).pc]? = some ⟨none,.tcLd ds ta sh none⟩)
    (hw : Assumptions.tcLdDataflowSites.contains (Site.sldw c).pc = true)
    (hn : ∀ e, succ p L g ⟨.sldw c,v,1,[]⟩ e = some (some ⟨s,v,0,[]⟩))
    (hi : Inv ⟨s,v,0,[]⟩)
    (seg : SegU kernel Assumptions.all L g ((Site.sldw c).pc+1)
      (Softmax.facts p L g ⟨.sldw c,v.scheduler,1,[]⟩) s.pc
      (Softmax.facts p L g ⟨s,v.scheduler,0,[]⟩)) : (code p L g).StepAtU ⟨.sldw c,v,1,[]⟩ := by
  refine ⟨fun _ => ⟨_,hc,rfl,trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨hpc,hsub,hacc,hfault,hr⟩ := hat
  obtain ⟨rfl,rfl⟩ := fires_tcLd_wait (hpc ▸ (Assumptions.tcLdWait_iff _).trans hw)
    (hsub ▸ Nat.one_ne_zero) hf
  obtain ⟨u,ht,hu⟩ := Code.landsU (C := code p L g) (d := ⟨s,v,0,[]⟩)
    (u := { PTX.next t with sub := 0 }) ⟨congrArg (·+1) hpc,rfl,hacc,hfault,hr⟩ seg hi rfl rfl
  exact .inl (.inr ⟨_,u,hn ⟨(Site.sldw c).pc,.tc .waitLd⟩,ht,hu⟩)

theorem stepAt_sldw0U (v : V) : (code p L g).StepAtU ⟨.sldw 0,v,1,[]⟩ := by
  refine waitStep (s := .sld .plain 1) Flow.code_6679 rfl (fun _ => rfl)
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  unfold Softmax.facts
  seg_ctl rules_frame, hooks_ok

theorem stepAt_sldw1U (v : V) : (code p L g).StepAtU ⟨.sldw 1,v,1,[]⟩ := by
  refine waitStep (s := .sld .plain 2) Flow.code_6696 rfl (fun _ => rfl)
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  unfold Softmax.facts
  seg_ctl rules_frame, hooks_ok

theorem stepAt_sldw2U (v : V) : (code p L g).StepAtU ⟨.sldw 2,v,1,[]⟩ := by
  refine waitStep (s := .sld .plain 3) Flow.code_6713 rfl (fun _ => rfl)
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  unfold Softmax.facts
  seg_ctl rules_frame, hooks_ok

theorem stepAt_sldw3U (v : V) : (code p L g).StepAtU ⟨.sldw 3,v,1,[]⟩ := by
  refine waitStep (s := .stat true) Flow.code_6730 rfl (fun _ => rfl)
    (.inl ⟨rfl,rfl,rfl⟩) ?_
  unfold Softmax.facts
  seg_ctl rules_frame, hooks_ok

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
