-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Lemmas.Flow.AdvanceU
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
set_option maxRecDepth 100000
variable {p : Params} {L : Launch} {g : Nat}

open Epilogue (andi scmpi)

theorem bsyncFirstOfSpan {m} (hp : Pre p L m) (v : V)
    (tail : SegU kernel Assumptions.all L g 3591
      (factsFrom (ctlLive 3591) (valueOf p L g ⟨.barr false,v.scheduler,0,[]⟩))
      (Site.pc (.narr .first)) (Softmax.facts p L g ⟨.narr .first,v.scheduler,0,[]⟩)) :
    (code p L g).StepAtU ⟨.bsync false,v,0,[]⟩ := by
  have hparams := params hp
  let cond := scmpi .ne .b (andi (tidW L g) 31) 0
  let F := Softmax.facts p L g (Softmax.D.mk' (.bsync false) v.scheduler)
  have hpred : (482,Value.pred cond) ∈ F :=
    mem_factsFrom (List.contains_iff_mem.mp
      (by decide +kernel : (ctlLive 3583).contains 482 = true))
  have key (e : Event) : (code p L g).next ⟨.bsync false,v,0,[]⟩ e =
      some (some (if cond then ⟨.narr .first,v,0,[]⟩ else ⟨.barr false,v,0,[]⟩)) := by
    unfold cond
    simp only [succ,D.scheduler,Softmax.succ,Softmax.D.ite]
    split <;> rfl
  cases hc : cond with
  | false =>
    refine Code.advanceU (dn := ⟨.barr false,v,0,[]⟩) Flow.code_3583 rfl
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e,hc]; rfl)
      rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
    suffices run : ∃ n, Seg kernel Assumptions.all L g n 3584 F 3590
        (Softmax.facts p L g ⟨.barr false,v.scheduler,0,[]⟩) from
      run.elim fun _ h => SegU.of_seg h
    apply Seg.pred_ex hpred hc
    unfold F
    seg_sym using (soft_seg)
  | true =>
    refine Code.advanceU (dn := ⟨.narr .first,v,0,[]⟩) Flow.code_3583 rfl
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e,hc]; rfl)
      rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
    refine SegU.comp ?_ tail
    suffices run : ∃ n, Seg kernel Assumptions.all L g n 3584 F 3591
        (factsFrom (ctlLive 3591) (valueOf p L g ⟨.barr false,v.scheduler,0,[]⟩)) from
      run.elim fun _ h => SegU.of_seg h
    apply Seg.pred_ex hpred hc
    unfold F
    seg_sym using (soft_seg)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
