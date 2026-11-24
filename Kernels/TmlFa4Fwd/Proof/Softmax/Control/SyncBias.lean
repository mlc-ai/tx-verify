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

theorem bsyncBiasOfSpan {m} (hp : Pre p L m) (v : V)
    (tail : SegU kernel Assumptions.all L g 5279
      (factsFrom (ctlLive 5279) (valueOf p L g ⟨.barr true,v.scheduler,0,[]⟩))
      (Site.pc (.stat false)) (Softmax.facts p L g ⟨.stat false,v.scheduler,0,[]⟩)) :
    (code p L g).StepAtU ⟨.bsync true,v,0,[]⟩ := by
  have hparams := params hp
  let cond := scmpi .ne .b (andi (tidW L g) 31) 0
  let F := Softmax.facts p L g (Softmax.D.mk' (.bsync true) v.scheduler)
  have hpred : (632,Value.pred cond) ∈ F :=
    mem_factsFrom (List.contains_iff_mem.mp
      (by decide +kernel : (ctlLive 5271).contains 632 = true))
  have key (e : Event) : (code p L g).next ⟨.bsync true,v,0,[]⟩ e =
      some (some (if cond then ⟨.stat false,v,0,[]⟩ else ⟨.barr true,v,0,[]⟩)) := by
    unfold cond
    simp only [succ,D.scheduler,Softmax.succ,Softmax.D.ite]
    split <;> rfl
  cases hc : cond with
  | false =>
    refine Code.advanceU (dn := ⟨.barr true,v,0,[]⟩) Flow.code_5271 rfl
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e,hc]; rfl)
      rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
    suffices run : ∃ n, Seg kernel Assumptions.all L g n 5272 F 5278
        (Softmax.facts p L g ⟨.barr true,v.scheduler,0,[]⟩) from
      run.elim fun _ h => SegU.of_seg h
    apply Seg.pred_ex hpred hc
    unfold F
    seg_sym using (soft_seg)
  | true =>
    refine Code.advanceU (dn := ⟨.stat false,v,0,[]⟩) Flow.code_5271 rfl
      (fun hf => fires_barSyncN_next hf) (fun e => by rw [key e,hc]; rfl)
      rfl rfl rfl rfl (.inl ⟨rfl,rfl,rfl⟩) ?_
    refine SegU.comp ?_ tail
    suffices run : ∃ n, Seg kernel Assumptions.all L g n 5272 F 5279
        (factsFrom (ctlLive 5279) (valueOf p L g ⟨.barr true,v.scheduler,0,[]⟩)) from
      run.elim fun _ h => SegU.of_seg h
    apply Seg.pred_ex hpred hc
    unfold F
    seg_sym using (soft_seg)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
