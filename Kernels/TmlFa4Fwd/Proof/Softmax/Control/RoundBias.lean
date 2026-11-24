-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.CloseRound
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.NextPlain
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailLoop
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part102
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
open Epilogue (i32 xor32 addi scmpi)
set_option maxRecDepth 100000
set_option maxHeartbeats 900000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

private def bump (v : V) : V :=
  { v with
    ppar := xor32 v.ppar (i32 1), bpar := xor32 v.bpar (i32 1),
    spar := xor32 v.spar (i32 1), nb := addi v.nb 1 }

private abbrev repeats (v : V) := scmpi .ne .b (addi v.nb 1) (-1)

private def dest (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  if repeats v then ⟨.ws .bias,{bump v with bt := addi v.bt (-1)},0,[]⟩
  else nextPlain p L g (bump v)

private theorem advance (v : V) (m q s) :
    succ p L g ⟨.pwend .bias,v,0,[]⟩ ⟨6558,.wait m q true true s⟩ =
      some (some (dest p L g v)) := by
  simp only [succ,D.scheduler,Softmax.succ,afterRound,afterBias,Softmax.D.ite,plainEntry,
    dest,nextPlain,↓reduceIte]
  cases h₁ : repeats v <;> unfold repeats at h₁ <;>
    simp only [V.scheduler,h₁,↓reduceIte,Bool.false_eq_true]
  · cases h₂ : scmpi .lt .s (r431 p L g v.scheduler) 1 <;>
      simp only [bump,r431,r169,r299,r166,r168,r165,r1808,V.scheduler] at h₂ ⊢ <;>
      simp only [h₂,↓reduceIte,Bool.false_eq_true] <;> rfl
  · rfl

private theorem tail (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 6561 (Softmax.facts p L g ⟨.pwend .bias,v.scheduler,0,[]⟩)
      (dest p L g v).site.pc (Softmax.facts p L g (dest p L g v).scheduler) := by
  unfold dest
  cases hc : repeats v <;> simp only [Bool.false_eq_true,↓reduceIte]
  · refine SegU.comp ?_ (nextPlainSpan hp (bump v))
    refine SegU.comp ?_ (SegU.branch (target := 5032) false Flow.code_6653
      (fun t => braFree t.pc _ _ t rfl) (Epilogue.segFree (by decide)))
    rw [← hc]
    dsimp only [Softmax.facts,entryFacts]
    seg_ctl rules_frame, hooks_ok
  · obtain ⟨_,loop⟩ := biasLoopControl (p := p) (L := L) (g := g) (bump v).scheduler
    refine SegU.comp ?_ (SegU.of_seg loop)
    refine SegU.comp ?_ (SegU.branch (target := 5032) true Flow.code_6653
      (fun t => braFree t.pc _ _ t rfl) (Epilogue.segFree (by decide)))
    rw [← hc]
    dsimp only [Softmax.facts]
    seg_ctl rules_frame, hooks_ok

theorem stepAt_pwend_biasU (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.pwend .bias,v,0,[]⟩ := by
  refine closeRound .bias v (dest p L g v) Flow.code_6558 Flow.code_6559 Flow.code_6560
    (Epilogue.segFree (by decide)) (Epilogue.segFree (by decide)) (by decide +kernel)
    (advance v) ?_ ?_ ?_ (tail hp v)
  all_goals unfold dest nextPlain
  all_goals split <;> try split
  all_goals first | rfl | exact .inl ⟨rfl,rfl,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
