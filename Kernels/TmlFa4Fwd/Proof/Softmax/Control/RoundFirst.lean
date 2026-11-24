-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.FirstBounds
import Kernels.TmlFa4Fwd.Proof.Softmax.Control.CloseRound
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.NextPlain
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPwE2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailLoop
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
open Epilogue (i32 sub32 addi scmpi)
set_option maxRecDepth 100000
set_option maxHeartbeats 900000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

open FirstRound

private def dest (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  if skipBias p L g v then nextPlain p L g (bump v)
  else ⟨.ws .bias,{loopV p L g v with bt := addi (r169 p L g v.scheduler) (-1)},0,[]⟩

private theorem advance (v : V) (m q s) :
    succ p L g ⟨.pwend .first,v,0,[]⟩ ⟨4874,.wait m q true true s⟩ =
      some (some (dest p L g v)) := by
  let w := v.scheduler
  let a := {w with
    ppar := i32 1, spar := i32 1, mf := finE (foldF p L g w), mr := (foldF p L g w).toReal,
    rs := rs1 p L g w}
  let b := Softmax.D.mk' (.ws .bias) {a with
    nb := sub32 (r299 p L g w) (r166 p L g w), bt := addi (r169 p L g w) (-1), bpar := i32 1}
  simp only [succ,D.scheduler,Softmax.succ,↓reduceIte,Option.map_some,afterRound,afterFirst,
    Softmax.D.ite]
  change some (some (erase (if skipBias p L g v then plainEntry p L g a else b))) = _
  have ha : r431 p L g a = r431 p L g w := r431_eq_of rfl rfl
  have hu : r431 p L g (bump v).scheduler = r431 p L g w := r431_eq_of rfl rfl
  unfold dest
  cases h : skipBias p L g v
  · rfl
  · simp only [↓reduceIte,plainEntry,Softmax.D.ite,nextPlain,ha,hu]
    split <;> rfl

private theorem tail (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 4877 (Softmax.facts p L g ⟨.pwend .first,v.scheduler,0,[]⟩)
      (dest p L g v).site.pc (Softmax.facts p L g (dest p L g v).scheduler) := by
  refine SegU.comp (b := 5006) (G := entryFacts p L g 5006 (.pwend .first) v) ?_ ?_
  · dsimp only [Softmax.facts,entryFacts]
    seg_ctl rules_frame, hooks_ok
  refine (testBound hp v).comp ?_
  refine (SegU.branch (skipBias p L g v) Flow.code_5024 (fun t => braFree t.pc _ _ t rfl)
    (Epilogue.segFree (by decide))).comp ?_
  unfold dest
  cases hc : skipBias p L g v <;> simp only [Bool.false_eq_true,↓reduceIte]
  · obtain ⟨_,loop⟩ := biasLoopControl (p := p) (L := L) (g := g) (loopV p L g v).scheduler
    exact (prepareBias hp v).comp (SegU.of_seg loop)
  · exact (skipToPlain v).comp (nextPlainSpan hp (bump v))

theorem stepAt_pwend_firstU (hp : Pre p L m) (v : V) :
    (code p L g).StepAtU ⟨.pwend .first,v,0,[]⟩ := by
  refine closeRound .first v (dest p L g v) Flow.code_4874 Flow.code_4875 Flow.code_4876
    (Epilogue.segFree (by decide)) (Epilogue.segFree (by decide)) (by decide +kernel)
    (advance v) ?_ ?_ ?_ (tail hp v)
  all_goals unfold dest nextPlain
  all_goals split <;> try split
  all_goals first | rfl | exact .inl ⟨rfl,rfl,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
