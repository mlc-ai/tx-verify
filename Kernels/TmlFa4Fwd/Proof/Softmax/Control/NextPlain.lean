-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Entry
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
open Epilogue (scmpi)
set_option maxRecDepth 100000
set_option maxHeartbeats 700000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

def nextPlain (p : Params) (L : Launch) (g : Nat) (v : V) : D :=
  if scmpi .lt .s (r431 p L g v.scheduler) 1 then ⟨.fin 0,v,0,[]⟩
  else ⟨.ws .plain,{v with pl := Mma.neg32 (r431 p L g v.scheduler)},0,[]⟩

private noncomputable abbrev before (p : Params) (L : Launch) (g : Nat) (v : V) :=
  entryFacts p L g 6654 (.pwend .bias) v

private theorem toFinal (hp : Pre p L m) (v : V)
    (hc : scmpi .lt .s (r431 p L g v.scheduler) 1 = true) :
    SegU kernel Assumptions.all L g 6654 (before p L g v) 7614
      (entryFacts p L g 7614 (.fin 0) v) := by
  refine SegU.comp ?_ (enterFinal hp v)
  refine SegU.comp ?_ (SegU.branch (target := 7605) true Flow.code_6656
    (fun t => braFree t.pc _ _ t rfl) (Epilogue.segFree (by decide)))
  rw [← hc]
  unfold before entryFacts
  seg_ctl rules_frame, hooks_ok

private theorem toPlain (hp : Pre p L m) (v : V)
    (hc : scmpi .lt .s (r431 p L g v.scheduler) 1 = false) :
    let u := {v with pl := Mma.neg32 (r431 p L g v.scheduler)}
    SegU kernel Assumptions.all L g 6654 (before p L g v) 6676
      (entryFacts p L g 6676 (.ws .plain) u) := by
  dsimp only
  let u := {v with pl := Mma.neg32 (r431 p L g v.scheduler)}
  have hparams := params hp
  let F := (1491,Value.bits 32 (r431 p L g v.scheduler)) ::
    entryFacts p L g 6654 (.pwend .bias) v
  refine SegU.comp (b := 6656) (G := (643,.pred false) :: F) ?_ ?_
  · rw [← hc]
    unfold F before entryFacts
    seg_ctl rules_frame, hooks_ok
  · refine (SegU.branch false Flow.code_6656 (fun t => braFree t.pc _ _ t rfl)
      (Epilogue.segFree (by decide))).comp ?_
    refine SegU.comp ?_ (enterPlain hp u)
    refine SegU.comp (b := 6660) (G := entryFacts p L g 6661 (.ws .plain) u) ?_ ?_
    · suffices h : ∃ n, Seg kernel Assumptions.all L g n 6657 F 6660
          (entryFacts p L g 6661 (.ws .plain) u) from h.elim fun _ h => SegU.of_seg h
      unfold F entryFacts u
      dsimp only [Softmax.D.mk',V.scheduler]
      seg_sym using (soft_seg)
    · unfold entryFacts
      seg_ctl rules_frame, hooks_ok

theorem nextPlainSpan (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 6654 (entryFacts p L g 6654 (.pwend .bias) v)
      (nextPlain p L g v).site.pc (Softmax.facts p L g (nextPlain p L g v).scheduler) := by
  unfold nextPlain
  split
  · exact toFinal hp v ‹_›
  · exact toPlain hp v (Bool.eq_false_iff.mpr ‹_›)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
