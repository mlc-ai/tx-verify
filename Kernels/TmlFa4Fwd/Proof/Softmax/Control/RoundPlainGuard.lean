-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
public import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.WaitU
import Lemmas.Flow.BranchU
public import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc

set_option maxRecDepth 100000
set_option maxHeartbeats 900000

namespace PlainWait

theorem keys {v : Nat → Value} {rs : List Nat} :
    (factsFrom rs v).map Prod.fst = rs := by
  simp only [factsFrom, List.map_map, Function.comp_def]
  exact List.map_id _

open Epilogue (addi scmpi xor32 i32)
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

abbrev cond (v : V) := scmpi .ne .b (addi v.pl 1) 0
def dest (v : V) : D :=
  ⟨if cond v then .ws .plain else .fin 0,
   {v with spar := xor32 v.spar (i32 1), ppar := xor32 v.ppar (i32 1), pl := addi v.pl 1},0,[]⟩

theorem advance (v : V) {e : Event} {m q a s} (h : e.kind = .wait m q true a s) :
    succ p L g ⟨.pwend .plain,v,0,[]⟩ e = some (some (dest v)) := by
  simp only [succ,D.scheduler,Softmax.succ,h,afterRound,afterPlain,Softmax.D.ite]
  cases hc : cond v <;> unfold cond at hc <;>
    simp only [dest,cond,V.scheduler,hc,Bool.false_eq_true,↓reduceIte] <;> rfl

theorem ofStrict {a b F G} (h : ∃ n, Seg kernel Assumptions.all L g n a F b G) :
    SegU kernel Assumptions.all L g a F b G := h.elim fun _ hs => SegU.of_seg hs

theorem toGuard (v : V) : SegU kernel Assumptions.all L g 7466
    (Softmax.facts p L g ⟨.pwend .plain,v.scheduler,0,[]⟩) 7599
    (factsFrom (ctlLive 7599) (valueOf p L g ⟨.pwend .plain,v.scheduler,0,[]⟩)) := by
  dsimp only [Softmax.facts]
  seg_ctl rules_frame, hooks_ok

end PlainWait

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
