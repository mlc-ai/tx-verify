-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
public import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part088
import Kernels.TmlFa4Fwd.Flow.Code.Part090
import Kernels.TmlFa4Fwd.Flow.Code.Part093
import Lemmas.Flow.AdvanceU
import Lemmas.Flow.Step.TcSteps
public import Lemmas.Flow.SegCtl
import Lemmas.Flow.SegJump

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow KernelHavoc
noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

namespace BiasExponent

abbrev before (p : Params) (L : Launch) (g : Nat) (v : V) :=
  valueOf p L g (narrB v.scheduler)
abbrev after (p : Params) (L : Launch) (g : Nat) (v : V) :=
  valueOf p L g (pstB0 v.scheduler)
abbrev pred (p : Params) (L : Launch) (g : Nat) (v : V) :=
  Epilogue.scmp .lt .u v.bt (r301 p L g v.scheduler)

theorem ctl_eq (d : Softmax.D) (pc : Nat) :
    factsFrom (ctlLive pc) (valueOfD p L g d) = factsFrom (ctlLive pc) (valueOf p L g d) := by
  apply List.map_congr_left
  intro r hr
  rw [valueOfD_ctl _ (List.mem_filter.mp hr).2]

theorem ctl_tail (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 6299 (factsFrom (ctlLive 6299) (before p L g v))
      6508 (factsFrom (ctlLive 6508) (after p L g v)) := by
  obtain ⟨n,h⟩ := ctlTail hp v.scheduler
  rw [ctl_eq,ctl_eq] at h
  refine (SegU.of_seg h).comp ?_
  seg_ctl rules_frame, hooks_ok

theorem ctl_branch (v : V) :
    SegU kernel Assumptions.all L g 5815
      ((634,.pred (pred p L g v)) :: factsFrom (ctlLive 6299) (before p L g v))
      6299 (factsFrom (ctlLive 6299) (before p L g v)) := by
  cases he : pred p L g v with
  | true =>
    refine (SegU.of_seg (Seg.bra (pick := true) Flow.code_5815 List.mem_cons_self
      (braFree _ _ _) (Gen.segFree _ (by decide)))).comp ?_
    seg_ctl rules_frame, hooks_ok
  | false =>
    refine (SegU.of_seg (Seg.bra (pick := false) Flow.code_5815 List.mem_cons_self
      (braFree _ _ _) (Gen.segFree _ (by decide)))).comp ?_
    refine SegU.comp (b := 5976) (G := factsFrom (ctlLive 6299) (before p L g v)) ?_ ?_
    · seg_ctl rules_frame, hooks_ok
    · exact SegU.of_seg (seg_jmp Flow.code_5976 (braFree _ _ _) (Gen.segFree _ (by decide)))

end BiasExponent

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
