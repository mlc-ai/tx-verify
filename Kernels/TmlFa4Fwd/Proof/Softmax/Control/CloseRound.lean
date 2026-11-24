-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Epilogue.Base
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegJump
import Lemmas.Flow.WaitU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow

theorem closeRound {p L g} (r : Rd) (v : V) (dst : D)
    {reg base : Nat} {off : Int} {par : Opnd} {entry : Nat}
    (hc : kernel.code[(Site.pwend r).pc]? = some ⟨none,.mbarWait reg base off par true .cta⟩)
    (hb : kernel.code[(Site.pwend r).pc+1]? = some ⟨some (reg,false),.bra entry true⟩)
    (hj : kernel.code[(Site.pwend r).pc+2]? = some ⟨none,.bra (Site.pwend r).pc true⟩)
    (hfree : Assumption.SegFreePc Assumptions.all ((Site.pwend r).pc+1))
    (jfree : Assumption.SegFreePc Assumptions.all ((Site.pwend r).pc+2))
    (hr : reg ∉ ctlLive (Site.pwend r).pc)
    (hn : ∀ m q s, succ p L g ⟨.pwend r,v,0,[]⟩ ⟨(Site.pwend r).pc,.wait m q true true s⟩ =
        some (some dst))
    (hk : dst.k = 0) (ha : dst.acc = []) (hi : Inv dst)
    (tail : SegU kernel Assumptions.all L g entry (Softmax.facts p L g ⟨.pwend r,v.scheduler,0,[]⟩)
      dst.site.pc (Softmax.facts p L g dst.scheduler)) :
    (code p L g).StepAtU ⟨.pwend r,v,0,[]⟩ := by
  refine Code.waitU (dst := fun ok => if ok then dst else ⟨.pwend r,v,0,[]⟩) hc ?_ ?_
    rfl rfl (fun ok => by cases ok <;> first | rfl | exact congrArg Fin.val hk)
    (fun ok => by cases ok <;> first | rfl | exact ha) ?_ ?_
  · change reg ∉ (factsFrom (ctlLive (Site.pwend r).pc) _).map Prod.fst
    simp only [factsFrom,List.map_map,Function.comp_def]
    exact (List.map_id _ : (ctlLive (Site.pwend r).pc).map (fun x => x) = _).symm ▸ hr
  · intro m q ok s
    cases ok
    · rfl
    · exact hn m q s
  · intro ok
    cases ok
    · exact .inl ⟨rfl,rfl,rfl⟩
    · exact hi
  · intro ok
    refine (SegU.branch ok hb (fun t => braFree t.pc _ _ t rfl) hfree).comp ?_
    cases ok
    · exact SegU.of_seg (seg_jmp hj (braFree _ _ _) jfree)
    · exact tail

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
