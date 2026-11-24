-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.LoadFrameU
import Lemmas.Flow.Vector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
noncomputable section

def biasNext (b : Bool) (c : Fin 16) : Site :=
  if c.val = 15 then .fence b else .bld b (c+1)

private def row (b : Bool) (c : Fin 16) : Bool :=
  let s := (Site.bld b c).pc
  let dst := (biasNext b c).pc
  let regs := ctlLive dst
  s+1 ≤ dst && dst ≤ 9206 &&
    Havoc.check hooks regs (s+1) dst ((kernel.code.drop (s+1)).take (dst-(s+1))) &&
    match kernel.code[s]? with
    | some ⟨none,.mem a⟩ =>
      a.kind == .load && !a.nc && a.ext == .same && a.regs.length == 4 &&
        !(Op.mem a).isLocal && regs.all (fun r => !(a.regs.contains r) && (ctlLive s).contains r)
    | _ => false

set_option maxRecDepth 100000 in
private theorem rows : ∀ (b : Bool) (c : Fin 16), row b c = true := by decide +kernel

private theorem keys {rg : List Nat} {v : Nat → Value} :
    (factsFrom rg v).map Prod.fst = rg := by
  simp only [factsFrom,List.map_map,Function.comp_def]
  exact List.map_id _

theorem stepAt_bld_lastU {p L g} (b : Bool) (c : Fin 16) (v : V) (acc : List Value) :
    (code p L g).StepAtU ⟨.bld b c,v,3,acc⟩ := by
  let dst : D := ⟨biasNext b c,v,0,[]⟩
  have facts_dst : (code p L g).facts dst =
      factsFrom (ctlLive dst.site.pc) (valueOf p L g (⟨.bld b c,v,3,acc⟩ : D).scheduler) := by
    unfold dst biasNext
    split <;> cases b <;> rfl
  have h := rows b c
  simp only [row,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨⟨hle,hbound⟩,hspan⟩,hdec⟩ := h
  split at hdec
  · rename_i a hc
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hdec
    obtain ⟨⟨⟨⟨⟨hk,hn⟩,he⟩,h4⟩,hl⟩,hr⟩ := hdec
    refine ⟨fun _ => ⟨_,hc,hl,trivial⟩, ?_⟩
    intro t e u ins hat _ hlookup hf
    obtain rfl := Option.some.inj (hlookup.symm.trans hc)
    obtain ⟨addr,bs,rfl,rfl⟩ := fires_load hk hn hf he
    have hnext : succ p L g ⟨.bld b c,v,3,acc⟩ ⟨(Site.bld b c).pc,.rd addr bs⟩ =
        some (some dst) := rfl
    suffices h : ∃ s, Relation.ReflTransGen (Tau kernel Assumptions.all L g)
        (afterLoad t a.regs bs) s ∧ (code p L g).GoodU (some dst) s by
      obtain ⟨s,hs⟩ := h
      exact .inl (.inr ⟨dst,s,hnext,hs⟩)
    cases hv : rebuild 3 bs with
    | error f =>
      exact Code.goodU_of_dead (C := code p L g) dst
        (Machine.dead_of_fault (afterLoad_fault hv))
    | ok w =>
      obtain ⟨hpc,hsub,_,hfault,hregs⟩ := hat
      change t.sub = 3 at hsub
      rw [afterLoad_last hv (by omega)]
      obtain ⟨_,_,_,hkeep⟩ := setRegs_skel t a.regs (t.acc ++ [w])
      apply Code.landsU (C := code p L g) (d := dst) (a := (Site.bld b c).pc + 1)
        (F := (code p L g).facts dst)
      · refine ⟨congrArg (·+1) hpc,rfl,rfl,hkeep.trans hfault,?_⟩
        rw [facts_dst]
        apply holds_setRegs_frame hregs
        intro r hmem
        have h := List.all_eq_true.mp hr r hmem
        simp only [Bool.and_eq_true,Bool.not_eq_true',List.contains_iff_mem] at h
        exact ⟨by simpa using h.1, h.2, rfl⟩
      · apply SegU.of_havoc rules_frame hooks_ok hle
          (hbound.trans (show 9206 ≤ kernel.code.length by decide +kernel)) _ (fun _ h => h)
        rw [facts_dst, keys]
        exact hspan
      · change Inv dst
        unfold dst biasNext
        split
        · exact .inl ⟨rfl,rfl,rfl⟩
        · rfl
      · rfl
      · rfl
  · cases hdec

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
