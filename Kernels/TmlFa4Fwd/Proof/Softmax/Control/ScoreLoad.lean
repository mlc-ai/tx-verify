-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Proof.Common.LdWait
import Lemmas.Flow.LoadFrameU

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow
noncomputable section

def scoreNext (r : Rd) (c : Fin 4) := if c.val = 3 then afterLoads r else Site.sld r (c+1)

private def row (b : Bool) (c : Fin 4) : Bool :=
  let pc := (Site.sld (rdOf b) c).pc
  !Assumptions.tcLdDataflowSites.contains pc &&
    match kernel.code[pc]? with
    | some ⟨none,.tcLd ds _ .s32x32b none⟩ => (ctlLive pc).all fun r => !ds.contains r
    | _ => false

set_option maxRecDepth 100000 in
private theorem rows : ∀ b c, row b c = true := by decide +kernel

abbrev ScoreSpan (p : Params) (L : Launch) (g : Nat) (r : Rd) (c : Fin 4) (v : V) :=
  SegU kernel Assumptions.all L g ((Site.sld r c).pc+1)
    (Softmax.facts p L g (Softmax.D.mk' (.sld r c) v.scheduler)) (scoreNext r c).pc
    (Softmax.facts p L g (Softmax.D.mk' (scoreNext r c) v.scheduler))

theorem stepAt_score_of_span {p L g} (b : Bool) (c : Fin 4) (v : V)
    (hs : ScoreSpan p L g (rdOf b) c v) : (code p L g).StepAtU ⟨.sld (rdOf b) c,v,0,[]⟩ := by
  let dst : D := ⟨scoreNext (rdOf b) c, v, 0, []⟩
  have h := rows b c
  simp only [row,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨hw,hdec⟩ := h
  split at hdec
  · rename_i ds ta hc
    refine ⟨fun _ => ⟨_,hc,rfl,trivial⟩, ?_⟩
    intro t e u ins hat _ hlookup hf
    obtain rfl := Option.some.inj (hlookup.symm.trans hc)
    obtain ⟨hpc,hsub,hacc,hfault,hr⟩ := hat
    obtain ⟨a,vs,_,rfl,rfl⟩ := fires_tcLd (fun s h => by cases h) hf
      (hpc ▸ (Assumptions.tcLdWait_iff _).trans hw)
    obtain ⟨hp',hs',ha',hf'⟩ := setRegs_skel (PTX.next t) ds vs
    obtain ⟨u,ht,hu⟩ := Code.landsU (C := code p L g) (d := dst)
      (u := setRegs (PTX.next t) ds vs) (by
        refine ⟨hp'.trans (congrArg (·+1) hpc),hs'.trans hsub,ha'.trans hacc,hf'.trans hfault,?_⟩
        apply holds_setRegs_frame (t := PTX.next t) hr
        intro r hmem
        exact ⟨by simpa using List.all_eq_true.mp hdec r hmem, hmem, rfl⟩)
      hs (by unfold dst scoreNext; cases b <;> split <;> exact .inl ⟨rfl,rfl,rfl⟩) rfl rfl
    exact .inl (.inr ⟨dst,u,by cases b <;> rfl,ht,hu⟩)
  · cases hdec

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
