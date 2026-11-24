-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Common.LdWait
import Lemmas.Flow.LoadFrameU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Proof PTX.Flow
noncomputable section

private def row (c : Fin 4) : Bool :=
  let pc := (Site.sld .plain c).pc
  Assumptions.tcLdDataflowSites.contains pc &&
    match kernel.code[pc]? with
    | some ⟨none,.tcLd ds _ .s32x32b none⟩ =>
      (ctlLive (pc+1)).all (fun r => !ds.contains r && (ctlLive pc).contains r)
    | _ => false

set_option maxRecDepth 100000 in
private theorem rows : ∀ c, row c = true := by decide +kernel

/-- Each plain score load accepts arbitrary lane payloads and reaches the implicit wait. -/
theorem stepAt_sld_plainU {p L g} (c : Fin 4) (v : V) :
    (code p L g).StepAtU ⟨.sld .plain c,v,0,[]⟩ := by
  have h := rows c
  simp only [row,Bool.and_eq_true] at h
  obtain ⟨hw,hd⟩ := h
  split at hd
  · rename_i ds ta hc
    refine ⟨fun _ => ⟨_,hc,rfl,trivial⟩, ?_⟩
    intro t e u ins hat _ hlookup hf
    obtain rfl := Option.some.inj (hlookup.symm.trans hc)
    obtain ⟨hpc,hsub,hacc,hfault,hregs⟩ := hat
    obtain ⟨a,vs,rfl,rfl⟩ := fires_tcLd_loadU (fun s h => by cases h)
      (hpc ▸ (Assumptions.tcLdWait_iff _).trans hw) hsub hf
    obtain ⟨_,_,hacc',hfault'⟩ := setRegs_skel (PTX.next t) ds vs
    refine .inl (.inr ⟨⟨.sldw c,v,1,[]⟩,_,rfl,.refl,.inl ⟨?_,.inr ⟨rfl,rfl⟩⟩⟩)
    exact ⟨hpc,rfl,hacc'.trans hacc,hfault'.trans hfault,holds_after_tcLd hregs hd⟩
  · cases hd

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
