-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaEv

@[expose] public section

/-! # The QK MMAs' events

Each MMA site of a QK block `b` fires the MMA `MmaEv` names: the instruction at the site
(read off the decoded code) with the site's register facts (`Mma.asmVals`, `Mma.qVals`) in
`qk_ev`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A QK site's MMA.** -/
theorem qk_site_ev (hpre : Pre P L mem0) (hg : g < L.threads) {b j : Fin 8} (hb : isPv b = false)
    {i tt : Nat} {base : Value} {pro : Nat → Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : Holds t.regs (facts L g ⟨.mma b j, i, tt, base, pro⟩))
    (hc : kernel.code[(Site.mma b j).pc]? = some ins)
    (hf : Fires (Site.mma b j).pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tc (.mma (mmaCol b) (mmaSpec L g ⟨.mma b j, i, tt, base, pro⟩ b j)
      (mmaAcc ⟨.mma b j, i, tt, base, pro⟩ b j) (List.replicate 8 0)) := by
  fin_cases b <;> simp only [isPv, Fin.isValue, Fin.reduceFinMk] at hb <;> try contradiction
  · fin_cases j <;> code_at hc <;> subst hc
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨0, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5343) (by table_decide) (by mma_val))
        (reg_of h (r := 5363) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨1, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5344) (by table_decide) (by mma_val))
        (reg_of h (r := 5364) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨2, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5345) (by table_decide) (by mma_val))
        (reg_of h (r := 5365) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨3, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5346) (by table_decide) (by mma_val))
        (reg_of h (r := 5366) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨4, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5347) (by table_decide) (by mma_val))
        (reg_of h (r := 5367) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨5, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5348) (by table_decide) (by mma_val))
        (reg_of h (r := 5368) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨6, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5349) (by table_decide) (by mma_val))
        (reg_of h (r := 5369) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i 0) ⟨7, by decide⟩
        (reg_of h (r := 5357) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5350) (by table_decide) (by mma_val))
        (reg_of h (r := 5370) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨0, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5343) (by table_decide) (by mma_val))
        (reg_of h (r := 5380) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨1, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5344) (by table_decide) (by mma_val))
        (reg_of h (r := 5381) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨2, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5345) (by table_decide) (by mma_val))
        (reg_of h (r := 5382) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨3, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5346) (by table_decide) (by mma_val))
        (reg_of h (r := 5383) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨4, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5347) (by table_decide) (by mma_val))
        (reg_of h (r := 5384) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨5, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5348) (by table_decide) (by mma_val))
        (reg_of h (r := 5385) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨6, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5349) (by table_decide) (by mma_val))
        (reg_of h (r := 5386) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i 0) ⟨7, by decide⟩
        (reg_of h (r := 5374) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5350) (by table_decide) (by mma_val))
        (reg_of h (r := 5387) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5343) (by table_decide) (by mma_val))
        (reg_of h (r := 5409) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5344) (by table_decide) (by mma_val))
        (reg_of h (r := 5410) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5345) (by table_decide) (by mma_val))
        (reg_of h (r := 5411) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5346) (by table_decide) (by mma_val))
        (reg_of h (r := 5412) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5347) (by table_decide) (by mma_val))
        (reg_of h (r := 5413) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5348) (by table_decide) (by mma_val))
        (reg_of h (r := 5414) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5349) (by table_decide) (by mma_val))
        (reg_of h (r := 5415) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := true) (kvSlot_lt L i (2 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5403) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5350) (by table_decide) (by mma_val))
        (reg_of h (r := 5416) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5343) (by table_decide) (by mma_val))
        (reg_of h (r := 5436) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5344) (by table_decide) (by mma_val))
        (reg_of h (r := 5437) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5345) (by table_decide) (by mma_val))
        (reg_of h (r := 5438) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5346) (by table_decide) (by mma_val))
        (reg_of h (r := 5439) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5347) (by table_decide) (by mma_val))
        (reg_of h (r := 5440) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5348) (by table_decide) (by mma_val))
        (reg_of h (r := 5441) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5349) (by table_decide) (by mma_val))
        (reg_of h (r := 5442) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf
    · exact qk_ev hpre hg (low := false) (kvSlot_lt L i (2 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5430) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5350) (by table_decide) (by mma_val))
        (reg_of h (r := 5443) (by table_decide) (by mma_val))
        (reg_of h (by table_decide) (by mma_val)) rfl hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
