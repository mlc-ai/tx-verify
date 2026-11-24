-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaEv

@[expose] public section

/-! # The PV MMAs' events

Each MMA site of a PV block `b` fires the MMA `MmaEv` names: the instruction at the site
(read off the decoded code) with the site's register facts (`Mma.asmVals`, `Mma.qVals`) in
`pv_ev`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **A PV site's MMA.** -/
theorem pv_site_ev (hpre : Pre P L mem0) (hg : g < L.threads) {b j : Fin 8} (hb : isPv b = true)
    {i tt : Nat} {base : Value} {pro : Nat → Value} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : Holds t.regs (facts L g ⟨.mma b j, i, tt, base, pro⟩))
    (hc : kernel.code[(Site.mma b j).pc]? = some ins)
    (hf : Fires (Site.mma b j).pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tc (.mma (mmaCol b) (mmaSpec L g ⟨.mma b j, i, tt, base, pro⟩ b j)
      (mmaAcc ⟨.mma b j, i, tt, base, pro⟩ b j) (List.replicate 8 0)) := by
  fin_cases b <;> simp only [isPv, Fin.isValue, Fin.reduceFinMk] at hb <;> try contradiction
  · fin_cases j <;> code_at hc <;> subst hc
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 0) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) (acc := decide (tt ≠ 0))
        (by simp [mmaEnable, readReg, reg_of h (r := 5391) (v := .pred (decide (tt ≠ 0)))
          (by table_decide) (by mma_val)]; rfl) hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 8) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 16) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 24) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 32) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 40) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 48) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5393) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5394) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 56) (by decide))
        (reg_of h (r := 5398) (by table_decide) (by mma_val))
        (reg_of h (r := 5392) (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 0) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) (acc := decide (tt ≠ 0))
        (by simp [mmaEnable, readReg, reg_of h (r := 5419) (v := .pred (decide (tt ≠ 0)))
          (by table_decide) (by mma_val)]; rfl) hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 8) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 16) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 24) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 32) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 40) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 48) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5421) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5422) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 56) (by decide))
        (reg_of h (r := 5426) (by table_decide) (by mma_val))
        (reg_of h (r := 5420) (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 0) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) (acc := decide (tt ≠ 0))
        (by simp [mmaEnable, readReg, reg_of h (r := 5447) (v := .pred (decide (tt ≠ 0)))
          (by table_decide) (by mma_val)]; rfl) hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 8) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 16) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 24) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 32) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 40) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 48) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5449) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5450) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 64) (off := 56) (by decide))
        (reg_of h (r := 5454) (by table_decide) (by mma_val))
        (reg_of h (r := 5448) (by table_decide) (by mma_val)) rfl hf
  · fin_cases j <;> code_at hc <;> subst hc
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨0, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 0) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) (acc := decide (tt ≠ 0))
        (by simp [mmaEnable, readReg, reg_of h (r := 5458) (v := .pred (decide (tt ≠ 0)))
          (by table_decide) (by mma_val)]; rfl) hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨1, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 8) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨2, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 16) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨3, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 24) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨4, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 32) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨5, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 40) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨6, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 48) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf
    · exact pv_ev hpre hg (kvSlot_lt L i (1 + 2 * tt)) ⟨7, by decide⟩
        (reg_of h (r := 5460) (by table_decide) (by mma_val)) (by decide)
        (reg_of h (r := 5461) (by table_decide) (by mma_val)) (by decide)
        (tmemOffset_of (a := 192) (off := 56) (by decide))
        (reg_of h (r := 5465) (by table_decide) (by mma_val))
        (reg_of h (r := 5459) (by table_decide) (by mma_val)) rfl hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
