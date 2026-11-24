-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepChunk
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepLoad

@[expose] public section

/-! # The implicit waits of the correction warps' loads

At a load's sub-step 1 (`rldW`, `fldW`) the thread performs the implicit `tcgen05.wait::ld`
(ASM-TCLD-DATAFLOW) and continues at the next instruction's first sub-step with its registers
unchanged; from there the chunk's products reach the chunk's store (`rldW_step`,
`fldW_step`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The state after the implicit wait of a load: one instruction past it, at its first
sub-step, with the facts of the wait's state. -/
theorem waitLd_at {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ds : List Nat}
    {ta : Nat} (hw : asms.any (·.tcLdWait d.site.pc) = true) (hsub : d.site.sub = 1)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hf : Fires d.site.pc (eventTmpl asms L g t (.tcLd ds ta)) e (some u)) :
    (e.pc = d.site.pc ∧ e.kind = .tc .waitLd) ∧ At u (d.site.pc + 1) (facts L g d) := by
  obtain ⟨rfl, rfl⟩ := fires_tcLd_wait (h.1 ▸ hw) (by rw [h.2.1, hsub]; decide) hf
  exact ⟨⟨rfl, rfl⟩, by simp only [PTX.next, h.1], rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **The implicit wait of a rescale load**, then the chunk's products and store. -/
theorem step_rldW {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (j : Fin 8)
    (hs : d.site = .rldW st j) (hi : Inv L g d)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (code_rld st j))
  have hw : asms.any (·.tcLdWait d.site.pc) = true := hs ▸ tcLdWait_rld st j
  obtain ⟨hev, hu⟩ := waitLd_at hw (by rw [hs]; rfl) h hf
  refine ⟨⟨hev.1, ?_⟩, rldW_step hpre st j hs hi (hs ▸ hu)⟩
  rw [hs]
  exact hev.2

/-- **The implicit wait of a final load**, then the chunk's products and first store. -/
theorem step_fldW {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (j : Fin 8)
    (hs : d.site = .fldW st j) (hi : Inv L g d)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (code_fld st j))
  have hw : asms.any (·.tcLdWait d.site.pc) = true := hs ▸ tcLdWait_fld st j
  obtain ⟨hev, hu⟩ := waitLd_at hw (by rw [hs]; rfl) h hf
  refine ⟨⟨hev.1, ?_⟩, fldW_step hpre st j hs hi (hs ▸ hu)⟩
  rw [hs]
  exact hev.2

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
