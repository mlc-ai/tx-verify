-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.SafeStatic
import Kernels.InklingRelDecode.Proof.Prologue.ShapeMbar
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Init
import Lemmas.Flow.TmplOkMore
import Lemmas.Flow.Step.ShapeClasses
import Lemmas.Flow.TmaTmpl
import Lemmas.Flow.TmplOkSync
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Shuffle
import Kernels.InklingRelDecode.Flow.Code.Part004
import Kernels.InklingRelDecode.Flow.Code.Part005

@[expose] public section

/-! # The prologue's barrier initialisations and arrivals are not undefined behaviour

The address register of a barrier holds the aligned shared address of its object
(`Prologue.object_reg`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow Control

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The control table of a value state is that of its control state. -/
theorem atD_ctl {d : Data.D} {t : TState} (h : (Data.code Q L g w).AtD d t) :
    (Control.code Q L g w).AtD d.c t :=
  by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨a1, a2, a3, a4, ((holds_append _ _ _).mp a5).1⟩

/-- **An `mbarrier.init` of the prologue is not undefined behaviour.** -/
theorem safe_init {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {i : Fin 12} (hs : d.c.site = .init i)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (init_fetch i))
  have keys : ∀ i : Fin 12, 613 + i.val ∈ ctlLive (Site.init i).pc := by decide +kernel
  obtain ⟨reg, bound, aligned⟩ := object_reg hp (atD_ctl hat) i (hs ▸ keys i)
  have hi : tmaTmpl L g t (.mbarInit (613 + i.val) 0 (.imm 1)) =
      .mbInit ⟨.shared, g / L.block, L.sharedBase + MbarRow.initOffset i⟩ 1 (next t) :=
    tma_mbarInit (L := L) (g := g) (t := t) reg bound aligned (n := 1) (by decide) (by decide)
  simp only [eventTmpl, hi, widenMbarScope]
  split_ifs <;> simp

/-- **An `mbarrier.arrive.expect_tx` of the prologue is not undefined behaviour.** -/
theorem safe_arr {m} (hp : Pre Q L m) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {b : Fin 3} (hs : d.c.site = .arr b)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have fetch : kernel.code[(Site.arr b).pc]? = some ⟨some (177, false),
      .mbarArrive (613 + 2 * b.val) 0 (.imm 65536) (.imm 1) false true .cta none⟩ := by
    fin_cases b
    · exact Flow.code_193
    · exact Flow.code_237
    · exact Flow.code_279
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans fetch)
  have keys : ∀ b : Fin 3, 613 + 2 * b.val ∈ ctlLive (Site.arr b).pc := by decide +kernel
  obtain ⟨reg, bound, aligned⟩ := object_reg hp (atD_ctl hat) (readyIndex b) (hs ▸ keys b)
  have hl : mbarLoc L g t (613 + 2 * b.val) 0 = .ok ⟨.shared, g / L.block, _⟩ :=
    mbarLoc_b32_ok reg bound aligned
  exact arrive_loc_ok (by simpa using hl) rfl rfl f

/-- **A broadcast of the warp index is not undefined behaviour.** -/
theorem safe_psh (hb : L.block % 32 = 0) {d : Data.D} {t : TState} {ins : Instr}
    (hat : (Data.code Q L g w).AtD d t) {b : Fin 3} (hs : d.c.site = .psh b)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have keys : ∀ b : Fin 3, 464 ∈ ctlLive (Site.psh b).pc := by decide +kernel
  have reg := reg_ctl hat (r := 464) (hs ▸ keys b)
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans (psh_fetch b))
  have hv : valueOf Q L g w d.c 464 = .bits 32 (BitVec.ofNat 64 (g % L.block / 32)) := rfl
  rw [hv] at reg
  exact shfl_imm_ok (p := none) (Or.inr rfl) hb reg f

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
