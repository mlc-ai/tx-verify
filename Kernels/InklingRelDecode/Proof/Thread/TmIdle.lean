-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmWorker

@[expose] public section

/-! # The idle role's and the exit's sites -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker.Idle
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- **No idle site has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨s, P⟩ := d
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_2)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_25)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_26)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_3)
    exact plainOk_tmpl hb (by decide) f

end
end PTX.Kernels.InklingRelDecode.Proof.Worker.Idle
