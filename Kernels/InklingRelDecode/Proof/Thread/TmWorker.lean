-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase

@[expose] public section

/-! # The worker's sites are not undefined behaviour -/

namespace PTX.Kernels.InklingRelDecode.Proof.Worker
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Loader (Pro)
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- **No worker site has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr}
    (hH : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  obtain ⟨s, P⟩ := d
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedSym rfl rfl rfl (by norm_num; omega), by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (warpOf L g)) (.inr rfl) hb
      (holds_mem hH (tbl_mem (by live_dec) (by simp [valueOf, own, List.lookup, b32]))) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_4)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_27)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_203)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedReg (x := Loader.addW (Loader.baseW L) (BitVec.ofNat 64 (warpOf L g)))
      rfl rfl (holds_mem hH (tbl_mem (by live_dec)
      (by simp [valueOf, roleAddr]))), Nat.mod_one _⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_2)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_7)
    exact plainOk_tmpl hb (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_37)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_32)
    exact barSync_imm_ok (id := 1) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_33)
    exact barSync_imm_ok (id := 1) (by decide) f

end
end PTX.Kernels.InklingRelDecode.Proof.Worker
