-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.TmBase
public import Kernels.InklingRelDecode.Proof.Thread.DStartAll

@[expose] public section

/-! # The common start's sites are not undefined behaviour -/

namespace PTX.Kernels.InklingRelDecode.Proof.DStart
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Tm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

/-- The shared base register, where it is live, holds the base word. -/
theorem base_reg {pc : Nat} {tm : Value} (hl : 534 ∈ Flow.live pc)
    (hH : Holds t.regs (factsAt L g Q tm pc)) (hsb : L.sharedBase < 2 ^ 32) :
    t.regs 534 = some (b32 L.sharedBase) := by
  have h1 : t.regs 534 = some (.bits 32 (Loader.baseW L)) :=
    holds_reg hH hl (by simp [valueOf, table, lookupLit])
  rw [h1, show Loader.baseW L = BitVec.ofNat 64 L.sharedBase from baseW_eq (by omega)]
  rfl

/-- **No site of the common start has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre Q L mem0) {d : D} {ins : Instr}
    (hH : Holds t.regs (facts L g Q d)) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsa := hpre.sharedAlignment
  have hsr := hpre.sharedRange
  have hsb : L.sharedBase < 2 ^ 32 := by omega
  obtain ⟨s, tm⟩ := d
  cases s
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact tcAlloc_imm_ok hb (base_reg (by live_dec) hH hsb) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
    exact tcAlloc_imm_ok hb (base_reg (by live_dec) hH hsb) (by omega) (by omega) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
    refine loadAccess_ok rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) ?_ f
    exact ⟨_, accessLoc_sharedSym (off := 0) rfl rfl rfl (by omega),
      by simp [DType.width]; omega⟩
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    exact barSync_imm_ok (id := 0) (by decide) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
    exact plainOk_tmpl hb rfl f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
    exact shfl_imm_ok (p := none) (x := BitVec.ofNat 64 (warpOf L g)) (.inr rfl) hb
      (holds_reg hH (by live_dec) (by simp [valueOf, table, lookupLit, b32])) f
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
    exact plainOk_tmpl hb (by decide) f

end
end PTX.Kernels.InklingRelDecode.Proof.DStart
