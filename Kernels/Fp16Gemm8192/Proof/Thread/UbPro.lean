-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.UbLoader

@[expose] public section

/-! # The prologue's sites are not undefined behaviour

At every site of the prologue, the instruction's event is not undefined behaviour
(`Prologue.tmpl_ok`): the shuffle and the elections use the full mask, the initializations name
aligned barriers of the CTA with counts in range, the allocation takes the 512 columns into the
CTA's base word, and the remaining instructions are fences, cluster operations and the register
request. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

namespace Prologue

set_option maxHeartbeats 8000000 in
/-- **No site of the prologue has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre P L mem0) {d : D} {ins : Instr}
    (hat : (code L g).AtD (.inl d) t) (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl Prod L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hF := hat.2.2.2.2
  obtain ⟨site, w⟩ := d
  cases site with
  | shfl =>
    code_at hc
    subst hc
    have hr9 : t.regs 55 = some (b32 (warpOf L g)) :=
      (holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by pro_values))
    simp only [eventTmpl, warpTmpl_shfl_idx, shflTmpl, readBits, readValue, readReg, hr9, b32,
      Value.bytes, hb, pure, Except.pure]
    rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 by decide]
    simp
  | elect | roleElect =>
    code_at hc
    subst hc
    exact elect_ok ((holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by pro_values))) f
  | warpBar =>
    code_at hc
    subst hc
    exact warpBar_ok f
  | init i =>
    fin_cases i
    all_goals
      code_at hc
      subst hc
      exact mbarInit_ok ((holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by pro_values; rfl))) (by omega) (by omega)
        ((holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans
          (congrArg some (by pro_values; rfl))) (by decide) (by decide) f
  | alloc | allocWrite =>
    code_at hc
    subst hc
    exact tcAlloc_ok hb ((holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by pro_values; rfl))) (by omega) (by omega)
      ((holds_mem hF (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by pro_values))) f
  | fence | fenceInit | arrive | wait | setMaxReg =>
    code_at hc
    subst hc
    exact plainOk_tmpl hb rfl f

end Prologue

end

end PTX.Kernels.Fp16Gemm8192.Proof
