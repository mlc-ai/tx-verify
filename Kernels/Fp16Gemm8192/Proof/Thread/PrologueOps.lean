-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueDispatch

@[expose] public section

/-! # The operations of the prologue's instructions

Facts about which operations the prologue performs, shared by the roles' invariants. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Prologue

/-- No prologue instruction is a poll. -/
theorem code_notPoll (s : Site) {ins : Instr} (hc : kernel.code[s.pc]? = some ins) :
    ∀ p b off par a sc, ins.op ≠ .mbarWait p b off par a sc := by
  intro p b off par a sc hop
  cases s with
  | shfl => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0); cases hop
  | elect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0); cases hop
  | init i =>
    obtain ⟨ins', hc', hadv⟩ := code_init i
    rw [hc] at hc'
    cases hc'
    rw [hop] at hadv
    exact hadv
  | alloc => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases hop
  | allocWrite => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0); cases hop
  | warpBar => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0); cases hop
  | fence => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0); cases hop
  | fenceInit => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0); cases hop
  | arrive => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0); cases hop
  | wait => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0); cases hop
  | setMaxReg => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0); cases hop
  | roleElect => obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_1); cases hop

end Prologue

end
end PTX.Kernels.Fp16Gemm8192.Proof
