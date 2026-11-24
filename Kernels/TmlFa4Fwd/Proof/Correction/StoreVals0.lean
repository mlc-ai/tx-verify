-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.StoreVals
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part133
import Kernels.TmlFa4Fwd.Flow.Code.Part134
import Kernels.TmlFa4Fwd.Flow.Code.Part135
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part138
import Kernels.TmlFa4Fwd.Flow.Code.Part139
import Kernels.TmlFa4Fwd.Flow.Code.Part140
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Proof.Correction.SafeSt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The bytes of the final stores of stage 0 (`fst_val0`) -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option maxHeartbeats 4000000 in
private theorem fst_0_0 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 0 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 0 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 0 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 0 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_1 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 1 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 1 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 1 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 1 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_2 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 2 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 2 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 2 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 2 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_3 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 3 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 3 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 3 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 3 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_4 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 4 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 4 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 4 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 4 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_5 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 5 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 5 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 5 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 5 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_6 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 6 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 6 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 6 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 6 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_7 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 7 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 7 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 7 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 7 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_8 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 8 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 8 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 8 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 8 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_9 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 9 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 9 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 9 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 9 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_10 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 10 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 10 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 10 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 10 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_11 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 11 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 11 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 11 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 11 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_12 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 12 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 12 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 12 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 12 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_13 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 13 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 13 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 13 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 13 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_14 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 14 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 14 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 14 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 14 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

set_option maxHeartbeats 4000000 in
private theorem fst_0_15 {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 15 hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 15 hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 15 hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  have hreg : ∀ r ∈ Flow.live (Site.fst 0 15 hh).pc, t.regs r = some (valueOf p L g _ r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub := h.2.1
  simp only at hsub
  fin_cases hh <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    fin_cases k <;>
      exact store32_val rfl rfl rfl rfl rfl rfl (by rw [hsub]; rfl) (hreg _ (by lit_mem)) rfl hf hk

/-- **The bytes of a final store of stage 0.** -/
theorem fst_val0 {j : Fin 16} {v : V} {k : Fin 4} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {hh : Fin 2} (h : (code p L g).AtD ⟨.fst 0 j hh, v, k⟩ t)
    (hc : kernel.code[(Site.fst 0 j hh).pc]? = some ins)
    (hf : Fires (Site.fst 0 j hh).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {acc : Acc} {bs : List Byte} (hk : e.kind = .wr acc bs) :
    bs = (fv (v.ys (4 * hh.val + k.val) * fRecip (rsOf v 0))).toBytes := by
  fin_cases j
  · exact fst_0_0 h hc hf hk
  · exact fst_0_1 h hc hf hk
  · exact fst_0_2 h hc hf hk
  · exact fst_0_3 h hc hf hk
  · exact fst_0_4 h hc hf hk
  · exact fst_0_5 h hc hf hk
  · exact fst_0_6 h hc hf hk
  · exact fst_0_7 h hc hf hk
  · exact fst_0_8 h hc hf hk
  · exact fst_0_9 h hc hf hk
  · exact fst_0_10 h hc hf hk
  · exact fst_0_11 h hc hf hk
  · exact fst_0_12 h hc hf hk
  · exact fst_0_13 h hc hf hk
  · exact fst_0_14 h hc hf hk
  · exact fst_0_15 h hc hf hk

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
