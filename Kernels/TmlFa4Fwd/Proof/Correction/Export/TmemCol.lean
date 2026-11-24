-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemAddr
import Kernels.TmlFa4Fwd.Flow.Code.Part125
import Kernels.TmlFa4Fwd.Flow.Code.Part126
import Kernels.TmlFa4Fwd.Flow.Code.Part127
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part129
import Kernels.TmlFa4Fwd.Flow.Code.Part130
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

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Shape

@[expose] public section

/-! # The columns of the correction warps' Tensor Memory accesses

Chunk `c` of a rescale round of stage `st` loads and stores the 16 columns `256 + 128 st + 16 c …`
(`rld_col`, `rst_col`); chunk `j` of the final stage loads the 8 columns `256 + 128 st + 8 j …`
(`fld_col`), all with the shape `.32x32b`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- One Tensor Memory load site: its column. -/
macro "corr_ld_col" : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := ld_at hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact truncBits_lt _ | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_, hl⟩
  simp (disch := norm_num) only [fStage, addi_low, tm0_low, tm1_low]
  try norm_num))

set_option hygiene false in
/-- One Tensor Memory store site: its column. -/
macro "corr_st_col" : tactic => `(tactic| (
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  obtain ⟨rfl, rfl, hl⟩ := st_at hat hc
    (by rw [← b32_toNat]; exact Flow.mem_factsFrom (by lit_mem))
    (by first | exact truncBits_lt _ | exact ori_lt _ _) hf hk
  refine ⟨rfl, ?_, hl⟩
  simp (disch := norm_num) only [fStage, addi_low, tm0_low, tm1_low]
  try norm_num))

set_option maxHeartbeats 40000000 in
/-- **A rescale load's columns.** -/
theorem rld_col {st : Fin 2} {c : Fin 8} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rld st c, v, k⟩ t)
    (hc : kernel.code[(Site.rld st c).pc]? = some ins)
    (hf : Fires (Site.rld st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_ld_col

set_option maxHeartbeats 40000000 in
/-- **A rescale store's columns.** -/
theorem rst_col {st : Fin 2} {c : Fin 8} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.rst st c, v, k⟩ t)
    (hc : kernel.code[(Site.rst st c).pc]? = some ins)
    (hf : Fires (Site.rst st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    sh = .s32x32b ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_st_col

set_option maxHeartbeats 40000000 in
/-- **A final load's columns.** -/
theorem fld_col {st : Fin 2} {c : Fin 16} {v : Control.V} {k : Fin 4} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (Control.code p L g).AtD ⟨.fld st c, v, k⟩ t)
    (hc : kernel.code[(Site.fld st c).pc]? = some ins)
    (hf : Fires (Site.fld st c).pc (eventTmpl Assumptions.all L g t ins.op) e o)
    {a : Nat} {vals : List Value} {sh : TcShape} (hk : e.kind = .tc (.ld a vals sh)) :
    sh = .s32x32b ∧ a % 65536 = 256 + 128 * st.val + 8 * c.val ∧ vals.length = 8 := by
  fin_cases st <;> fin_cases c <;> dsimp only [Fin.reduceFinMk, Fin.isValue] at hat hc hf ⊢ <;>
    corr_ld_col

end PTX.Kernels.TmlFa4Fwd.Proof.Correction
