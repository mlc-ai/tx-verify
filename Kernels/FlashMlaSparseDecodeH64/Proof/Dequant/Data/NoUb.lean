-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.NoUbSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeBase
import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
import Lemmas.Flow.UbStop
import Lemmas.Flow.StoreSrc
import Lemmas.Flow.Step.RdNoUb
import Lemmas.Flow.Step.SiteShape
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part041
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part042
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part043
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part044
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part045
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part046
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part047
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part048
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part049
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part050
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part051
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part052
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part053
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part054
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part055
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056

@[expose] public section

/-! # The chunk stores fire no undefined behaviour, and the data machine's states with them

`noUbAt_store`: a chunk store at the aligned address of its lane (`store_loc`) of the payload
register, which holds a 16-byte value, is no fault. `dq_nonub`: the event fired from any state of
the data machine is no fault, the control sites by `Dequant/NoUbSite.lean` on the erased
concrete state, the stores by the data fact of their chunk. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

/-- The control state's concrete state of a data state's. -/
theorem ctl_atD {d : D} {t : TState} (hat : (code P L g w).AtD d t) :
    (Control.code P L g w).AtD d.c t :=
  by
  obtain ⟨hpc, hsub, hacc, hf, hF⟩ := hat
  exact ⟨hpc, hsub, hacc, hf, ((holds_append _ _ _).mp hF).1⟩

/-- **The event fired from a state of the data machine is no fault.** -/
theorem dq_nonub (hp : Pre P L m) (d : D) (hl : LenOk P d.c) {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hat : (code P L g w).AtD d t) (hi : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∀ f, e.kind ≠ .ub f := by
  have hC := ctl_atD hat
  cases hs : d.c.site with
  | smr => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | fpx => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | arrD => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | arrF => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | bar => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | exit => exact noUbAt_simple hp d.c (by simp [hs]) hC hi hc hf
  | wq => exact noUbAt_polls hp d.c (by simp [hs]) hC hi hc hf
  | wraw => exact noUbAt_polls hp d.c (by simp [hs]) hC hi hc hf
  | wsv => exact noUbAt_polls hp d.c (by simp [hs]) hC hi hc hf
  | lenA => exact noUbAt_len hp d.c hl (by simp [hs]) hC hi hc hf
  | lenB => exact noUbAt_len hp d.c hl (by simp [hs]) hC hi hc hf
  | scale r => exact noUbAt_scale hp d.c ⟨r, hs⟩ hC hi hc hf
  | raw r i => exact noUbAt_raw hp d.c ⟨r, i, hs⟩ hC hi hc hf
  | store r s =>
    obtain ⟨-, -, -, -, hF0⟩ := hat
    have hF' := ((holds_append _ _ _).mp hF0).2
    simp only [dF, hs, holds_append] at hF'
    obtain ⟨-, hreg, -⟩ := hF'
    refine noUbAt_store hp d.c ⟨r, s, hs⟩ hC hi hc hf ⟨chunkVal L g d s, ?_, dequantChunk_width _ _⟩
    simpa [chunkRegOf, hs] using hreg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
