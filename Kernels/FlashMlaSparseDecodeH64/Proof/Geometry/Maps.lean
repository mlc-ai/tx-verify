-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Data.TensorMaps

@[expose] public section

/-! ## The four published tensor maps are valid under `Pre` -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Geometry
open PTX TensorDescriptor

/-- The Q map's outer byte strides. -/
theorem mapQ_valid_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    Valid (mapQ P.qBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.qClass) := by
  apply mapQ_valid
  · exact h.qAlign
  · exact ⟨by decide, by have := h.strideRange; omega⟩
  · exact ⟨by decide, by have := h.strideRange; omega⟩
  · refine ⟨?_, ?_⟩
    · omega
    · have := h.strideRange
      omega
  · exact ⟨h.sqPos, h.sqRange⟩
  · exact ⟨h.bPos, h.bRange⟩

/-- The O map's outer byte strides. -/
theorem mapO_valid_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    Valid (mapO P.outBase 512 32768 (P.s_q * 32768) P.s_q P.b .zero P.oClass) := by
  apply mapO_valid
  · exact h.outAlign
  · exact ⟨by decide, by have := h.strideRange; omega⟩
  · exact ⟨by decide, by have := h.strideRange; omega⟩
  · refine ⟨?_, ?_⟩
    · omega
    · have := h.strideRange
      omega
  · exact ⟨h.sqPos, h.sqRange⟩
  · exact ⟨h.bPos, h.bRange⟩

/-- The main KV map is valid: its row count is positive and below `2^31`. -/
theorem mapKv_valid_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0) :
    Valid (mapKv P.kvBase P.numBlocks P.blockStride P.kvClass) := by
  apply mapKv_valid
  · exact h.kvAlign
  · refine ⟨?_, by have := h.rowsRange; omega⟩
    have hb : 0 < P.blockStride / 528 := by
      have := h.pagePos
      have := h.pageFits
      omega
    exact Nat.mul_pos h.numBlocksPos hb

/-- The extra KV map is valid when the extra cache is on. -/
theorem mapExtraKv_valid_of_pre {P : Params} {L : Launch} {mem0 : Mem0} (h : Pre P L mem0)
    (hextra : P.extra_topk ≠ 0) :
    Valid (mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass) := by
  have hp := h.extraPos (Nat.pos_of_ne_zero hextra)
  apply mapExtraKv_valid
  · exact h.extraKvAlign
  · refine ⟨?_, by have := h.extraRowsRange; omega⟩
    have hb : 0 < P.extraBlockStride / 528 := by
      have := hp.1
      have := hp.2.2.2
      omega
    exact Nat.mul_pos hp.2.1 hb

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Geometry
