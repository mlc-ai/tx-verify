-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderUsedKRead
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionMetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTripMetadata
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPageWord
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageWord
import all Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderUsedKRead
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionMetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxMetadataReads
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTripMetadata
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingPageWord
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderRecurringPageWord

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- The four used-K observations belong to their selected request reads. -/
theorem MetadataRead.usedK {X : Execution} {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : MetadataRead X i .usedK a bytes) :
    LoaderUsedKRead X i a bytes ∨ MmaTripRead.Observed X i 2 a bytes ∨
      SoftmaxGeometryRead X i 2 a bytes ∨ CorrectionUsedKRead X i a bytes := by
  obtain ⟨site, hSite, he⟩ := h
  change site ∈ [385, 2116, 3373, 7959] at hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl
  · exact .inl he
  · exact .inr (.inl he)
  · exact .inr (.inr (.inl he))
  · exact .inr (.inr (.inr he))

/-- Every page-table observation is an optional priming or recurring lookup. -/
theorem MetadataRead.pageTable {X : Execution} {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (h : MetadataRead X i .pageTable a bytes) :
    LoaderPrimingPageRead X i a bytes ∨ LoaderRecurringPageRead X i a bytes := by
  obtain ⟨site, hSite, he⟩ := h
  change site ∈ [503, 946, 1416] at hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl
  · exact .inl he
  · exact .inr ⟨0, he⟩
  · exact .inr ⟨1, he⟩

end PTX.Kernels.TmlFa4Fwd.Thread
