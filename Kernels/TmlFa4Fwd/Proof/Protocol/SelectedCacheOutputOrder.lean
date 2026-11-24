-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedRecurringCopyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingKeyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingValueOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputScratchSource
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCacheCopyFamily
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final))
include hp hX hFrame hExtent

/-- The selected request's actual cache acquisitions order every overlapping
ordinary cache copy before the correction staging write. -/
theorem cacheCopyBeforeStagingOfSelectedExtent {copy writer : EvId} {s : Spec} {a : Acc}
    {data : List Byte} {loc : Loc} (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (hWrite : Thread.Correction.StagingWrite X (.thread writer) a data) (hOther : a.Covers loc) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  obtain ⟨hStage,hCta⟩ := cacheOverlapStaging hp hX hCopy hCover hWrite hOther
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with
    ⟨pair,upper,hPriming⟩ | ⟨pair,upper,hPriming⟩ | ⟨_,he,hVector,hKind⟩
  · exact primingKeyCopyBeforeSecondStaging hp hX hPriming hStage hCta hCover hOther
  · exact primingValueCopyBeforeSecondStaging hp hX hPriming hStage hCta hCover hOther
  · exact recurringCacheBeforeSecondStagingOfUse hp hX hCopy hCover hStage hOther hCta
      (recurringCopyUsesBeforeSelectedFinal hp hX hFrame hExtent he hVector hKind hCover)

/-- The same selected cache extent orders every overlapping ordinary copy
before an O store's shared-memory read, including pending effects. -/
theorem cacheCopyBeforeOutputReadOfSelectedExtent {copy issue : EvId} {address x y byte : Nat}
    {loc : Loc} {spec : TensorStore.Spec} {s : Spec} (hCopy : X.Copy copy s)
    (hCover : s.dst.Covers loc) (hStore : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y byte = some loc) :
    ByteCausality l X loc (.async copy (.write .copy))
      (.async issue (.read (.store x y byte))) := by
  rcases Thread.Loader.copyPrimingOrRecurringVector hX hCopy with
    ⟨pair,upper,hPriming⟩ | ⟨pair,upper,hPriming⟩ | ⟨_,he,hVector,hKind⟩
  · exact primingKeyCopyBeforeOutputRead hp hX hPriming hCover hStore hRead
  · exact primingValueCopyBeforeOutputRead hp hX hPriming hCover hStore hRead
  · exact recurringCacheBeforePendingOutputOfUse hp hX hCopy hCover hStore hRead
      (recurringCopyUsesBeforeSelectedFinal hp hX hFrame hExtent he hVector hKind hCover)

/-- The selected cache extent fixes the source of every O byte, including bytes
in the cache region. The source is the ordinary correction staging element. -/
theorem actualSourceOrderedOfSelectedExtent {issue : EvId} {address x y byte : Nat}
    {spec : TensorStore.Spec} {loc : Loc} (hStore : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y byte = some loc) :
    ∃ writer dst data, X.Writes writer dst data ∧ dst.Covers loc ∧
      SourceOrdered l X (.async issue (.read (.store x y byte))) loc (.thread writer) dst data := by
  obtain ⟨_, writer, dst, data, hStaging, hCover, _, _, _, _, hVisible⟩ :=
    Thread.Output.actualPublishedStagingSource hp hX hStore hRead
  have hOrder := coveringWritesOrderOfCacheHandoff hp hX hStore hRead hStaging.writes hCover
    (fun _ _ hCopy hCopyCover => cacheCopyBeforeStagingOfSelectedExtent
      hp hX hFrame hExtent hCopy hCopyCover hStaging.toStagingWrite hCover)
  exact ⟨writer, dst, data, hStaging.writes, hCover,
    .inl hStaging.writes, hCover, .direct hVisible, coveringOrder hStaging.writes hCover hOrder⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
