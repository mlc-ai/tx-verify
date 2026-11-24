-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.TensorInputReuse
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCacheOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

/-- A second-stage staging store uses its actual final MMA acquire to order cache writes.
The consuming fragment and cache-ready order determine which operand bytes it can reuse. -/
theorem cacheBeforeSecondStagingOfOperand {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {copy writer : EvId} {s : Spec} {a : Acc} {data : List Byte} {loc : Loc}
    (hCopy : X.Copy copy s) (hCopyCovers : s.dst.Covers loc)
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hStoreCovers : a.Covers loc)
    (hOperand : ∀ commit spec, Thread.SecondOutputCommit X commit spec →
      SameCta l commit.1 writer.1 →
      ∃ mma d op accum mask index, X.MmaIssue mma d op accum mask ∧
        TraceBefore X mma commit ∧ op.byteLoc .b index = some loc ∧
        ByteCausality l X loc (.async copy (.write .copy)) (.async mma (.mmaRead true index))) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  obtain ⟨wait, hWait, hLater⟩ := Thread.StageStagingWrite.secondAcquire hp hX hStage
  obtain ⟨commit, spec, scope, hCommit, hCta, hObserved⟩ :=
    Thread.secondOutputAcquireReads hp hX hWait
  have hOwner : SameCta l commit.1 writer.1 := hLater.1 ▸ hCta
  obtain ⟨mma, d, op, accum, mask, index, hMma, hEarlier, hLoc, hBefore⟩ :=
    hOperand commit spec hCommit hOwner
  obtain ⟨hObserve, hScope, hRead⟩ := hObserved (isB := true) hMma hEarlier.1 hEarlier.2.1 hLoc
  have hShape := actualCopyShape hX hCopy
  have hIntent : X.Intent (.async copy (.write .copy)) s.dst true :=
    ⟨rfl, s, hCopy, hShape.whole, rfl⟩
  have hShared := hCopyCovers.1.trans hShape.dstShared
  have hWritten : X.MemWrites (.thread writer) a data := .inl hStage.writes
  exact .commitOperand hShared ⟨s.dst, hIntent, hCopyCovers⟩ (.inl ⟨d, op, accum, mask, hMma⟩)
    hRead hBefore ⟨scope, hObserve, hScope⟩ hLater
    ⟨a, .inl ⟨true, hWritten.intent⟩, hStoreCovers⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
