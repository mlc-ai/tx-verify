-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputBytes
import Kernels.TmlFa4Fwd.Proof.Safety.TensorInputStaging
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionReadyElementUniqueness
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlot
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX Correction Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Any two ordinary stores covering the shared source of an output byte are the
same correction event. -/
theorem samePublishedWriter {issue i j : EvId} {addr x y k : Nat} {s : TensorStore.Spec} {src : Loc}
    (hIssue : X.TensorStoreIssue issue addr s) (hRead : TensorStore.readLoc s x y k = some src)
    {a b : Acc} {data₁ data₂ : List Byte} (hi : X.Writes i a data₁) (hj : X.Writes j b data₂)
    (hCoverA : a.Covers src) (hCoverB : b.Covers src) : i = j := by
  obtain ⟨stage, box, hReady, hx, hy, hk, hLoc⟩ := Thread.Output.actualReadySlot hp hX hIssue hRead
  let g := Thread.Output.sourceLane l issue y
  have hShared : src.space = .shared := by rw [hLoc]; rfl
  have hCover : (Correction.outputElementAccess l g stage box x y).Covers src :=
    hLoc.symm ▸ Acc.covers_at hk
  have hLo := (Thread.Output.elementStageRange hx hy hCover).1
  have hStageA := (Thread.ordinarySharedWriteBelowOrStaging hp hX hi hCoverA hShared).resolve_left
    (by omega)
  have hStageB := (Thread.ordinarySharedWriteBelowOrStaging hp hX hj hCoverB hShared).resolve_left
    (by omega)
  obtain ⟨hLaneA, _, hWriteA⟩ :=
    Thread.Output.stagingWriterOfSlot hp hX hx hy hk hLoc hStageA hCoverA
  obtain ⟨hLaneB, _, hWriteB⟩ :=
    Thread.Output.stagingWriterOfSlot hp hX hx hy hk hLoc hStageB hCoverB
  obtain ⟨pub, hPub⟩ := Thread.Output.actualReadyIncludesEveryRow hp hX hReady hy
  obtain ⟨aLane, aIndex⟩ := i
  obtain ⟨bLane, bIndex⟩ := j
  change aLane = g at hLaneA
  change bLane = g at hLaneB
  subst aLane bLane
  exact Prod.ext rfl (Thread.Correction.sameStagingByteUnique hp hX hPub hWriteA hWriteB
    hCoverA hCoverB)

/-- Every ordinary write of a tensor store's shared source byte precedes the source read. -/
theorem ordinaryWriteBeforeOutputRead {issue writer : EvId} {address x y k : Nat}
    {s : TensorStore.Spec} {src : Loc} (hIssue : X.TensorStoreIssue issue address s)
    (hRead : TensorStore.readLoc s x y k = some src) {a : Acc} {data : List Byte}
    (hw : X.Writes writer a data) (hCover : a.Covers src) :
    ByteCausality l X src (.thread writer) (.async issue (.read (.store x y k))) := by
  obtain ⟨published, _, _, hWrite, hSlot, _, _, hVisible⟩ :=
    Thread.Output.actualPublishedSource hp hX hIssue hRead
  have hEq := samePublishedWriter hp hX hIssue hRead hWrite hw hSlot hCover
  exact hEq ▸ ByteCausality.direct hVisible

/-- The output publication identifies its only ordinary writer. Any overlapping tensor
input precedes it, leaving only the cache handoff for output bytes in the cache region. -/
theorem coveringWritesOrderOfCacheHandoff {issue writer : EvId} {address x y k : Nat}
    {spec : TensorStore.Spec} {loc : Loc} {dst : Acc} {data : List Byte}
    (hIssue : X.TensorStoreIssue issue address spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) (hWrite : X.Writes writer dst data)
    (hCover : dst.Covers loc)
    (hCache : ∀ copy s, X.Copy copy s → s.dst.Covers loc →
      ByteCausality l X loc (.async copy (.write .copy)) (.thread writer)) :
    CoveringWritesOrder l X (.async issue (.read (.store x y k))) loc writer := by
  obtain ⟨_, _, _, _, _, _, hLoc⟩ := Thread.Output.actualReadySlot hp hX hIssue hRead
  have hShared : loc.space = .shared := by rw [hLoc]; rfl
  intro other a bytes hOther hByte
  rcases Thread.sharedWriteSource hX hOther hByte hShared with
    ⟨i, rfl, hOtherWrite⟩ | ⟨input, col, row, byte, rfl⟩ | ⟨copy, s, rfl, hCopy, rfl⟩
  · have hEq := samePublishedWriter hp hX hIssue hRead hWrite hOtherWrite hCover hByte
    subst i
    exact .inl ⟨writer.2, le_rfl, rfl⟩
  · exact .inr (.inl (Safety.tensorInputBeforeOrdinaryWrite hp hX hOther.intent hByte
      hWrite hCover).2)
  · exact .inr (.inl (hCache copy s hCopy hByte))

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
