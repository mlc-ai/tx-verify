-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlot
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionReadyElements
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Proof Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction (outputElementAccess rowOf)

noncomputable section

private theorem publishedStageRange {base addr : Nat} {stage : Fin 2}
    (h : addr < base + 3072 + 65536 * (stage.val+1)) :
    addr < base+68608 ∨ stage = 1 := by
  by_cases hs : stage = 1
  · exact .inr hs
  · have hVal : stage.val = 0 := by
      have hs' : stage.val ≠ 1 := fun h => hs (Fin.ext h)
      have := stage.isLt
      omega
    rw [hVal,Nat.zero_add,Nat.mul_one,Nat.add_assoc] at h
    exact .inl h

/-- The actual source of a pending output byte retains its correction stage and CTA. -/
theorem actualPublishedStagingSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {addr x y k : Nat} {spec : TensorStore.Spec} {loc : Loc}
    (hIssue : X.TensorStoreIssue issue addr spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) :
    ∃ (stage : Fin 2) (writer : EvId) (access : Acc) (data : List Byte),
      StageStagingWrite X writer stage access data ∧ access.Covers loc ∧
      writer.1/l.block = issue.1/l.block ∧
      (loc.addr < l.sharedBase+68608 ∨ stage = 1) ∧
      loc.space = .shared ∧ loc.cta = issue.1 / l.block ∧
      modelCausality l X loc (.thread writer) (.async issue (.read (.store x y k))) := by
  obtain ⟨stage, box, hReady, hx, hy, hk, hByte⟩ := actualReadySlot hp hX hIssue hRead
  let g := sourceLane l issue y
  have hRow : rowOf l g = y := sourceLane_row hp issue hy
  obtain ⟨pub, hPub⟩ := actualReadyIncludesEveryRow hp hX hReady hy
  obtain ⟨write, data, hWritten, _⟩ :=
    Correction.stageElementWrittenBeforeReady hp hX hPub box ⟨x, hx⟩
  obtain ⟨_, _, hPublished⟩ :=
    actualStagingPublication hp hX hIssue hy hReady hPub hWritten
  let access := outputElementAccess l g stage box x (rowOf l g)
  have hByte' : loc = access.loc.at k := by simpa only [access,hRow] using hByte
  have hCover : access.Covers loc := hByte'.symm ▸ Acc.covers_at hk
  have hSpace : loc.space = .shared := by rw [hByte']; rfl
  have hCta : loc.cta = g / l.block := by rw [hByte']; rfl
  have hOwner : g / l.block = issue.1 / l.block := by
    unfold g sourceLane
    rw [hp.block]
    omega
  have hReadCover : AsyncCovers X issue (.read (.store x y k)) loc :=
    ⟨{loc, size := 1}, false, ⟨rfl, spec, addr, hIssue, hRead, rfl⟩,
      rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
  have hRange := elementStageRange hx (show rowOf l g < 128 by rwa [hRow]) hCover
  have hBounds := publishedStageRange hRange.2
  exact ⟨stage,(g,write),access,data,hWritten,hCover,hOwner,hBounds,hSpace,hCta.trans hOwner,
    hPublished.modelCausality hSpace hCta hReadCover⟩

/-- The stage-specific source is an ordinary correction staging observation. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.StageStagingWrite.toStagingWrite
    {X : Execution} {writer : EvId} {stage : Fin 2} {a : Acc} {data : List Byte}
    (h : StageStagingWrite X writer stage a data) :
    Thread.Correction.StagingWrite X (.thread writer) a data := by
  obtain ⟨box, chunk, he⟩ := h.decoded
  exact .of_event stage box chunk he

/-- Every pending O byte has a performed correction write published to the output issuer.
Its address, row and word come from that same consistent execution. -/
theorem actualPublishedSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {addr x y k : Nat} {spec : TensorStore.Spec} {loc : Loc}
    (hIssue : X.TensorStoreIssue issue addr spec)
    (hRead : TensorStore.readLoc spec x y k = some loc) :
    ∃ writer access data, X.Writes writer access data ∧ access.Covers loc ∧
      loc.space = .shared ∧ loc.cta = issue.1 / l.block ∧
      modelCausality l X loc (.thread writer) (.async issue (.read (.store x y k))) := by
  obtain ⟨_,writer,access,data,hStage,hCover,_,_,hShared,hCta,hOrder⟩ :=
    actualPublishedStagingSource hp hX hIssue hRead
  exact ⟨writer,access,data,hStage.writes,hCover,hShared,hCta,hOrder⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
