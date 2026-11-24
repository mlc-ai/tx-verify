-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitNormalizedRow
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlot
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Proof PTX.AsyncCopy Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An issued writeback descriptor identifies the stage that supplied its ready acquire. -/
theorem readyOfWritebackSpec (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {addr batch head tile : Nat} (stage : Fin 2) (box : Fin 4)
    (hIssue : X.TensorStoreIssue issue addr
      (writebackStoreSpec p l issue.1 batch head tile stage box)) :
    addr = p.oMapAddress ∧ ReadyAcquire l X issue stage := by
  obtain ⟨hAddr,_,actualStage,actualBox,hShared,hReady⟩ := OutputWarp.readyBox hp hX hIssue
  have hBase := congrArg Loc.addr hShared
  change l.sharedBase + (3072+65536*stage.val+16384*box.val) =
    l.sharedBase + (3072+65536*actualStage.val+16384*actualBox.val) at hBase
  have hStage : actualStage = stage := Fin.ext (by
    have := box.isLt
    have := actualBox.isLt
    omega)
  exact ⟨hAddr,hStage ▸ hReady⟩

/-- The correction lane's normalized write supplies the selected FP32 byte and
is published through the tensor store's actual ready acquire. -/
theorem singleVisitNormalizedSource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X) {issue : EvId}
    {addr x y k batch : Nat} {spec : TensorStore.Spec} {stage : Fin 2} {box : Fin 4} {loc : Loc}
    (hIssue : X.TensorStoreIssue issue addr spec) (hReady : ReadyAcquire l X issue stage)
    (hx : x < 32) (hy : y < 128) (hk : k < 4) (hLoc : TensorStore.readLoc spec x y k = some loc)
    (hElement : loc = (outputElementAccess l (sourceLane l issue y) stage box x y).loc.at k)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ issue.1/l.block)
    (hHi : issue.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (issue.1/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (issue.1/l.block)).1 stage+y < p.qLength batch) :
    let coords := assignedCoordinates p batch (issue.1/l.block)
    let value := fl (attention p batch coords.2 (stageRow coords.1 stage+y) (32*box.val+x))
    ∃ writer a, StageStagingWrite X writer stage a value.toBytes ∧
      writer.1/l.block = issue.1/l.block ∧ a.Covers loc ∧
      modelCausality l X loc (.thread writer) (.async issue (.read (.store x y k))) ∧
      wbyte a value.toBytes loc = some (value.byteAt k) := by
  let g := sourceLane l issue y
  have hOwner : g/l.block = issue.1/l.block := by unfold g sourceLane; rw [hp.block]; omega
  have hY : rowOf l g = y := sourceLane_row hp issue hy
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold warpIndex g sourceLane
    rw [hp.block]
    omega
  have hRecord := hIssue
  obtain ⟨_,hGet⟩ := hRecord
  have hGrid := NamedBar.cta_lt (event_thread_lt hX hGet)
  have hg : g < l.threads := by
    change g < l.grid*l.block
    unfold g sourceLane
    rw [hp.block] at *
    omega
  have hValid : stageRow (assignedCoordinates p batch (g/l.block)).1 stage+rowOf l g <
      p.qLength batch := by rwa [hOwner,hY]
  obtain ⟨start,old,reciprocal,hNormalized,hExact⟩ :=
    Correction.singleVisitNormalizedRowOfComplete hp hX hDone hFootprint hg hWarp.1 hWarp.2
      stage hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) hValid
  let write := start + 10 * (4*box.val+x/8) + 2 + 4*((x/4)%2) + x%4
  let a := outputElementAccess l g stage box x y
  let value := fl (attention p batch (assignedCoordinates p batch (issue.1/l.block)).2
    (stageRow (assignedCoordinates p batch (issue.1/l.block)).1 stage+y) (32*box.val+x))
  let chunk : Fin 16 := ⟨4*box.val+x/8, by have := box.isLt; omega⟩
  let elem : Fin 8 := ⟨x%8, by omega⟩
  have hValue : old chunk elem.val * reciprocal =
      attention p batch (assignedCoordinates p batch (issue.1/l.block)).2
        (stageRow (assignedCoordinates p batch (issue.1/l.block)).1 stage+y) (32*box.val+x) := by
    have hAt := hExact chunk elem
    rw [hOwner,hY] at hAt
    rw [show 8*chunk.val+elem.val = 32*box.val+x by dsimp [chunk,elem]; omega] at hAt
    exact hAt
  have hWrite := (hNormalized.element box hx).2
  change X.get (g,write) = some ⟨outputStorePc stage box ⟨x/4,by omega⟩,
    .wr (outputElementAccess l g stage box x (rowOf l g))
      (fl (old chunk elem.val * reciprocal)).toBytes⟩ at hWrite
  rw [hY,hValue] at hWrite
  have hStaging : StageStagingWrite X (g,write) stage a value.toBytes :=
    StageStagingWrite.ofEvent box ⟨x/4,by omega⟩ hWrite
  obtain ⟨pub,hPub⟩ := actualReadyIncludesEveryRow hp hX hReady hy
  obtain ⟨_,_,hPublish⟩ := actualStagingPublication hp hX hIssue hy hReady hPub hStaging
  have hByte : loc = a.loc.at k := hElement
  have hCover : a.Covers loc := hByte.symm ▸ Acc.covers_at hk
  have hSpace : loc.space = .shared := by rw [hByte]; rfl
  have hCta : loc.cta = g/l.block := by rw [hByte]; rfl
  have hRead : AsyncCovers X issue (.read (.store x y k)) loc :=
    ⟨{loc, size := 1}, false, ⟨rfl, spec, addr, hIssue, hLoc, rfl⟩,
      rfl, rfl, le_rfl, Nat.lt_succ_self _⟩
  refine ⟨(g,write),a,hStaging,hOwner,hCover,hPublish.modelCausality hSpace hCta hRead,?_⟩
  simp only [hByte,wbyte,Loc.at,Nat.add_sub_cancel_left,Value.toBytes]
  rw [List.getElem?_map,List.getElem?_range (show k < value.bytes from hk)]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Thread.Output
