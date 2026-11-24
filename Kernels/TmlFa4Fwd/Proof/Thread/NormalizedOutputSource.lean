-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitNormalizedRow
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadyHistory
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Proof PTX.AsyncCopy Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

/-- The observed normalized row supplies the exact byte through the selected
output-ready publication. -/
theorem normalizedSourceOfObservedRow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {issue : EvId} {addr x y k batch : Nat} {spec : TensorStore.Spec}
    {stage : Fin 2} {box : Fin 4} {loc : Loc}
    (hIssue : X.TensorStoreIssue issue addr spec)
    (hReady : ReadyAcquire l X issue stage) (hx : x < 32) (hy : y < 128) (hk : k < 4)
    (hLoc : TensorStore.readLoc spec x y k = some loc)
    (hElement : loc = (outputElementAccess l (sourceLane l issue y) stage box x y).loc.at k)
    (hRow : ∃ start,
      Thread.Correction.SingleVisitNormalizedRow p l X (sourceLane l issue y) batch stage start) :
    let coords := assignedCoordinates p batch (issue.1/l.block)
    let value := fl (attention p batch coords.2 (stageRow coords.1 stage+y) (32*box.val+x))
    ∃ writer a, StageStagingWrite X writer stage a value.toBytes ∧
      writer.1/l.block = issue.1/l.block ∧ a.Covers loc ∧
      modelCausality l X loc (.thread writer) (.async issue (.read (.store x y k))) ∧
      wbyte a value.toBytes loc = some (value.byteAt k) := by
  let g := sourceLane l issue y
  have hOwner : g/l.block = issue.1/l.block := by unfold g sourceLane; rw [hp.block]; omega
  have hY : rowOf l g = y := sourceLane_row hp issue hy
  obtain ⟨start,old,reciprocal,hNormalized,hExact⟩ := hRow
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
