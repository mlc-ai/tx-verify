-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputScratchSource
public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitOutputSource
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCacheOverlap
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialValueStaging
import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitCacheCopies
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy Epilogue Correction Loader
open PTX.Kernels.TmlFa4Fwd.Mma (trips)
open Thread (initialKeyByte)

noncomputable section

private theorem singleVisitCacheBeforeStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {batch : Nat} {writer copy : EvId} {a : Acc} {data : List Byte} {s : Spec} {loc : Loc}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ copy.1/l.block)
    (hHi : copy.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (copy.1/l.block)).1 = 1)
    (hSame : copy.1/l.block = writer.1/l.block)
    (hStage : Thread.StageStagingWrite X writer 1 a data) (hStageCover : a.Covers loc)
    (hCopy : X.Copy copy s) (hCover : s.dst.Covers loc)
    (slot : Fin 2) (pair : Fin 16) (upper : Bool)
    (hDst : s.dst = {loc := ⟨.shared, copy.1/l.block,
      kvCopyAddress l.sharedBase slot (copy.1%l.block) pair upper⟩, size := 16}) :
    ByteCausality l X loc (.async copy (.write .copy)) (.thread writer) := by
  let lane : Fin 64 := ⟨copy.1%l.block%64,Nat.mod_lt _ (by decide)⟩
  let base := kvCopyAddress l.sharedBase slot lane pair upper
  have hPhysical : s.dst = {loc := ⟨.shared,writer.1/l.block,base⟩, size := 16} := by
    simpa [base,lane,kvCopyAddress,Nat.mod_mod,hSame] using hDst
  have hCover' := hCover
  rw [hPhysical] at hCover'
  obtain ⟨hSpace,hCta,hMin,hMax⟩ := hCover'
  let off := loc.addr-base
  have hOff : off < 16 := by
    change base ≤ loc.addr at hMin
    change loc.addr < base+16 at hMax
    unfold off
    omega
  have hLoc : loc = ⟨.shared,writer.1/l.block,base+off⟩ := by
    have hAddr : loc.addr = base+off := by change base ≤ loc.addr at hMin; unfold off; omega
    cases loc
    congr
  fin_cases slot
  · obtain ⟨frag,row,k,byte,hRow,hK,hByte,hAt⟩ :=
      initialKeyByteOfVector l (writer.1/l.block) lane pair upper hOff
    have hByteLoc : initialKeyByte l (writer.1/l.block) frag row k byte = loc :=
      hAt.trans hLoc.symm
    obtain ⟨pub,group,j,spec,_,_,_,_,_,hMember,_,hSource,_,hOrder⟩ :=
      initialKeyCopyBeforeSecondStaging hp hX hStage frag hRow hK hByte
        (hByteLoc.symm ▸ hStageCover)
    rw [hByteLoc] at hSource hOrder
    have hLinked := ((group.member j spec).mp hMember).2.2
    have hEq := Thread.Loader.singleVisitCacheCopyUnique hp hX hDone hFootprint
      hb hLo hHi hTrip hCopy hLinked hCover hSource
    exact hEq ▸ hOrder
  · obtain ⟨frag,col,k,byte,hCol,hK,hByte,hAt⟩ :=
      initialValueByteOfVector l (writer.1/l.block) lane pair upper hOff
    have hByteLoc : initialValueByte l (writer.1/l.block) frag col k byte = loc :=
      hAt.trans hLoc.symm
    obtain ⟨pub,group,j,spec,_,_,_,_,_,hMember,_,hSource,_,hOrder⟩ :=
      initialValueCopyBeforeSecondStaging hp hX hStage frag hCol hK hByte
        (hByteLoc.symm ▸ hStageCover)
    rw [hByteLoc] at hSource hOrder
    have hLinked := ((group.member j spec).mp hMember).2.2
    have hEq := Thread.Loader.singleVisitCacheCopyUnique hp hX hDone hFootprint
      hb hLo hHi hTrip hCopy hLinked hCover hSource
    exact hEq ▸ hOrder

/-- Each valid single-visit output slot has an ordered writer containing its exact
attention byte. Cache reuse is ordered through the initial K or V operand read. -/
theorem singleVisitAttentionSlot {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {issue : EvId} {x y k batch : Nat} {stage : Fin 2} {box : Fin 4}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ issue.1/l.block)
    (hHi : issue.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (issue.1/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (issue.1/l.block)).1 stage+y <
      p.qLength batch)
    (hx : x < 32) (hy : y < 128) (hk : k < 4)
    (hIssue : X.TensorStoreIssue issue p.oMapAddress
      (writebackStoreSpec p l issue.1 batch (assignedCoordinates p batch (issue.1/l.block)).2
        (assignedCoordinates p batch (issue.1/l.block)).1 stage box))
    (hReady : Thread.Output.ReadyAcquire l X issue stage) :
    let coords := assignedCoordinates p batch (issue.1/l.block)
    OrderedSlot l X issue (writebackStoreSpec p l issue.1 batch coords.2 coords.1 stage box)
      x y k ((Value.float .f32 (attention p batch coords.2
        (stageRow coords.1 stage+y) (32*box.val+x))).byteAt k) := by
  let g := Thread.Output.sourceLane l issue y
  have hOwner : g/l.block = issue.1/l.block := by
    unfold g Thread.Output.sourceLane
    rw [hp.block]
    omega
  let loc := (outputElementAccess l g stage box x y).loc.at k
  let coords := assignedCoordinates p batch (issue.1/l.block)
  have hLoc := writebackSourceAddress hp (batch := batch) (head := coords.2) (tile := coords.1)
    hOwner stage box hx hy hk
  obtain ⟨writer,a,hWrite,hWriterCta,hCover,hVisible,hByte⟩ :=
    Thread.Output.singleVisitNormalizedSource hp hX hDone hFootprint hIssue hReady hx hy hk
      hLoc (show loc = _ from rfl) hb hLo hHi hTrip hRow
  let value := Value.float .f32
    (attention p batch coords.2 (stageRow coords.1 stage+y) (32*box.val+x))
  have hWriter := hWrite.writes
  have hOrdered := coveringWritesOrderOfCacheHandoff hp hX hIssue hLoc hWriter hCover
  refine ⟨loc,writer,a,value.toBytes,hLoc,⟨.inl hWriter,hCover,.direct hVisible,?_⟩,hByte⟩
  apply coveringOrder hWriter hCover
  apply hOrdered
  intro copy s hCopy hCache
  obtain ⟨_,hCopyCta,slot,pair,upper,hDst⟩ := cacheOverlap hp hX hIssue hLoc hCopy hCache
  have hSame : copy.1/l.block = writer.1/l.block := hCopyCta.trans hWriterCta.symm
  have hStage : stage = 1 := by
    have hRange := Thread.Output.elementStageRange hx hy
      (show (outputElementAccess l g stage box x y).Covers loc from Acc.covers_at hk)
    have hLower := (Thread.cacheCopyWriteLower hp hX hCopy).trans hCache.2.2.1
    change l.sharedBase+68608 ≤ loc.addr at hLower
    have hVal := stage.isLt
    apply Fin.ext
    change stage.val = 1
    omega
  rw [hStage] at hWrite
  exact singleVisitCacheBeforeStaging hp hX hDone hFootprint hb (hCopyCta.symm ▸ hLo)
    (hCopyCta.symm ▸ hHi) (hCopyCta.symm ▸ hTrip) hSame hWrite hCover hCopy hCache
    slot pair upper hDst

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
