-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Result.SingleVisit
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCoordinates
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.CorrectionSource
import Kernels.TmlFa4Fwd.Proof.Protocol.SelectedCacheOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaMaximalCacheExtent
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
public import Kernels.TmlFa4Fwd.Proof.Thread.NormalizedOutputSource
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedNormalizedRow
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Result
open PTX PTX.Proof Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

/-- The ordered source byte of each valid repeated output slot carries its normalized value. -/
def RepeatedAttentionSlots (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ (issue : EvId) (batch : Nat) (stage : Fin 2) (box : Fin 4) (x y k : Nat),
    let coords := assignedCoordinates p batch (issue.1/l.block)
    batch < p.batch →
    tilePrefix p batch*p.heads ≤ issue.1/l.block →
    issue.1/l.block < tilePrefix p (batch+1)*p.heads →
    trips p batch coords.1 ≠ 1 →
    stageRow coords.1 stage+y < p.qLength batch → x < 32 → y < 128 → k < 4 →
    X.TensorStoreIssue issue p.oMapAddress
      (writebackStoreSpec p l issue.1 batch coords.2 coords.1 stage box) →
    Protocol.Output.OrderedSlot l X issue
      (writebackStoreSpec p l issue.1 batch coords.2 coords.1 stage box)
      x y k ((Value.float .f32
        (attention p batch coords.2 (stageRow coords.1 stage+y) (32*box.val+x))).byteAt k)

/-- The repeated writeback reads its ordered source slot and carries that byte to global O. -/
theorem repeatedOutputValuesOfAttentionSlots {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) (hSlots : RepeatedAttentionSlots p l X) :
    RepeatedOutputValues p X := by
  intro batch hb head hh row hr hTrip col hc k hk writer a bytes hw hCover
  let loc := (p.oLoc (p.qOffset batch+row) head col).at k
  have hTarget := outputByte_in (hp.packedRow_lt hb hr) hh hc hk
  obtain ⟨hCuQ,_⟩ := hFootprint.metadataProtected hp
  change a.Covers loc at hCover
  change p.oRegion.Contains loc at hTarget
  have hSpace : a.loc.space = .global := hCover.1.symm
  rcases Thread.globalWriteSource hX hw.intent hSpace with
    ⟨i,data,_,he⟩ | ⟨i,x,y,j,addr,spec,rfl,hIssue,hLoc,hSize⟩
  · obtain ⟨q,hq,h,hHead,hStore,hSize⟩ := Thread.lseWriteShape hp hX he hSpace
    let off := loc.addr-a.loc.addr
    have hOff : off < 4 := by
      have hBounds := hCover.2.2
      change a.loc.addr ≤ loc.addr ∧ loc.addr < a.loc.addr+a.size at hBounds
      unfold off
      omega
    have hByteLoc : loc = a.loc.at off := by
      have hBounds := hCover.2.2.1
      have hAddr : loc.addr = a.loc.addr+off := by unfold off; omega
      have hSpaces := hCover.1
      have hCtas := hCover.2.1
      rcases hLoc : loc with ⟨space,cta,addr⟩
      simp only [hLoc] at hAddr hSpaces hCtas
      unfold Loc.at
      rw [Loc.mk.injEq]
      exact ⟨hSpaces,hCtas,hAddr⟩
    rw [hStore] at hByteLoc
    exact (lseByte_apart_output hp hq hHead hOff (hByteLoc ▸ hTarget)).elim
  · have hDest := hLoc.trans (congrArg some (Acc.loc_of_one hCover hSize))
    obtain ⟨actual,ha,stage,box,hLo,hHi,rfl⟩ :=
      OutputWarp.issuedAssignment hp hX hIssue
    let coords := assignedCoordinates p actual (i.1/l.block)
    have hHead := (assignedCoordinates_valid hp hLo hHi).2
    obtain ⟨hx,hy,hj,hRow,hByteLoc⟩ :=
      Protocol.Output.writebackByteCoordinates hp ha hHead hDest
    let row' := stageRow coords.1 stage + y
    let col' := 32*box.val+x
    have hCol' : col' < 128 := by unfold col'; have := box.isLt; omega
    have hEq : (p.oLoc (p.qOffset batch+row) head col).at k =
        (p.oLoc (p.qOffset actual+row') coords.2 col').at j := by
      simpa only [row',col',coords,Nat.add_assoc] using hByteLoc
    obtain ⟨hPacked,hH,hC,hK⟩ := outputByte_inj hh hHead hc hCol' hk hj hEq
    obtain ⟨hBatch,hR⟩ := hp.packedRow_inj hb ha hr hRow hPacked
    subst actual
    have hTile : coords.1 = row/256 := by
      have hs := stage.isLt
      have hRowEq : row = 256*coords.1 + 128*stage.val+y := hR
      omega
    obtain ⟨rfl,_⟩ := Thread.Output.readyOfWritebackSpec hp hX stage box hIssue
    have hSlot := hSlots i batch stage box x y j hb hLo hHi
      (hTile.symm ▸ hTrip) hRow hx hy hj hIssue
    obtain ⟨o,stored,byte,ho,hActual,hWriteLoc,hWritten,_,hBytes,_,_,_,_⟩ := hw
    have hObserved := Protocol.Output.OrderedSlot.writeByte hX hIssue ho hWritten hSlot
    have hOut : wbyte a bytes loc = some byte := by
      rw [hBytes,wbyte,Acc.loc_of_one hCover hSize,Nat.sub_self]
      rfl
    rw [hOut,hObserved]
    change some ((Value.float .f32 (attention p batch coords.2 row' col')).byteAt j) = _
    have hR' : row = row' := hR
    have hH' : head = coords.2 := hH
    rw [← hR',← hH',← hC,← hK]

/-- The correction output events contain the normalized value of the repeated row. -/
def RepeatedNormalizedRows (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ g < l.threads, 8 ≤ Prologue.warpIndex l g → Prologue.warpIndex l g < 12 →
    ∀ (stage : Fin 2) (batch : Nat), batch < p.batch →
      tilePrefix p batch*p.heads ≤ g/l.block →
      g/l.block < tilePrefix p (batch+1)*p.heads →
      trips p batch (assignedCoordinates p batch (g/l.block)).1 ≠ 1 →
      stageRow (assignedCoordinates p batch (g/l.block)).1 stage +
        Correction.rowOf l g < p.qLength batch →
      ∃ start, Thread.Correction.SingleVisitNormalizedRow p l X g batch stage start

/-- The completed correction arithmetic suffices for O. Actual cache extents establish
which byte the writeback observes even when staging reuses cache addresses. -/
theorem repeatedOutputValuesOfNormalizedRows {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hRows : RepeatedNormalizedRows p l X) : RepeatedOutputValues p X := by
  apply repeatedOutputValuesOfAttentionSlots hp hX (hFootprint X hX)
  intro issue batch stage box x y k coords hb hLo hHi hTrip hRow hx hy hk hIssue
  let g := Thread.Output.sourceLane l issue y
  have hOwner : g/l.block = issue.1/l.block := by
    unfold g Thread.Output.sourceLane
    rw [hp.block]
    omega
  have hWarp : 8 ≤ Prologue.warpIndex l g ∧ Prologue.warpIndex l g < 12 := by
    unfold Prologue.warpIndex g Thread.Output.sourceLane
    rw [hp.block]
    omega
  have hRecord := hIssue
  obtain ⟨_,hGet⟩ := hRecord
  have hGrid := NamedBar.cta_lt (event_thread_lt hX hGet)
  have hg : g < l.threads := by
    change g < l.grid*l.block
    unfold g Thread.Output.sourceLane
    rw [hp.block] at *
    omega
  have hY := Thread.Output.sourceLane_row hp issue hy
  have hValid : stageRow (assignedCoordinates p batch (g/l.block)).1 stage +
      Correction.rowOf l g < p.qLength batch := by
    change Correction.rowOf l g = y at hY
    rwa [hOwner,hY]
  have hNormalized := hRows g hg hWarp.1 hWarp.2 stage batch hb
    (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) hValid
  obtain ⟨_,hReady⟩ := Thread.Output.readyOfWritebackSpec hp hX stage box hIssue
  let loc := (Correction.outputElementAccess l g stage box x y).loc.at k
  have hRead := Correction.writebackSourceAddress hp (batch := batch) (head := coords.2)
    (tile := coords.1) hOwner stage box hx hy hk
  obtain ⟨w,a,hWrite,_,hCover,hVisible,hValue⟩ := Thread.Output.normalizedSourceOfObservedRow
    hp hX hIssue hReady hx hy hk hRead (show loc = _ from rfl) hNormalized
  have hOrder := Protocol.Output.coveringWritesOrderOfCacheHandoff hp hX hIssue hRead
    hWrite.writes hCover (fun copy s hCopy hCache =>
      Protocol.Output.cacheCopyBeforeStagingOfSelectedExtent hp hX (hFootprint X hX)
        (fun _ _ hFinal hWork =>
          Thread.Mma.selectedCacheExtentOfConsistentPrefix hp hX hFootprint hFinal hWork)
        hCopy hCache hWrite.toStagingWrite hCover)
  exact ⟨loc,w,a,_,hRead,
    ⟨.inl hWrite.writes,hCover,.direct hVisible,Protocol.Output.coveringOrder hWrite.writes hCover
      hOrder⟩,hValue⟩

/-- The mathematical histories of a completed work item's live rows determine
all bytes written by its repeated stages. -/
theorem repeatedOutputValuesOfHistories {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    (hHistory : ∀ g < l.threads, 8 ≤ Prologue.warpIndex l g → Prologue.warpIndex l g < 12 →
      ∀ (stage : Fin 2) (batch : Nat), batch < p.batch →
        let coords := assignedCoordinates p batch (g/l.block)
        tilePrefix p batch*p.heads ≤ g/l.block →
        g/l.block < tilePrefix p (batch+1)*p.heads →
        trips p batch coords.1 ≠ 1 →
        stageRow coords.1 stage+Correction.rowOf l g < p.qLength batch →
        Nonempty (Thread.Correction.RepeatedRowHistory p l X g batch stage)) :
    RepeatedOutputValues p X := by
  apply repeatedOutputValuesOfNormalizedRows hp hX hFootprint
  intro g hg hWarpLo hWarpHi stage batch hb hLo hHi hTrip hLive
  exact Thread.Correction.normalizedRowOfCompletedHistory hp hX hDone hFootprint
    hg hWarpLo hWarpHi stage hb hLo hHi hLive
    (fun other hRow =>
      hHistory g hg hWarpLo hWarpHi other batch hb hLo hHi hTrip hRow)

end
end PTX.Kernels.TmlFa4Fwd.Result
