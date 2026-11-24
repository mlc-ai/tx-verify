-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstCacheAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValueCopyProgress
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderCopyBytes
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValuePacketClose
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderFirstCachePhase
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPrimingPublication
import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryReadyPhase
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstValueRoute
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondQueryProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmOpeningProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread.Output

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 15) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg hw hb hLo hHi

private theorem openingValueAcquiredWithExactRank :
    ∃ votes ends,
      ∃ done : Loader.OpeningValueAcquired l X g (Loader.primingSearchShuffleCount batch+32)
        votes ends,
      ∀ lane < 32, ∃ j, j+1 = done.pos lane ∧
        Loader.OpeningValueWaitAt l X (warpLane l g lane) j := by
  obtain ⟨votes,ends,hK⟩ := selectedCacheKeyCommitWithRankOfMaximal hp hMax
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hg (by omega) hb hLo hHi
  have hStart := Loader.openingValueReachedBySecondLoader hp hMax hg hw
    (by unfold Loader.primingSearchShuffleCount; omega) hK
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  obtain ⟨done,hWait⟩ := Loader.openingValueAcquiredOfReady hp hMax hg hStart
    (fun lane hl hQuiet => by
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hThis : warpIndex l (warpLane l g lane) = 15 := hSame.2.symm.trans hw
      have hWarp : 14 ≤ warpIndex l (warpLane l g lane) := by rw [hThis]; decide
      have hPhase := Protocol.Loader.cacheEmptyPhaseBeforeSlotPublication
        hp hMax hSame.1.2.1 hWarp 1 hQuiet
      simpa only [Thread.Mma.Observation.emptyObject,hSame.1.2.2] using hPhase)
  exact ⟨votes,ends,done,hWait⟩

end

/-- The issued opening V packet and its exact materialized vectors for a loader warp. -/
abbrev OpeningValuePacketPublished (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) : Prop :=
    (∀ lane < 32, ∃ index,
      Thread.Loader.PrimingPublication l X (warpLane l g lane,index) 1 ∧
      X.async.arrived (warpLane l g lane,index) = true) ∧
    ∃ index : Fin 16 → Nat → Nat,
      ∀ (pair : Fin 16) (lane : Nat), lane < 32 → ∀ upper : Bool, ∃ spec,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1 - 1
      let tid := 32*warpIndex l g+lane
      let row := kvCopyRow tile tid pair
      let issue := (warpLane l g lane,index pair lane+if upper then 1 else 0)
      X.Copy issue spec ∧
      spec.src.loc = p.vLayout.loc (Loader.primingScratchPage p batch row) (co.2/6)
        (row%16) (kvCopyColumn tid upper) ∧
      spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      (X.async.copies issue).writeBytes = some
        (if row < p.kLength batch then
          (List.range 16).map (Protocol.LoaderReady.cacheByte p .value batch (co.2/6) row tid upper)
         else List.replicate 16 AsyncCopy.zeroByte)

private structure OpeningValueProgress (p : Params) (l : Launch) (X : Execution)
    (g batch firstShuffles : Nat) : Prop where
  packet : OpeningValuePacketPublished p l X g batch
  single : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1 →
    Nonempty (Thread.Loader.SingleVisitDrainNeighbors p l X g)
  warm : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 →
    ∃ c : Thread.Loader.WarmCacheStarted p l X g batch, c.shuffles = firstShuffles+32

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

private theorem openingValuePacketPublishedOfAcquire {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRank : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 < shuffles)
    {ends : Nat → Option TState} (done : Loader.OpeningValueAcquired l X g shuffles votes ends)
    (hWait : ∀ lane < 32, ∃ j, j+1 = done.pos lane ∧
      Loader.OpeningValueWaitAt l X (warpLane l g lane) j) :
    OpeningValueProgress p l X g batch shuffles := by
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1-1
  let warp := warpIndex l g
  let rows := fun (slot : Fin 2) lane => Loader.primingLaneRow tile (32*warp+lane) + 64*slot.val
  let bases := fun slot lane => Loader.primingVRowPointer p batch (co.2/6) (rows slot lane)
  let writes := fun w a data loc => Thread.Loader.loaderOutputWrites hFrame (w := w)
    (a := a) (data := data) (loc := loc)
  obtain ⟨_,⟨start⟩⟩ :=
    Loader.selectedPrimingAddressesOfMaximal hp hMax writes hg (by omega) hb hLo hHi
  obtain ⟨hTile,_,packed,_⟩ :=
    selectedCacheKeyMaskEntryOfMaximal hp hMax writes hg (by omega) hb hLo hHi
  have hMasks := Loader.openingValueMaskFrameOfMaximal hp hb hLo hHi hTile start packed done hWait
  have hAbi := Loader.openingValueAbiFromAddresses hp hb hLo hHi hRank start done
  have hStored := fun lane hl => Loader.openingValueSecondPointerWithFrameOfMaximal hp hMax hg
    (by omega) hb hLo hHi done hl
    (Loader.openingValueFirstPointerWithFrameOfMaximal hp hMax writes hg (by omega)
      hb hLo hHi done hAbi hWait lane hl)
  obtain ⟨ready,hPos,hRead⟩ :=
    Loader.openingValueBroadcastWithReadsOfMaximal hp hMax hg hb hLo hHi done hMasks hStored
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2/6 < p.kvHeads := by
    unfold Params.heads at hHead
    change co.2 < 6*p.kvHeads at hHead
    omega
  have hBounds (slot : Fin 2) (lane : Nat) (_ : lane < 32) :
      bases slot lane < 2^64 ∧ bases slot lane%16 = 0 := by
    obtain ⟨hEq,hFit,hAlign⟩ := Loader.sourceScratchPayload_live hp 1
      (Loader.primingScratchPageBound hp (row := rows slot lane) hb)
      (Nat.mod_lt (rows slot lane) (by decide)) hh
    rw [hEq] at hFit hAlign
    exact ⟨hFit,hAlign⟩
  have hFirst := fun lane hl => hRead lane hl 0
  obtain ⟨commit,index,hCopy⟩ := Loader.primingVPacketOfMaximal hp hMax hg (by omega)
    bases (fun _ => Loader.vPrimingResidual p batch co.1) (fun lane => done.pos lane+6)
    hBounds ready (by
      intro lane hl
      have h := hFirst lane hl
      simp only [Fin.val_zero,Nat.add_zero] at h
      exact h)
    (by intro lane _; rw [hPos]; exact Nat.add_le_add_left (by decide : 6 ≤ 8) _)
    (fun lane hl => (hStored lane hl).latest 1)
  refine ⟨?_,fun hSingle => ?_,fun hWarm => ?_⟩
  · refine ⟨fun lane hl => ?_,index,?_⟩
    · have hPub := Loader.openingValuePublishOfMaximal hp hMax hg done commit lane hl
      exact ⟨_,hPub,Protocol.LoaderReady.drainedPrimingPublication hp hMax hFrame hPub⟩
    · intro pair lane hl upper
      let tid := 32*warp+lane
      let row := kvCopyRow tile tid pair
      let base := bases (Loader.vPacketSlot pair) (Loader.vPacketSender pair lane)
      let spec := Loader.vPacketCopySpec l (warpLane l g lane) tid base
        (Loader.vPacketBytes p batch tile tid pair) pair upper
      have hIssue : X.Copy (warpLane l g lane,index pair lane+if upper then 1 else 0) spec :=
        ⟨_,hCopy pair lane hl upper⟩
      have hRow : rows (Loader.vPacketSlot pair) (Loader.vPacketSender pair lane) = row := by
        simpa only [rows,row,tid,Loader.vPacketSender,Loader.vPacketSelect,Loader.vPacketSlot,
          Nat.add_assoc] using Loader.kvCopyRow_of_pointerLane tile warp lane pair.val
      have hLoc : spec.src.loc = p.vLayout.loc (Loader.primingScratchPage p batch row) (co.2/6)
          (row%16) (kvCopyColumn tid upper) := by
        dsimp only [spec,Loader.vPacketCopySpec,base,bases]
        rw [hRow]
        exact Loader.primingVSourceLoc hp (Loader.primingScratchPageBound hp (row := row) hb)
          hh pair upper
      have hSource (hLive : row < p.kLength batch) :
          spec.src.loc = Protocol.LoaderReady.cacheVector p .value batch (co.2/6) row tid
            upper := by
        simpa only [Protocol.LoaderReady.cacheVector,Protocol.LoaderReady.cacheLayout,
          Loader.primingScratchPage,ite_eq_left hLive] using hLoc
      exact ⟨spec,hIssue,hLoc,rfl,
        Protocol.LoaderReady.cacheVectorWritesBytesOfMaximal hp hMax hFrame
        hIssue .value hb hh upper hSource rfl⟩
  · exact Thread.Loader.singleVisitDrainNeighborsOfValueCommit hp hMax hg hw
      (hp.cuQ_protected writes) hb hLo hHi hSingle start commit
  · exact Thread.Loader.warmCacheStartedWithRankOfOpeningValueCommit hp hMax hg hw
      (hp.cuQ_protected writes) hb hLo hHi hWarm start commit

private theorem openingValueProgressBySecondLoader {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 15) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    OpeningValueProgress p l X g batch (Loader.primingSearchShuffleCount batch+32) := by
  obtain ⟨_,_,done,hWait⟩ := openingValueAcquiredWithExactRank hp hMax hFrame hg hw hb hLo hHi
  exact openingValuePacketPublishedOfAcquire hp hMax hFrame hg (by omega) hb hLo hHi
    (by unfold Loader.primingSearchShuffleCount; omega) done hWait

/-- Each lane of warp 15 issues the opening V publication and all 16 pairs of
vectors, whose physical source locations and materialized bytes match its selected request. -/
theorem openingValuePacketPublishedBySecondLoaderOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 15) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    OpeningValuePacketPublished p l X g batch :=
  (openingValueProgressBySecondLoader hp hMax hFrame hg hw hb hLo hHi).packet

private theorem openingValueProgressByFirstLoader {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    OpeningValueProgress p l X g batch (Loader.primingSearchShuffleCount batch+32) := by
  have writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame
  obtain ⟨_,_,_,hKeyRank,hKey⟩ :=
    selectedCacheKeyCommitOfMaximal hp hMax writes hg (by omega) hb hLo hHi
  obtain ⟨_,_,hQ1,_,_⟩ :=
    selectedOpeningBiasPacketWithRankOfMaximal hp hMax hFrame hg hw hb hLo hHi
  have hRank : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 <
      Loader.primingSearchShuffleCount batch+32 := by
    unfold Loader.primingSearchShuffleCount
    omega
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  obtain ⟨hQ1Entry,_,_⟩ :=
    Loader.openingSecondQueryExpectedFromCursorOfMaximal hp hMax hg hQ1
      (fun lane hl hBlocked => by
        have hSame := (Step.sameWarp_lane hBlock hg hl).1
        have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
        rw [hSame.1.2.2]
        exact Protocol.Loader.openingSecondQueryEmptyPhaseForBlockedLane
          hp hMax hSame.1.2.1 hWarp hBlocked)
  obtain ⟨hBias1,_⟩ :=
    Loader.selectedSecondBiasEntryOfMaximal hp hMax writes hg hw hb hLo hHi hRank hQ1Entry
  obtain ⟨hBiasEntry,_,_⟩ := Loader.openingSecondBiasExpectedOfMaximal hp hMax hg hBias1
    (fun lane hl hBlocked => by
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
      rw [hSame.1.2.2]
      exact Protocol.Bias.openingSecondBiasEmptyPhase hp hMax hSame.1.2.1 hWarp hBlocked)
  obtain ⟨_,⟨tail⟩⟩ :=
    Loader.openingSecondBiasBoxesAndTailOfMaximal hp hMax writes hg hw hb hLo hHi
      hRank hBiasEntry
  have hStart := Loader.openingValueReachedByFirstLoader hp hMax.1 hg hw (by omega) hKey tail
  obtain ⟨done,hWait⟩ := Loader.openingValueAcquiredOfReady hp hMax hg hStart
    (fun lane hl hQuiet => by
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hThis : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
      have hWarp : 14 ≤ warpIndex l (warpLane l g lane) := by rw [hThis]
      have hPhase := Protocol.Loader.cacheEmptyPhaseBeforeSlotPublication
        hp hMax hSame.1.2.1 hWarp 1 hQuiet
      simpa only [Thread.Mma.Observation.emptyObject,hSame.1.2.2] using hPhase)
  exact openingValuePacketPublishedOfAcquire hp hMax hFrame hg (by omega) hb hLo hHi
    hRank done hWait

/-- Each lane of warp 14 issues the opening V publication and all 16 pairs of
vectors, whose physical source locations and materialized bytes match its selected request. -/
theorem openingValuePacketPublishedByFirstLoaderOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    OpeningValuePacketPublished p l X g batch :=
  (openingValueProgressByFirstLoader hp hMax hFrame hg hw hb hLo hHi).packet

/-- Either loader warp of a single-visit tile advances from its actual opening
value publication into the terminal group scan. -/
theorem singleVisitLoaderDrainNeighborsOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    Nonempty (Thread.Loader.SingleVisitDrainNeighbors p l X g) := by
  by_cases hKey : warpIndex l g = 14
  · exact (openingValueProgressByFirstLoader hp hMax hFrame hg hKey hb hLo hHi).single
      hSingle
  · have hValue : warpIndex l g = 15 := by have := warpIndex_lt hp g; omega
    exact (openingValueProgressBySecondLoader hp hMax hFrame hg hValue hb hLo hHi).single hSingle

/-- Either scheduled loader begins its actual first warm cache iteration after publishing V. -/
theorem openingLoaderWarmCacheOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWarm : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    Nonempty (Thread.Loader.WarmCacheStarted p l X g batch) := by
  by_cases hKey : warpIndex l g = 14
  · obtain ⟨c,_⟩ :=
      (openingValueProgressByFirstLoader hp hMax hFrame hg hKey hb hLo hHi).warm hWarm
    exact ⟨c⟩
  · have hValue : warpIndex l g = 15 := by have := warpIndex_lt hp g; omega
    obtain ⟨c,_⟩ :=
      (openingValueProgressBySecondLoader hp hMax hFrame hg hValue hb hLo hHi).warm hWarm
    exact ⟨c⟩

/-- Warp fifteen reaches the first warm round at its exact opening shuffle rank. -/
theorem openingLoaderWarmCacheWithRankOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 15) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWarm : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    ∃ c : Thread.Loader.WarmCacheStarted p l X g batch,
      c.shuffles = Loader.primingSearchShuffleCount batch+64 :=
  (openingValueProgressBySecondLoader hp hMax hFrame hg hw hb hLo hHi).warm hWarm

/-- Warp fourteen reaches the first warm round at its exact opening shuffle rank. -/
theorem openingFirstLoaderWarmCacheWithRankOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWarm : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    ∃ c : Thread.Loader.WarmCacheStarted p l X g batch,
      c.shuffles = Loader.primingSearchShuffleCount batch+64 :=
  (openingValueProgressByFirstLoader hp hMax hFrame hg hw hb hLo hHi).warm hWarm

end PTX.Kernels.TmlFa4Fwd.Progress
