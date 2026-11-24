-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionTerminalWords
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTerminalOutputPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstNormalizedChunk
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionVectorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionFirstStageStaging
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Lemmas.Step.WarpLanes
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleStoreValues
import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsCredit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
include hp hMax hFrame hg hRole hb hLo hHi hSingle

/-- A single-visit correction lane consumes both terminal statistics words,
returns their credit, and acquires the completed first accumulator. -/
theorem singleVisitCorrectionFirstOutputOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstOutputAcquired p l Y g batch (laneOf l g)) := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionFirstTerminalWordsOfMaximal hp hMax hFrame hg hRole hb hLo hHi
      (hSingle ▸ (by decide : 1 < 2))
  have hFrameY : OutputFootprint p Y := by unfold OutputFootprint; rw [hWrites]; exact hFrame
  have hPhase := singleVisitTerminalOutputPhaseOfMaximal hp hY hFrameY (NamedBar.cta_lt hg)
    hb hLo hHi hSingle 0
  exact ⟨Y,hY,hTrace,hWrites,c.acquireFirstOutputOfMaximal hp hY (hSelf.symm ▸ hg)
    (by simpa only [hSelf] using hPhase)⟩

/-- Every single-visit correction row issues its first accumulator load with
its actual reciprocal and staging acquire already recorded. -/
theorem singleVisitCorrectionFirstLoadOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstOutputLoadIssued p l Y g batch (laneOf l g)) := by
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionFirstOutputOfMaximal hp hMax hFrame hg hRole hb hLo hHi hSingle
  have hFrameY : OutputFootprint p Y := by unfold OutputFootprint; rw [hWrites]; exact hFrame
  have hCuQ := (hFrameY.metadataProtected hp).1
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact ⟨Y,hY,hTrace,hWrites,c.issueLoadOfMaximal hp hY (syncGuarded hp hY.1 hCuQ)
    (Mma.actualMmaLayoutInjective hY.1) (hSelf.symm ▸ hg) (hSelf.symm ▸ hRole)⟩

/-- The first accumulator issue of every lane has its warp dependencies when
the lane's recorded trace ends at that issue. -/
theorem singleVisitCorrectionFirstLoadReleasedOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      ∃ issued : FirstOutputLoadIssued p l Y g batch (laneOf l g),
        (issued.loadCursor.pos+1 = (Y.tr g).length → Step.Released l Y g) := by
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionFirstLoadOfMaximal hp hMax hFrame hg hRole hb hLo hHi hSingle
  have hFrameY : OutputFootprint p Y := by unfold OutputFootprint; rw [hWrites]; exact hFrame
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hRank := c.ordinal hp hY.1 hFrameY (hSelf.symm ▸ hRole)
    hb (hSelf.symm ▸ hLo) (hSelf.symm ▸ hHi) (hSelf.symm ▸ hSingle)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hPeers : ∀ peer ∈ warpLanes l g, ∃ k, Y.TcK (peer,k) 0 := by
    intro peer hPeer
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hPeer
    have hl := (List.mem_range.mp hLane).trans_le (min_le_left _ _)
    obtain ⟨hWarp,_⟩ := Step.sameWarp_lane hBlock hg hl
    let peer := warpLane l g lane
    have hg' : peer < l.threads := hWarp.1.2.1
    have hCta : g/l.block = peer/l.block := hWarp.1.2.2
    have hWarpIndex : warpIndex l g = warpIndex l peer := hWarp.2
    have hRole' : 8 ≤ warpIndex l peer ∧ warpIndex l peer < 12 := hWarpIndex ▸ hRole
    obtain ⟨Z,hZ,hTr,hMW,⟨d⟩⟩ :=
      singleVisitCorrectionFirstLoadOfMaximal hp hY hFrameY hg' hRole' hb
        (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hSingle)
    have hFrameZ : OutputFootprint p Z := by unfold OutputFootprint; rw [hMW]; exact hFrameY
    have hSelf' : warpLane l peer (laneOf l peer) = peer := Step.warpLane_of_sameWarp
      ⟨⟨hg',hg',rfl⟩,rfl⟩
    have hK := d.ordinal hp hZ.1 hFrameZ (hSelf'.symm ▸ hRole') hb
      (hSelf'.symm ▸ hCta ▸ hLo) (hSelf'.symm ▸ hCta ▸ hHi) (hSelf'.symm ▸ hCta ▸ hSingle)
    refine ⟨d.loadCursor.pos,?_⟩
    simpa only [Execution.TcK,Execution.get,hTr,hSelf'] using hK
  exact ⟨Y,hY,hTrace,hWrites,c,by
    simpa only [hSelf] using c.released hRank (by simpa only [hSelf] using hPeers)⟩
end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
include hp hMax hOutputs hg hRole hb hLo hHi hSingle

/-- A single-visit correction row computes its first eight normalized values
from the actual load, explicit warp wait and terminal statistics. -/
theorem singleVisitCorrectionFirstNormalizedOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstNormalizedChunk p l Y g batch (laneOf l g)) := by
  obtain ⟨Y,hY,hTrace,hWrites,c,hReleased⟩ :=
    singleVisitCorrectionFirstLoadReleasedOfMaximal hp hMax (hOutputs X hMax.1) hg hRole
      hb hLo hHi hSingle
  have hFrame := hOutputs Y hY.1
  have hCuQ := (hFrame.metadataProtected hp).1
  have hOperands := Safety.mmaOperandsOfProbabilities hp hY.1 hFrame
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hY.1 hOutputs)
  have hRescale := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hY.1 hOutputs
  have hValues := Safety.mmaCompletedValuesOfOperandsAndRescaleStores hp hY.1 hCuQ
    hOperands hRescale
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact ⟨Y,hY,hTrace,hWrites,c.normalizeOfMaximal hp hY hCuQ hValues (hSelf.symm ▸ hg)
    (by simpa only [hSelf] using hReleased)⟩

/-- All explicit waits of the single-visit warp are recorded at the same ordinal. -/
theorem singleVisitCorrectionFirstNormalizedReleasedOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      ∃ c : FirstNormalizedChunk p l Y g batch (laneOf l g),
        (c.source.loadCursor.pos+2 = (Y.tr g).length → Step.Released l Y g) := by
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionFirstNormalizedOfMaximal hp hMax hOutputs hg hRole hb hLo hHi hSingle
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hRank := c.waitOrdinal hp hY.1 (hOutputs Y hY.1) (hSelf.symm ▸ hRole)
    hb (hSelf.symm ▸ hLo) (hSelf.symm ▸ hHi) (hSelf.symm ▸ hSingle)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hPeers : ∀ peer ∈ warpLanes l g, ∃ k, Y.TcK (peer,k) 1 := by
    intro peer hPeer
    obtain ⟨lane,hLane,rfl⟩ := List.mem_map.mp hPeer
    have hl := (List.mem_range.mp hLane).trans_le (min_le_left _ _)
    obtain ⟨hWarp,_⟩ := Step.sameWarp_lane hBlock hg hl
    let peer := warpLane l g lane
    have hg' : peer < l.threads := hWarp.1.2.1
    have hCta : g/l.block = peer/l.block := hWarp.1.2.2
    have hWarpIndex : warpIndex l g = warpIndex l peer := hWarp.2
    have hRole' : 8 ≤ warpIndex l peer ∧ warpIndex l peer < 12 := hWarpIndex ▸ hRole
    obtain ⟨Z,hZ,hTr,_,⟨d⟩⟩ := singleVisitCorrectionFirstNormalizedOfMaximal hp hY hOutputs
      hg' hRole' hb (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hSingle)
    have hSelf' : warpLane l peer (laneOf l peer) = peer := Step.warpLane_of_sameWarp
      ⟨⟨hg',hg',rfl⟩,rfl⟩
    have hK := d.waitOrdinal hp hZ.1 (hOutputs Z hZ.1) (hSelf'.symm ▸ hRole') hb
      (hSelf'.symm ▸ hCta ▸ hLo) (hSelf'.symm ▸ hCta ▸ hHi) (hSelf'.symm ▸ hCta ▸ hSingle)
    refine ⟨d.source.loadCursor.pos+1,?_⟩
    simpa only [Execution.TcK,Execution.get,hTr,hSelf'] using hK
  exact ⟨Y,hY,hTrace,hWrites,c,by
    simpa only [hSelf] using c.waitReleased hRank (by simpa only [hSelf] using hPeers)⟩

/-- The live first finalization step stages all eight words and reaches the
next output chunk in every single-visit correction lane. -/
theorem singleVisitCorrectionFirstStagedChunkOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstStagedChunk p l Y g batch (laneOf l g)) := by
  obtain ⟨Y,hY,hTrace,hWrites,c,hRelease⟩ :=
    singleVisitCorrectionFirstNormalizedReleasedOfMaximal hp hMax hOutputs hg hRole
      hb hLo hHi hSingle
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  exact ⟨Y,hY,hTrace,hWrites,c.stageChunkOfMaximal hp hY
    (hSelf.symm ▸ hg) (hSelf.symm ▸ hRole.2) (by simpa only [hSelf] using hRelease)⟩

/-- Every correction lane in a single-visit tile stages the entire first
normalized result, including the terminal eight-column chunk. -/
theorem singleVisitCorrectionFirstStageStagingOfMaximal :
    Nonempty (FirstStageStagingDone p l X g batch) := by
  have hFrame := hOutputs X hMax.1
  have hCuQ := (hFrame.metadataProtected hp).1
  have hOperands := Safety.mmaOperandsOfProbabilities hp hMax.1 hFrame
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hMax.1 hOutputs)
  have hRescale := Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hMax.1 hOutputs
  have hValues := Safety.mmaCompletedValuesOfOperandsAndRescaleStores hp hMax.1 hCuQ
    hOperands hRescale
  apply firstStageStagingOfMaximal hp hMax hFrame hValues hRole hb hLo hHi hSingle _ g
    ⟨⟨hg,hg,rfl⟩,rfl⟩
  intro lane hw
  have hCta := hw.1.2.2
  have hWarp : warpIndex l g = warpIndex l lane := hw.2
  obtain ⟨Y,_,ht,_,hFirst⟩ :=
    singleVisitCorrectionFirstStagedChunkOfMaximal hp hMax hOutputs hw.1.2.1 (hWarp ▸ hRole)
      hb (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hSingle)
  exact ⟨Y,ht,hFirst⟩
end

private theorem singleVisitCorrectionFirstTerminalCredit
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads)
    (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∃ j e, X.get (g,j) = some e ∧ Thread.correctionAction e = some (.statsCredit 0) ∧
      (Thread.correctionBefore X (g,j)).count (.statsCredit 0) = 1 := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionFirstTerminalWordsOfMaximal hp hMax hFrame hg hRole hb hLo hHi
      (hSingle ▸ (by decide : 1 < 2))
  have hFrameY : OutputFootprint p Y := by unfold OutputFootprint; rw [hWrites]; exact hFrame
  obtain ⟨hCuQ,hUsedK⟩ := hFrameY.metadataProtected hp
  have hWork : g/l.block < tilePrefix p p.batch*p.heads := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  have hWait : Thread.CorrectionWaits Y (g,c.waitIndex) .terminal 0 := by
    simpa only [hSelf] using c.waited
  obtain ⟨other,ho,hoLo,hoHi,hOrd⟩ :=
    terminalWaitOrdinalOfTrips hp hY.1 hWork hUsedK hWait
  have hSame : other = batch :=
    (tileBatch_existsUnique p hWork).unique ⟨ho,hoLo,hoHi⟩ ⟨hb,hLo,hHi⟩
  rw [hSame,hSingle] at hOrd
  obtain ⟨e,he,hAction,hRank⟩ := c.creditObservationOfMaximal hp hY (hSelf.symm ▸ hg)
    (hSelf.symm ▸ hRole) (by simpa only [hSelf] using hOrd)
  have hGet : X.get (g,c.cursor.pos) = some e := by
    simpa only [Execution.get,hSelf,hTrace] using he
  have hCount : (Thread.correctionBefore Y (g,c.cursor.pos)).count (.statsCredit 0) = 1 := by
    simpa only [hSelf] using hRank
  rw [Thread.correctionBefore_count,hTrace] at hCount
  exact ⟨c.cursor.pos,e,hGet,hAction,(Thread.correctionBefore_count ..).trans hCount⟩

/-- Every correction participant in a single-visit CTA returns the terminal
credit to the first statistics cohort, at generation one. -/
theorem singleVisitFirstTerminalCreditsOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {cta batch : Nat} (hCta : cta < l.grid) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta) (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) :
    Protocol.Statistics.TerminalCorrectionCredits l X cta 0 1 := by
  intro lane
  let g := statsCreditLane l cta lane
  have hLane : 256+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have hg : g < l.threads := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using NamedBar.cta_thread_lt hCta hLane
  obtain ⟨hOwner,hLocal⟩ := NamedBar.lane_cta (c := cta)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  have hSame : g/l.block = cta := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using hOwner
  have hLocal' : g%l.block = 256+lane.val := by
    simpa only [g,statsCreditLane,Nat.add_assoc] using hLocal
  have hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold warpIndex
    rw [hLocal']
    have := lane.isLt
    omega
  exact singleVisitCorrectionFirstTerminalCredit hp hMax hFrame hg hRole hb
    (hSame.symm ▸ hLo) (hSame.symm ▸ hHi) (hSame.symm ▸ hSingle)

end PTX.Kernels.TmlFa4Fwd.Progress
