-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminalWords
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityAck
import all Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionStatistics
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalPublicationMatch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open Correction Protocol.Statistics

/-- Both active cohorts of a single-visit tile reach the first final synchronization.
Each correction lane reads the actual terminal words from its paired softmax row. -/
theorem singleVisitCorrectionFirstTerminalWordsOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstTerminalWordsReady p l Y g batch (laneOf l g)) := by
  have hSelf : warpLane l g (laneOf l g) = g :=
    Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨second,hReady⟩ := secondStatisticsCursorWithRelease hp hMax hFrame hg hRole hb hLo hHi
  obtain ⟨_,⟨c⟩⟩ := second.firstTerminalCursorAndCreditOfMaximal hp hMax (hSelf.symm ▸ hg)
    hb hLo hHi hSingle hReady
  have hCuQ := (hFrame.metadataProtected hp).1
  apply c.readPublishedOfMaximal hp hMax hCuQ (hSelf.symm ▸ hg)
  · intro hLast
    rw [hSelf] at hLast ⊢
    have hIndex : c.index = (X.tr g).length-1 := by omega
    have hWait : Thread.CorrectionWaits X (g,(X.tr g).length-1) .terminal 0 := by
      simpa only [hSelf,hIndex] using c.waited
    apply terminalSynchronizationReleasedOfCohorts hp hMax hCuQ hg hWait
    · intro peer hPeer hCta hWarp
      have hStage : warpIndex l peer/4 = (0 : Fin 2).val := by
        rw [hWarp]
        change (warpIndex l g%4+4*0)/4 = 0
        omega
      exact singleVisitSoftmaxTerminalPublicationOfMaximal hp hMax hFrame hPeer 0 hStage
        hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
    · intro peer hPeer hCta hWarp
      have hCorr : 8 ≤ warpIndex l peer ∧ warpIndex l peer < 12 := by omega
      exact openingCorrectionFirstTerminalOfMaximal hp hMax hFrame hPeer hCorr hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
  · intro Y hY hTrace hWrites hPass
    rw [hSelf] at hPass ⊢
    have hFrameY : OutputFootprint p Y := by unfold OutputFootprint; rw [hWrites]; exact hFrame
    obtain ⟨hCuQY,hUsedK⟩ := hFrameY.metadataProtected hp
    let producer := terminalStatsProducer l g 0
    have hOwner : producer/l.block = g/l.block := terminalStatsCta hp g 0
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    have hProducer : producer < l.threads :=
      (Nat.div_lt_iff_lt_mul hBlock).mp (hOwner.symm ▸ NamedBar.cta_lt hg)
    have hWarp : warpIndex l producer = (terminalStatsWarp l g 0).val :=
      terminalStatsProducerWarp hp g 0
    have hw : warpIndex l producer < 8 := hWarp.symm ▸ (terminalStatsWarp l g 0).isLt
    have hStage : warpIndex l producer/4 = (0 : Fin 2).val := by
      rw [hWarp]
      change (rowOf l g/32+4*0)/4 = 0
      have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
      omega
    obtain ⟨pos,sum,max,hFinal,hOrdinal,hSum,hMaxWord,hValid⟩ :=
      singleVisitSoftmaxTerminalWordsWithMassOfMaximal hp hY hFrameY hProducer 0 hStage hb
        (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hSingle)
    have hEqWarp : (⟨warpIndex l producer,hw⟩ : Fin 8) = terminalStatsWarp l g 0 := Fin.ext hWarp
    rw [hEqWarp] at hSum hMaxWord
    have hWords := terminalPublishedWordsOfActualWrites hp hY.1 0 hFinal hSum hMaxWord
    have hWait : Thread.CorrectionWaits Y (g,c.index) .terminal 0 := by
      obtain ⟨e,he,hAction⟩ := c.waited
      exact ⟨e,by simpa only [Execution.get,hTrace,hSelf] using he,hAction⟩
    have hWork : g/l.block < tilePrefix p p.batch*p.heads := hHi.trans_le
      (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
    obtain ⟨other,ho,hoLo,hoHi,hWaitOrdinal⟩ :=
      terminalWaitOrdinalOfTrips hp hY.1 hWork hUsedK hWait
    have hSame : other = batch :=
      (tileBatch_existsUnique p hWork).unique ⟨ho,hoLo,hoHi⟩ ⟨hb,hLo,hHi⟩
    rw [hSame,Thread.correctionBarrierOrdinal] at hWaitOrdinal
    have hTrips : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1 := by
      have hTile := (assignedCoordinates_valid hp hLo hHi).1
      have hPos := (Mma.trips_bounds hp hb hTile).1
      omega
    have hId : 3+warpIndex l producer = statsBarrierId l g 0 :=
      (congrArg (3+·) hWarp).trans (terminalStatsBarrier l g 0)
    rw [Thread.Scores.notificationOrdinal hp hY.1 hw,Thread.Scores.observedOrdinal,hId] at hOrdinal
    have hGeneration := terminalPeerOfFinalPublication hp hY.1 hWait hPass hFinal
      (hOrdinal.trans (hWaitOrdinal.trans hTrips).symm)
    obtain ⟨key,ha,hs,_⟩ := hGeneration.sameGeneration
    refine ⟨pos+2,sum,max,hWords,⟨key,?_,hs⟩,hValid⟩
    rwa [Nat.add_sub_cancel]

end PTX.Kernels.TmlFa4Fwd.Progress
