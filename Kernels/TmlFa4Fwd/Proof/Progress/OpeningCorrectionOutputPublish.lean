-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionOutputAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondFinalizationAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalPublicationMatch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction Protocol.Statistics

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
include hp hMax hOutputs hg hRole hb hLo hHi hSingle

/-- Every single-visit correction lane publishes the fully staged first output. -/
theorem singleVisitCorrectionFirstOutputPublishedOfMaximal :
    Nonempty (FirstOutputPublished p l X g batch) := by
  obtain ⟨c⟩ := singleVisitCorrectionFirstStageStagingOfMaximal hp hMax hOutputs hg hRole
    hb hLo hHi hSingle
  exact c.publishOfMaximal hp hMax hg

private theorem singleVisitSecondWaitOfMaximal :
    Nonempty (SecondTerminalWaitReached p l X g batch) := by
  obtain ⟨first⟩ := singleVisitCorrectionFirstOutputPublishedOfMaximal hp hMax hOutputs hg
    hRole hb hLo hHi hSingle
  exact first.secondWaitOfMaximal hp hMax hg

/-- Following the first stage, the actual second terminal wait and paired
softmax publication supply both of the second row's statistics. -/
theorem singleVisitCorrectionSecondTerminalWordsOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Nonempty (SecondTerminalWordsReady p l Y g batch) := by
  have hFrame := hOutputs X hMax.1
  have hCuQ := (hFrame.metadataProtected hp).1
  have hTrips : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2 := by omega
  obtain ⟨c⟩ := singleVisitSecondWaitOfMaximal hp hMax hOutputs hg hRole hb hLo hHi hSingle
  let j := c.first.published.cursor.pos
  apply c.readOfMaximal hp hMax hCuQ hg
  · intro hLast
    have hIndex : j = (X.tr g).length-1 := by omega
    have hWait : Thread.CorrectionWaits X (g,(X.tr g).length-1) .terminal 1 :=
      hIndex ▸ c.waited
    apply terminalSynchronizationReleasedOfCohorts hp hMax hCuQ hg hWait
    · intro peer hPeer hCta hWarp
      have hStage : warpIndex l peer/4 = (1 : Fin 2).val := by
        rw [hWarp]
        change (warpIndex l g%4+4*1)/4 = 1
        omega
      exact singleVisitSoftmaxTerminalPublicationOfMaximal hp hMax hFrame hPeer 1 hStage
        hb (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hTrips)
    · intro peer hPeer hCta hWarp
      have hCorr : 8 ≤ warpIndex l peer ∧ warpIndex l peer < 12 := by omega
      obtain ⟨r⟩ := singleVisitSecondWaitOfMaximal hp hMax hOutputs hPeer hCorr hb
        (hCta.symm ▸ hLo) (hCta.symm ▸ hHi) (hCta.symm ▸ hSingle)
      exact ⟨_,r.waited⟩
  · intro Y hY hTrace _ hPass
    have hFrameY := hOutputs Y hY.1
    obtain ⟨hCuQY,hUsedK⟩ := hFrameY.metadataProtected hp
    let producer := terminalStatsProducer l g 1
    have hOwner : producer/l.block = g/l.block := terminalStatsCta hp g 1
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    have hProducer : producer < l.threads :=
      (Nat.div_lt_iff_lt_mul hBlock).mp (hOwner.symm ▸ NamedBar.cta_lt hg)
    have hWarp : warpIndex l producer = (terminalStatsWarp l g 1).val :=
      terminalStatsProducerWarp hp g 1
    have hw : warpIndex l producer < 8 := hWarp.symm ▸ (terminalStatsWarp l g 1).isLt
    have hStage : warpIndex l producer/4 = (1 : Fin 2).val := by
      rw [hWarp]
      change (rowOf l g/32+4*1)/4 = 1
      have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
      omega
    obtain ⟨pos,sum,max,hFinal,hOrdinal,hSum,hMaxWord,hValid⟩ :=
      singleVisitSoftmaxTerminalWordsWithMassOfMaximal hp hY hFrameY hProducer 1 hStage hb
        (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrips)
    have hEqWarp : (⟨warpIndex l producer,hw⟩ : Fin 8) = terminalStatsWarp l g 1 := Fin.ext hWarp
    rw [hEqWarp] at hSum hMaxWord
    have hWords := terminalPublishedWordsOfActualWrites hp hY.1 1 hFinal hSum hMaxWord
    have hWait : Thread.CorrectionWaits Y (g,j) .terminal 1 := by
      obtain ⟨e,he,hAction⟩ := c.waited
      exact ⟨e,by simpa only [Execution.get,hTrace] using he,hAction⟩
    have hWork : g/l.block < tilePrefix p p.batch*p.heads := hHi.trans_le
      (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
    obtain ⟨other,ho,hoLo,hoHi,hWaitOrdinal⟩ :=
      terminalWaitOrdinalOfTrips hp hY.1 hWork hUsedK hWait
    have hSame : other = batch :=
      (tileBatch_existsUnique p hWork).unique ⟨ho,hoLo,hoHi⟩ ⟨hb,hLo,hHi⟩
    rw [hSame,hSingle,Thread.correctionBarrierOrdinal] at hWaitOrdinal
    have hId : 3+warpIndex l producer = statsBarrierId l g 1 :=
      (congrArg (3+·) hWarp).trans (terminalStatsBarrier l g 1)
    rw [Thread.Scores.notificationOrdinal hp hY.1 hw,Thread.Scores.observedOrdinal,hId] at hOrdinal
    have hGeneration := terminalPeerOfFinalPublication hp hY.1 hWait hPass hFinal
      (hOrdinal.trans hWaitOrdinal.symm)
    obtain ⟨key,ha,hs,_⟩ := hGeneration.sameGeneration
    refine ⟨pos+2,sum,max,hWords,⟨key,?_,hs⟩,hValid⟩
    rwa [Nat.add_sub_cancel]

/-- The second staged output has the actual row reciprocal and both of its
acquires, following the first row's output publication. -/
theorem singleVisitCorrectionSecondOutputLoadReadyOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Nonempty (SecondOutputLoadReady p l Y g batch) := by
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    singleVisitCorrectionSecondTerminalWordsOfMaximal hp hMax hOutputs hg hRole hb hLo hHi hSingle
  have hPhase := singleVisitTerminalOutputPhaseOfMaximal hp hY (hOutputs Y hY.1)
    (NamedBar.cta_lt hg) hb hLo hHi hSingle 1
  exact ⟨Y,hY,hTrace,hWrites,c.acquireSecondOutputOfMaximal hp hY hg hRole hPhase⟩

end PTX.Kernels.TmlFa4Fwd.Progress
