-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCorrectionStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondFinalizationAcquire
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalPublicationMatch
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Correction Protocol.Statistics

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {g batch : Nat}
    (hg : g < l.threads) (hRole : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) {issuer : Nat}
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer)
include hp hMax hOutputs hg hRole hb hLo hHi multiple rows cta issues

/-- Following the first stage, the actual second terminal wait and paired
softmax publication supply both of the second row's statistics. -/
theorem repeatedCorrectionSecondTerminalWordsOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Nonempty (SecondTerminalWordsReady p l Y g batch) := by
  have hFrame := hOutputs X hMax.1
  have hCuQ := (hFrame.metadataProtected hp).1
  have reached (h : Nat) (hh : h < l.threads) (w : 8 ≤ warpIndex l h ∧ warpIndex l h < 12)
      (hc : g/l.block = h/l.block) : Nonempty (SecondTerminalWaitReached p l X h batch) := by
    obtain ⟨staging⟩ := repeatedFirstStageStagingOfRows hp hMax hOutputs hh w hb
      (hc ▸ hLo) (hc ▸ hHi) (hc ▸ multiple) (hc ▸ rows) (cta.trans hc) issues
    obtain ⟨published⟩ := staging.publishOfMaximal hp hMax hh
    exact published.secondWaitOfMaximal hp hMax hh
  obtain ⟨c⟩ := reached g hg hRole rfl
  let j := c.first.published.cursor.pos
  apply c.readOfMaximal hp hMax hCuQ hg
  · intro hLast
    have hIndex : j = (X.tr g).length-1 := by omega
    have hWait : Thread.CorrectionWaits X (g,(X.tr g).length-1) .terminal 1 :=
      hIndex ▸ c.waited
    apply terminalSynchronizationReleasedOfCohorts hp hMax hCuQ hg hWait
    · intro peer hPeer hCta hWarp
      obtain ⟨_,_,_,pub,_⟩ := rows peer hPeer hCta (waitingWarp l g 1) hWarp
      exact ⟨_,pub⟩
    · intro peer hPeer hCta hWarp
      have hCorr : 8 ≤ warpIndex l peer ∧ warpIndex l peer < 12 := by omega
      obtain ⟨r⟩ := reached peer hPeer hCorr hCta.symm
      exact ⟨_,r.waited⟩
  · intro Y hY hTrace _ hPass
    have hFrameY := hOutputs Y hY.1
    obtain ⟨-,hUsedK⟩ := hFrameY.metadataProtected hp
    let producer := terminalStatsProducer l g 1
    have hOwner : producer/l.block = g/l.block := terminalStatsCta hp g 1
    have hBlock : 0 < l.block := by rw [hp.block]; decide
    have hProducer : producer < l.threads :=
      (Nat.div_lt_iff_lt_mul hBlock).mp (hOwner.symm ▸ NamedBar.cta_lt hg)
    have hWarp : warpIndex l producer = (terminalStatsWarp l g 1).val :=
      terminalStatsProducerWarp hp g 1
    obtain ⟨pos,sum,max,hFinal,hOrdinal,hSum,hMaxWord,hValid⟩ :=
      (rows.ofTrace hTrace) producer hProducer hOwner _ hWarp
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
    rw [hSame,Thread.correctionBarrierOrdinal] at hWaitOrdinal
    have hId : 3+warpIndex l producer = statsBarrierId l g 1 :=
      (congrArg (3+·) hWarp).trans (terminalStatsBarrier l g 1)
    rw [hId] at hOrdinal
    have hGeneration := terminalPeerOfFinalPublication hp hY.1 hWait hPass hFinal
      (hOrdinal.trans hWaitOrdinal.symm)
    obtain ⟨key,ha,hs,_⟩ := hGeneration.sameGeneration
    refine ⟨pos+2,sum,max,hWords,⟨key,?_,hs⟩,hValid⟩
    rwa [Nat.add_sub_cancel]

/-- The second staged output has the actual row reciprocal and both of its
acquires, following the first row's output publication. -/
theorem repeatedCorrectionSecondOutputLoadReadyOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Nonempty (SecondOutputLoadReady p l Y g batch) := by
  obtain ⟨Y,hY,hTrace,hWrites,⟨c⟩⟩ :=
    repeatedCorrectionSecondTerminalWordsOfMaximal hp hMax hOutputs hg hRole hb hLo hHi
      multiple rows cta issues
  have hPhase := outputPhaseOfTerminalIssues hp hY (hOutputs Y hY.1) hTrace cta issues 1
  exact ⟨Y,hY,hTrace,hWrites,c.acquireSecondOutputOfMaximal hp hY hg hRole hPhase⟩

end PTX.Kernels.TmlFa4Fwd.Progress
