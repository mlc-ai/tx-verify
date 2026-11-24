-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsProgressPeer
import Kernels.TmlFa4Fwd.Proof.SoftmaxExitPublications

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX Thread Prologue Epilogue

/-- Terminal arrivals in both cohorts advance the last statistics generation, with
the original traces and writes unchanged. The participants' generations are
identified by their common assigned tile, independently of the number of visits. -/
theorem terminalSynchronizationReleasedOfCohorts {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (hg : g < l.threads)
    {stage : Fin 2} (hWait : CorrectionWaits X (g,(X.tr g).length-1) .terminal stage)
    (hFinal : ∀ peer < l.threads, peer/l.block = g/l.block →
      warpIndex l peer = (waitingWarp l g stage).val → ∃ j, Scores.Publishes X (peer,j) .final)
    (hTerminal : ∀ peer < l.threads, peer/l.block = g/l.block →
      warpIndex l peer = 8 + (waitingWarp l g stage).val % 4 →
      ∃ j, CorrectionWaits X (peer,j) .terminal stage) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  let w := waitingWarp l g stage
  have hId : 3+w.val = Correction.statsBarrierId l g stage := by
    change 3 + (warpIndex l g % 4 + 4*stage.val) = Correction.statsBarrierId l g stage
    unfold Correction.statsBarrierId
    omega
  have hUsedK := usedKProtected hp hMax.1
  have hWork : g/l.block < tilePrefix p p.batch*p.heads :=
    Correction.terminalStatsWaitHasWork hp hMax.1 hWait
  obtain ⟨batch,hBatch,hLo,hHi,hOrd⟩ :=
    Correction.terminalWaitOrdinalOfTrips hp hMax.1 hWork hUsedK hWait
  have hUnique {other : Nat}
      (h : other < p.batch ∧ tilePrefix p other * p.heads ≤ g/l.block ∧
        g/l.block < tilePrefix p (other+1) * p.heads) : other = batch :=
    (tileBatch_existsUnique p hWork).unique h ⟨hBatch,hLo,hHi⟩
  have hOrdinal : observedBarrierOrdinal X (g,(X.tr g).length-1) (3+w.val) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    rw [correctionBarrierOrdinal,← hId] at hOrd
    exact hOrd
  rcases terminalSynchronizationPending hp hMax hCuQ hg hWait with hMissing | hRelease
  · obtain ⟨lane,hl,hm,_,hMissing⟩ := hMissing
    let peer := g/l.block*l.block+lane
    have hPeer : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hl
    have hPos := NamedBar.lane_cta (c := g/l.block) (NamedBar.block_pos_of_thread_lt hg) hl
    have hCta : peer/l.block = g/l.block := hPos.1
    have hWarp : warpIndex l peer = lane/32 := by
      rw [warpIndex,show peer % l.block = lane from hPos.2]
    have hPeerWork : peer/l.block < tilePrefix p p.batch*p.heads := hCta.symm ▸ hWork
    have hw : lane/32 = w.val ∨ lane/32 = 8+w.val%4 := by
      simpa only [statsParticipants,Finset.mem_insert,Finset.mem_singleton] using hm
    rw [hOrdinal] at hMissing
    rcases hw with hSoft | hCorr
    · have hPaired := hWarp.trans hSoft
      have hwLt : warpIndex l peer < 8 := hPaired ▸ w.isLt
      obtain ⟨j,hj⟩ := hFinal peer hPeer hCta hPaired
      obtain ⟨other,ho,hoLo,hoHi,hLower⟩ :=
        Softmax.finalPublicationOrdinalLower hp hMax.1 hwLt hPeerWork hCuQ hUsedK hj
      rw [hCta] at hoLo hoHi hLower
      have hSame : other = batch := hUnique ⟨ho,hoLo,hoHi⟩
      rw [hSame,Scores.notificationOrdinal hp hMax.1 hwLt,Scores.barrierOrdinal,hPaired] at hLower
      obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := Scores.publishes hp hMax.1 hj
      rw [hPaired] at hKind
      exact (Nat.not_le_of_lt (hLower.trans_lt (barrierArrivalExtent ⟨e,he,hKind⟩)) hMissing).elim
    · have hPaired := hWarp.trans hCorr
      obtain ⟨j,hj⟩ := hTerminal peer hPeer hCta hPaired
      obtain ⟨other,ho,hoLo,hoHi,hExact⟩ :=
        Correction.terminalWaitOrdinalOfTrips hp hMax.1 hPeerWork hUsedK hj
      rw [hCta] at hoLo hoHi hExact
      have hSame : other = batch := hUnique ⟨ho,hoLo,hoHi⟩
      have hEq : Correction.statsBarrierId l peer stage = 3+w.val := by
        unfold Correction.statsBarrierId
        rw [hPaired]
        have hs := stage.isLt
        have hW : w.val = warpIndex l g % 4 + 4*stage.val := rfl
        omega
      rw [hSame,correctionBarrierOrdinal,hEq] at hExact
      obtain ⟨_,⟨e,he,hKind,_,_⟩,_⟩ := correctionWaits hp hMax.1 hj
      rw [hEq] at hKind
      exact (Nat.not_le_of_lt ((Eq.le hExact.symm).trans_lt (barrierArrivalExtent ⟨e,he,hKind⟩))
        hMissing).elim
  · exact hRelease

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
