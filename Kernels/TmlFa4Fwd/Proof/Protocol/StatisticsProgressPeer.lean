-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX Thread Prologue Epilogue

/-- An active softmax lane missing a demanded generation of its tile is still pending. -/
theorem missingProducerHasNotExited {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {producer batch generation : Nat} (hWarp : warpIndex l producer < 8)
    (hWork : producer / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch + 1) * p.heads)
    (hBound : generation ≤ Mma.trips p batch (assignedCoordinates p batch (producer/l.block)).1)
    (hMissing : (X.tr producer).countP (Execution.isBarId (3 + warpIndex l producer)) ≤
      generation) :
    ¬ Exited X producer := by
  rintro ⟨pos, e, he, hExit⟩
  have hOrd := ordinalBeforeActiveExit hp hX hCuQ (usedKProtected hp hX)
    hWarp hWork hb hLo hHi hBound he hExit
  rw [Scores.notificationOrdinal hp hX hWarp, Scores.barrierOrdinal] at hOrd
  exact (Nat.not_lt_of_ge hMissing) (hOrd.trans_le (List.take_sublist _ _).countP_le)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g : Nat}
include hp hMax hCuQ

/-- A correction wait whose generation is within the assigned tile has a still-live lagging
participant, or can release in a write-preserving maximal execution with the same traces. -/
theorem boundedSynchronizationFrontier (hg : g < l.threads) {stage : Fin 2}
    {round : CorrectionRound} (hWait : CorrectionWaits X (g,(X.tr g).length - 1) round stage)
    (w : Fin 8) (hPaired : w.val = warpIndex l g % 4 + 4 * stage.val) {batch : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hBound : (correctionBefore X (g,(X.tr g).length - 1)).barrier
      (Correction.statsBarrierId l g stage) ≤
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    (∃ lane < l.block, lane / 32 ∈ statsParticipants w ∧
      let peer := g / l.block * l.block + lane
      ¬ Exited X peer ∧ (X.tr peer).countP (Execution.isBarId (3 + w.val)) ≤
        observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val)) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  have hId : 3 + w.val = Correction.statsBarrierId l g stage := by
    rw [hPaired, Correction.statsBarrierId]
    omega
  rw [correctionBarrierOrdinal, ← hId] at hBound
  obtain ⟨_, ⟨event, hGet, hKind, _, _⟩, _⟩ := correctionWaits hp hMax.1 hWait
  rw [← hId] at hKind
  rcases synchronizationFrontier hp hMax hCuQ hg w ⟨event, hGet, hKind⟩ with hLag | hRelease
  · obtain ⟨lane, hLane, hMember, hCount⟩ := hLag
    refine .inl ⟨lane, hLane, hMember, ?_, hCount⟩
    let peer := g / l.block * l.block + lane
    have hCtaLane := NamedBar.lane_cta (c := g / l.block)
      (NamedBar.block_pos_of_thread_lt hg) hLane
    have hPeerCta : peer / l.block = g / l.block := hCtaLane.1
    have hPeerWarp : warpIndex l peer = lane / 32 := by
      unfold warpIndex
      rw [show peer % l.block = lane from hCtaLane.2]
    have hWork : peer / l.block < tilePrefix p p.batch * p.heads := by
      rw [hPeerCta]
      exact hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (by omega)))
    simp only [statsParticipants, Finset.mem_insert, Finset.mem_singleton] at hMember
    rcases hMember with hProducer | hCorrection
    · have hWarp := hPeerWarp.trans hProducer
      apply missingProducerHasNotExited hp hMax.1 hCuQ (producer := peer)
        (generation := observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val))
        (by rw [hWarp]; exact w.isLt) hWork hb (hPeerCta.symm ▸ hLo) (hPeerCta.symm ▸ hHi)
      · unfold observedBarrierOrdinal
        rwa [hPeerCta]
      · rwa [hWarp]
    · intro hExit
      have hWarp := hPeerWarp.trans hCorrection
      obtain ⟨pos, hTerminal⟩ := correctionStatsWaitOfActiveExit hp hMax.1
        (by omega) (by have := Nat.mod_lt w.val (by decide : 0 < 4); omega) hWork hExit true stage
      obtain ⟨picked, hPicked, hPLo, hPHi, hOrd⟩ :=
        Correction.terminalWaitOrdinalOfTrips hp hMax.1 hWork
          (usedKProtected hp hMax.1) hTerminal
      obtain ⟨_, _, hUnique⟩ := tileBatch_existsUnique p hWork
      have hBatch := (hUnique picked ⟨hPicked, hPLo, hPHi⟩).trans
        (hUnique batch ⟨hb, hPeerCta.symm ▸ hLo, hPeerCta.symm ▸ hHi⟩).symm
      have hSameId : Correction.statsBarrierId l peer stage = 3 + w.val := by
        unfold Correction.statsBarrierId
        rw [hWarp]
        have hLocal := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
        omega
      change (correctionBefore X (peer,pos)).barrier (Correction.statsBarrierId l peer stage) =
        _ at hOrd
      rw [correctionBarrierOrdinal, hSameId, hBatch, hPeerCta] at hOrd
      obtain ⟨_, ⟨e, he, hk, _, _⟩, _⟩ := correctionWaits hp hMax.1 hTerminal
      change e.kind = .bar (Correction.statsBarrierId l peer stage) (some 64) .sync at hk
      rw [hSameId] at hk
      have hArrived := barrierArrivalExtent (g := peer) (pos := pos) ⟨e, he, hk⟩
      unfold observedBarrierOrdinal at hCount hArrived
      exact (Nat.not_lt_of_ge (hCount.trans hBound)) (hOrd ▸ hArrived)
  · exact .inr hRelease

omit hp hMax hCuQ in
/-- The softmax warp paired with the correction lane for this output stage. -/
def waitingWarp (l : Launch) (g : Nat) (stage : Fin 2) : Fin 8 :=
  ⟨warpIndex l g % 4 + 4 * stage.val, by
    have hw := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
    have hs := stage.isLt
    omega⟩

/-- A terminal statistics wait releases after all peers reached the last generation; any lane
that still owes that arrival has not exited. -/
theorem terminalSynchronizationPending (hg : g < l.threads) {stage : Fin 2}
    (hWait : CorrectionWaits X (g,(X.tr g).length - 1) .terminal stage) :
    let w := waitingWarp l g stage
    (∃ lane < l.block, lane / 32 ∈ statsParticipants w ∧
      let peer := g / l.block * l.block + lane
      ¬ Exited X peer ∧ (X.tr peer).countP (Execution.isBarId (3 + w.val)) ≤
        observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val)) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  have hWork := Correction.terminalStatsWaitHasWork hp hMax.1 hWait
  obtain ⟨_, hb, hLo, hHi, hOrd⟩ := Correction.terminalWaitOrdinalOfTrips hp hMax.1 hWork
      (usedKProtected hp hMax.1) hWait
  exact boundedSynchronizationFrontier hp hMax hCuQ hg hWait (waitingWarp l g stage)
    rfl hb hLo hHi hOrd.le

/-- A rescale wait's actual cursor identifies its lagging live peer, or the wait can release. -/
theorem rescaleSynchronizationPending (hg : g < l.threads) {stage : Fin 2}
    (hWait : CorrectionWaits X (g,(X.tr g).length - 1) .rescale stage) :
    let w := waitingWarp l g stage
    (∃ lane < l.block, lane / 32 ∈ statsParticipants w ∧
      let peer := g / l.block * l.block + lane
      ¬ Exited X peer ∧ (X.tr peer).countP (Execution.isBarId (3 + w.val)) ≤
        observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val)) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  have hWork := Correction.statsWaitHasWork hp hMax.1 hWait
  obtain ⟨_, hb, hLo, hHi, hOrd⟩ := Correction.rescaleWaitOrdinalWithinTrips hp hMax.1 hWork
      (usedKProtected hp hMax.1) hWait
  exact boundedSynchronizationFrontier hp hMax hCuQ hg hWait (waitingWarp l g stage)
    rfl hb hLo hHi hOrd

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
