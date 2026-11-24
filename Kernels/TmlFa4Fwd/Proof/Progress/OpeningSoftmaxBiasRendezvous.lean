-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxBiasReads
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasRendezvousProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg stage hRole hb hLo

/-- Every active softmax lane reaches its first post-load Bias rendezvous. -/
theorem openingSoftmaxBiasArrivalOfAllStages (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasArrivalLane p l X g batch stage j) := by
  obtain ⟨j,hAcquire,⟨loaded⟩⟩ := openingSoftmaxBiasReadsOfAllStages hp hMax hFrame
    hg stage hRole hb hLo hHi
  exact ⟨j,hAcquire,loaded.arrivalOfMaximal hp hMax hg⟩

/-- The first Bias rendezvous has received every participant. A lane either has
returned or can return in a maximal execution with the same trace and writes. -/
theorem openingSoftmaxBiasRendezvousOfAllStages (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasArrivalLane p l X g batch stage j) ∧
      (j+67 < (X.tr g).length ∨
        ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
          Y.MemWrites = X.MemWrites ∧ Step.Released l Y g) := by
  obtain ⟨j,hAcquire,⟨arrived⟩⟩ := openingSoftmaxBiasArrivalOfAllStages hp hMax hFrame
    hg stage hRole hb hLo hHi
  refine ⟨j,hAcquire,⟨arrived⟩,?_⟩
  by_cases hReturned : j+67 < (X.tr g).length
  · exact .inl hReturned
  right
  have hBound := len_of_get arrived.arrival
  have hLast : (X.tr g).length-1 = j+66 := by
    change j+66 < (X.tr g).length at hBound
    omega
  have hWait : BarrierArrival X (g,(X.tr g).length-1) (11+stage.val) (some 128) .sync := by
    rw [hLast]
    exact ⟨_,arrived.arrival,rfl⟩
  have hWork : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right p.heads
      (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hInitial : observedBarrierOrdinal X (g,(X.tr g).length-1) (11+stage.val) = 0 := by
    rw [hLast]
    exact arrived.initial
  rcases Protocol.Bias.firstSynchronizationFrontier hp hMax (hFrame.metadataProtected hp).1
    hg stage hWork hWait hInitial with hMissing | hReady
  · obtain ⟨lane,hLane,hMember,_,hZero⟩ := hMissing
    let peer := g/l.block*l.block+lane
    have hPeer : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
    have hCoord := NamedBar.lane_cta (c := g/l.block) (NamedBar.block_pos_of_thread_lt hg) hLane
    have hWarp : warpIndex l peer = lane/32 := by
      unfold warpIndex
      rw [show peer % l.block = lane from hCoord.2]
    have hPeerStage : warpIndex l peer/4 = stage.val :=
      hWarp.symm ▸ (Thread.biasParticipantIff stage (lane/32)).mp hMember |>.2
    have hOwner : peer/l.block = g/l.block := hCoord.1
    obtain ⟨k,_,⟨hArrived⟩⟩ := openingSoftmaxBiasArrivalOfAllStages hp hMax hFrame
      hPeer stage hPeerStage hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi)
    have hCounts := Thread.barrierArrivalExtent
      (show BarrierArrival X (peer,k+66) (11+stage.val) (some 128) .sync from
        ⟨_,hArrived.arrival,rfl⟩)
    exact ((Nat.not_lt_zero _) (hZero ▸ hCounts)).elim
  · exact hReady

end PTX.Kernels.TmlFa4Fwd.Progress
