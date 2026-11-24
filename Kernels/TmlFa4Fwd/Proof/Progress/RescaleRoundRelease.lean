-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsProgressPeer
public import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- A reached correction warp can return from either stage in any generation
once each paired producer has published for that generation. -/
theorem rescaleReleaseOfWarpPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g gen : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (stage : Fin 2)
    (joined : ∀ peer, SameWarp l g peer → ∃ i, CorrectionWaits X (peer,i) .rescale stage ∧
      observedBarrierOrdinal X (peer,i) (Correction.statsBarrierId l peer stage) = gen)
    (published : ∀ peer < l.threads, peer/l.block = g/l.block →
      warpIndex l peer = (Protocol.Statistics.waitingWarp l g stage).val →
      ∃ i round, Scores.Publishes X (peer,i) round ∧
        gen ≤ observedBarrierOrdinal X (peer,i) (3+warpIndex l peer))
    {i : Nat} (wait : CorrectionWaits X (g,i) .rescale stage)
    (ord : observedBarrierOrdinal X (g,i) (Correction.statsBarrierId l g stage) = gen)
    (last : i+1 = (X.tr g).length) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  have hi : (X.tr g).length-1 = i := by omega
  rcases Protocol.Statistics.rescaleSynchronizationPending hp hMax hCuQ hg (hi ▸ wait) with
    ⟨lane,hl,hm,_,hc⟩ | done
  · let peer := g/l.block*l.block+lane
    have ht : peer < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hl
    obtain ⟨hC,hL⟩ := NamedBar.lane_cta (c := g/l.block) (by rw [hp.block]; decide) hl
    change peer/l.block = g/l.block at hC
    have hW : warpIndex l peer = lane/32 := by rw [warpIndex,hL]
    have hId : 3+(Protocol.Statistics.waitingWarp l g stage).val =
        Correction.statsBarrierId l g stage := by
      simp [Protocol.Statistics.waitingWarp,Correction.statsBarrierId,
        Nat.add_comm,Nat.add_left_comm]
    rw [hi,hId,ord] at hc
    change (X.tr peer).countP _ ≤ gen at hc
    simp only [statsParticipants,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h
    · have hw' := hW.trans h
      obtain ⟨idx,round,hPub,hOrd⟩ := published peer ht hC hw'
      obtain ⟨_,⟨ev,he,hKind,_,_⟩,_⟩ := Scores.publishes hp hMax.1 hPub
      have ex := barrierArrivalExtent (show BarrierArrival X (peer,idx) (3+warpIndex l peer)
        (some 64) .arrive from ⟨ev,he,hKind⟩)
      have low := hOrd.trans_lt ex
      rw [hw',hId] at low
      exact (Nat.not_lt_of_ge hc low).elim
    · have stageLt := stage.isLt
      have modLt := Nat.mod_lt (warpIndex l g) (by decide : 0 < 4)
      have same : warpIndex l peer = warpIndex l g := by
        simp only [Protocol.Statistics.waitingWarp] at h
        omega
      obtain ⟨idx,hwj,ho⟩ := joined peer ⟨⟨hg,ht,hC.symm⟩,same.symm⟩
      obtain ⟨_,⟨ev,he,hKind,_,_⟩,_⟩ := correctionWaits hp hMax.1 hwj
      have ex := barrierArrivalExtent (show BarrierArrival X (peer,idx)
          (Correction.statsBarrierId l peer stage) (some 64) .sync from ⟨ev,he,hKind⟩)
      rw [ho] at ex
      simp only [Correction.statsBarrierId,same] at ex hc
      exact (Nat.not_lt_of_ge hc ex).elim
  · exact done

end PTX.Kernels.TmlFa4Fwd.Progress
