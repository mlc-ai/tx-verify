-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionStatistics
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxStatistics
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsProgressPeer
import Kernels.TmlFa4Fwd.Proof.Thread.FirstRescaleVoteOrdinal
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
import Kernels.TmlFa4Fwd.Proof.Protocol.Statistics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRepeat : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
include hp hMax hFrame hg hw hb hLo hHi hRepeat

/-- The first repeated correction rendezvous follows the initial stage-zero
arrival, its slot credit, and the initial stage-one arrival. Its generation is one. -/
theorem firstRescaleOrdinalsOfMaximal :
    ∃ d : Correction.FirstRescaleReached p l X g batch (laneOf l g),
      (∀ stage, observedBarrierOrdinal X (g,d.index) (Correction.statsBarrierId l g stage) = 1) ∧
      ((X.tr g).take d.index).countP isFullWarpVote = 1 ∧
      ((X.tr g).take d.index).countP isTcColl = 0 := by
  have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hReady {stage} (c : Correction.OpeningCorrectionStatistics p l X g batch (laneOf l g) stage)
      (hLast : c.index+1 = (X.tr (warpLane l g (laneOf l g))).length) :
      ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
        Step.Released l Y (warpLane l g (laneOf l g)) := by
    rw [hSelf] at hLast ⊢
    have he : (X.tr g).length-1 = c.index := by omega
    have hWait := c.waited
    rw [hSelf,← he] at hWait
    obtain ⟨Y,hY,ht,_,hr⟩ :=
      openingCorrectionStatisticsReadyOfMaximal hp hMax hFrame hg hw stage hb hLo hHi hWait
    exact ⟨Y,hY,ht,hr⟩
  obtain ⟨a⟩ := Correction.openingCorrectionFirstStatisticsOfMaximal hp hMax hg hw.1 hw.2
    ((hFrame.metadataProtected hp).1) hb hLo hHi
    ((hFrame.metadataProtected hp).2 batch hb) (laneOf l g) (Nat.mod_lt _ (by decide))
  obtain ⟨hCredit,b,hB⟩ := a.secondIndexedOfMaximal hp hMax (hSelf.symm ▸ hg) (hReady a)
  obtain ⟨d,hD⟩ := b.firstRescaleIndexedOfMaximal hp (hSelf.symm ▸ hg) hb hLo hHi hRepeat (hReady b)
  let w : Fin 8 := ⟨warpIndex l g%4,by have := Nat.mod_lt (warpIndex l g) (by decide : 0<4); omega⟩
  let id := Correction.statsBarrierId l g 0
  have hId : id = 3+w.val := by simp [id,w,Correction.statsBarrierId,Nat.add_comm]
  have ha := a.waited
  have hb' := b.waited
  rw [hSelf] at ha hb' hCredit
  have hv := Correction.firstRescaleVoteBase hp hMax.1 hg hw
    (hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))) hb'
  obtain ⟨e,he,hk⟩ := initialCorrectionStatisticsBarrier hp hMax.1 ha
  obtain ⟨f,hf,hj⟩ := initialCorrectionStatisticsBarrier hp hMax.1 hb'
  obtain ⟨pc,hc⟩ := hCredit
  have ho := correctionInitialWaitOrdinal hp hMax.1 ha (hId.symm ▸ statsBarrierSources hp hMax.1 w)
  rw [correctionBarrierOrdinal] at ho
  have ht := Correction.firstRescaleTensorBase hp hMax.1 hw hb'
  refine ⟨d,?_,by rwa [hD],by rwa [hD]⟩
  intro stage
  fin_cases stage
  · change observedBarrierOrdinal X (g,d.index) (Correction.statsBarrierId l g 0) = 1
    rw [hB] at hf
    rw [hD,hB]
    unfold observedBarrierOrdinal
    rw [countP_take_succ_false hf (by simp [Execution.isBarId,hj,Correction.statsBarrierId]),
      countP_take_succ_false hc (by rfl),countP_take_succ he (by simp [Execution.isBarId,hk]),ho]
  · change observedBarrierOrdinal X (g,d.index) (Correction.statsBarrierId l g 1) = 1
    let w' := Protocol.Statistics.waitingWarp l g 1
    have hId' : Correction.statsBarrierId l g 1 = 3+w'.val := by
      simp [w',Protocol.Statistics.waitingWarp,Correction.statsBarrierId,Nat.add_comm,
        Nat.add_left_comm]
    have hi := correctionInitialWaitOrdinal hp hMax.1 hb'
      (hId'.symm ▸ statsBarrierSources hp hMax.1 w')
    rw [correctionBarrierOrdinal] at hi
    rw [hD]
    unfold observedBarrierOrdinal
    rw [countP_take_succ hf (by simp [Execution.isBarId,hj]),hi]

end PTX.Kernels.TmlFa4Fwd.Progress
