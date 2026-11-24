-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleLoopTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionTerminalWords
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalPublicationMatch
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread
open _root_.PTX.Kernels.TmlFa4Fwd.Correction Protocol.Statistics

/-- Published row statistics and their generation at the end of the softmax loop. -/
def TerminalRowPublications (l : Launch) (X : Execution) (cta trips : Nat) : Prop :=
  ∀ h < l.threads, h/l.block = cta → ∀ w : Fin 8, warpIndex l h = w.val →
    ∃ pos sum maximum, Scores.Publishes X (h,pos+2) .final ∧
      observedBarrierOrdinal X (h,pos+2) (3+warpIndex l h) = trips ∧
      X.Writes (h,pos) (Softmax.statsAcc l h w 2) (fl sum).toBytes ∧
      X.Writes (h,pos+1) (Softmax.statsAcc l h w 3) (Softmax.scoreValue maximum).toBytes ∧
      Softmax.DenominatorValid sum maximum

theorem TerminalRowPublications.ofTrace {l : Launch} {X Y : Execution} {cta trips : Nat}
    (rows : TerminalRowPublications l X cta trips) (trace : Y.tr = X.tr) :
    TerminalRowPublications l Y cta trips := by
  simpa only [TerminalRowPublications,Scores.Publishes,Execution.get,Execution.Writes,
    observedBarrierOrdinal,trace] using rows

theorem TerminalRowPublications.rescale {l : Launch} {X : Execution} {g trips : Nat}
    (rows : TerminalRowPublications l X (g/l.block) trips) :
    RepeatedStatisticsPublished l X g trips := by
  intro gen _ bound stage h hg hc hw
  obtain ⟨pos,_,_,pub,ord,_⟩ := rows h hg hc (waitingWarp l g stage) hw
  exact ⟨_,_,pub,bound.le.trans ord.symm.le⟩

/-- Terminal publications from a repeated tile suffice for correction to read
the actual final sum and maximum from its matching producer generation. -/
theorem repeatedFirstTerminalWordsOfRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.MemWrites = X.MemWrites ∧
      Nonempty (FirstTerminalWordsReady p l Y g batch (laneOf l g)) := by
  obtain ⟨_,_,⟨warp⟩⟩ :=
    repeatedCorrectionTerminalWarpOfPublications hp hMax hFrame hg hw hb hLo hHi
      multiple rows.rescale
  have self : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  let c := warp.lane g self
  have own (h : Nat) (hh : h < l.threads) : warpLane l h (laneOf l h) = h :=
    Step.warpLane_of_sameWarp ⟨⟨hh,hh,rfl⟩,rfl⟩
  apply c.readPublishedOfMaximal hp hMax ((hFrame X hMax.1).metadataProtected hp).1
    ((own g hg).symm ▸ hg)
  · intro last
    rw [own g hg] at last ⊢
    have idx : (X.tr g).length-1 = c.index := by omega
    have wait := c.waited
    rw [own g hg,← idx] at wait
    apply terminalSynchronizationReleasedOfCohorts hp hMax
      ((hFrame X hMax.1).metadataProtected hp).1 hg wait
    · intro h hh hc hW
      obtain ⟨_,_,_,pub,_⟩ := rows h hh hc (waitingWarp l g 0) hW
      exact ⟨_,pub⟩
    · intro h hh hc hW
      have w : warpIndex l g = warpIndex l h := by
        simp only [waitingWarp] at hW
        omega
      have hs : SameWarp l g h := ⟨⟨hg,hh,hc.symm⟩,w⟩
      exact ⟨_,by simpa only [own h hh] using (warp.lane h hs).waited⟩
  · intro Y hY tr _ pass
    rw [own g hg] at pass ⊢
    let h := terminalStatsProducer l g 0
    have hc : h/l.block = g/l.block := terminalStatsCta hp g 0
    have hh : h < l.threads :=
      (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).mp (hc.symm ▸ NamedBar.cta_lt hg)
    have w := terminalStatsProducerWarp hp g 0
    obtain ⟨pos,sum,maximum,pub,ord,hs,hm,valid⟩ := (rows.ofTrace tr) h hh hc _ w
    have words := terminalPublishedWordsOfActualWrites hp hY.1 0 pub hs hm
    have wait : CorrectionWaits Y (g,c.index) .terminal 0 := by
      simpa only [CorrectionWaits,Execution.get,tr,own g hg] using c.waited
    have active := hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p hb))
    obtain ⟨-,hk⟩ := (hFrame Y hY.1).metadataProtected hp
    obtain ⟨b,ok,lo,hi,ho⟩ := terminalWaitOrdinalOfTrips hp hY.1 active hk wait
    have same := (tileBatch_existsUnique p active).unique ⟨ok,lo,hi⟩ ⟨hb,hLo,hHi⟩
    rw [same,correctionBarrierOrdinal] at ho
    have id : 3+warpIndex l h = statsBarrierId l g 0 :=
      (congrArg (3+·) w).trans (terminalStatsBarrier l g 0)
    rw [id] at ord
    have matched := terminalPeerOfFinalPublication hp hY.1 wait pass pub (ord.trans ho.symm)
    obtain ⟨key,ha,hh',_⟩ := matched.sameGeneration
    refine ⟨pos+2,sum,maximum,words,⟨key,?_,hh'⟩,valid⟩
    rwa [Nat.add_sub_cancel]

end PTX.Kernels.TmlFa4Fwd.Progress
