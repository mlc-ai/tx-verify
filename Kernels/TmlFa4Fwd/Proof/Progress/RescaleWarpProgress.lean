-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleWarpRoundProgress
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleLoopStart
import Kernels.TmlFa4Fwd.Proof.Progress.FirstRescaleGeneration
public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleRoundRelease
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Every correction warp on a repeated tile begins with the original trip
count, generation one on both statistics groups, and no tensor operations. -/
theorem openingRescaleWarpOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat}
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRepeat : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    Nonempty (Correction.RescaleWarpJoin p l X g batch
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) 0 (fun _ => 1) 1 0) := by
  classical
  have front (h : Nat) (hs : SameWarp l g h) :=
    let hW : warpIndex l g = warpIndex l h := hs.2
    firstRescaleOrdinalsOfMaximal hp hMax hFrame hs.1.2.1 (hW ▸ hw) hb
      (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi) (hs.1.2.2 ▸ hRepeat)
  choose raw named vote tc using front
  have each (h : Nat) (hs : SameWarp l g h) :
      ∃ d : Correction.RescaleWaitReached l X h 0 (Correction.rescaleLaneFrame p l h batch
          (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)),
        d.index = (raw h hs).index := by
    obtain ⟨d,hd⟩ := (raw h hs).asLoopWait hp hMax.1 hs.1.2.1 (hs.1.2.2 ▸ hRepeat)
    rw [hs.1.2.2]
    exact ⟨d,hd⟩
  choose d pos using each
  exact ⟨⟨d,fun h hs => by rw [pos]; exact ⟨tc h hs,vote h hs⟩,
    fun h hs s => by rw [pos]; exact named h hs s⟩⟩

/-- Matching softmax publications release the reached generation and return
both correction slot credits for every lane, including a nonzero rescale vote. -/
theorem rescaleWarpReturnedOfPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch blocks ord rank : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    {stage : Fin 2} {gen : Fin 2 → Nat}
    (c : Correction.RescaleWarpJoin p l X g batch blocks stage gen ord rank)
    (pub : ∀ peer < l.threads, peer/l.block = g/l.block →
      warpIndex l peer = (Protocol.Statistics.waitingWarp l g stage).val →
      ∃ i round, Scores.Publishes X (peer,i) round ∧
        gen stage ≤ observedBarrierOrdinal X (peer,i) (3+warpIndex l peer)) :
    ∃ n, (n = 0 ∨ n = 25) ∧ Nonempty (Correction.RescaleWarpReturned p l X g batch blocks stage
      (Correction.rescaleNextGeneration gen stage) (ord+1) (rank+n)) := by
  apply c.returnOfRelease hp hMax hFrame hg hw
  intro h hs last
  have w : warpIndex l g = warpIndex l h := hs.2
  apply rescaleReleaseOfWarpPublications hp hMax ((hFrame X hMax.1).metadataProtected hp).1
    hs.1.2.1 (w ▸ hw) stage (gen := gen stage) _ _
    (rescaleWaitObservation stage (c.lane h hs).joined) (c.named h hs stage) last
  · intro k hk
    have same := Step.sameWarp_trans hs hk
    exact ⟨_,rescaleWaitObservation stage (c.lane k same).joined,c.named k same stage⟩
  · intro k hLt hC hW
    apply pub k hLt (hC.trans hs.1.2.2.symm)
    simpa only [Protocol.Statistics.waitingWarp,w] using hW

end PTX.Kernels.TmlFa4Fwd.Progress
