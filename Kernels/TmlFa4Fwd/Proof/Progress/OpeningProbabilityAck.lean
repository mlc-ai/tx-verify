-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorNotice
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityStores
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCorrectionStatistics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
include hp hMax hFrame hg stage hRole hb hLo hHi

/-- An active lane acquires the opening probability acknowledgement when
correction supplies the first statistics credit for its stage. -/
theorem openingProbabilityAckOfMaximal
    (hSingle : stage.val = 1 → Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    Nonempty (Softmax.OpeningProbabilityAck l X g) := by
  let w : Fin 8 := ⟨warpIndex l g,by have := stage.isLt; omega⟩
  have hStage : Softmax.stageOf w = stage := Fin.ext hRole
  obtain ⟨elected⟩ := openingProbabilityTailElectionOfMaximal hp hMax hFrame hg stage
    hRole hb hLo hHi
  obtain ⟨joined⟩ := elected.joinOfMaximal hp hMax hg hRole
  have hGrid : g/l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hAdvanced := openingStatsSlotAdvancedOfMaximal hp hMax hFrame hGrid hb hLo hHi stage hSingle
  exact joined.acknowledgeOfMaximal hp hMax (hFrame.metadataProtected hp).1 hg rfl
    (hStage.symm ▸ hAdvanced)

/-- Every active softmax lane of a single-visit tile records its final statistics
publication, without using an exit or completion witness. -/
theorem singleVisitSoftmaxTerminalWordsWithMassOfMaximal
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    let warp : Fin 8 := ⟨warpIndex l g,by have := stage.isLt; omega⟩
    ∃ i sum maximum, Thread.Scores.Publishes X (g,i+2) .final ∧
      (Thread.Scores.before X (g,i+2)).notices = 1 ∧
      X.Writes (g,i) (Softmax.statsAcc l g warp 2) (fl sum).toBytes ∧
      X.Writes (g,i+1) (Softmax.statsAcc l g warp 3) (Softmax.scoreValue maximum).toBytes ∧
      Softmax.DenominatorValid sum maximum := by
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  let cap := blocks-Softmax.stageGeometryBlocks p batch tile stage+10
  let past := p.kLength batch-p.qLength batch+256*tile
  have ht := (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨hPos,_,hLimit⟩ := Mma.trips_bounds hp hb ht
  have hOne : blocks = 1 := by change 0 < blocks at hPos; change blocks < 2 at hSingle; omega
  have hCap : 0 < cap ∧ cap < 2^31 := by dsimp only [cap]; omega
  have hPast : past+256 < 2^31 := by
    change p.kLength batch-p.qLength batch+256*(tile+1) < 2^31 at hLimit
    change (p.kLength batch-p.qLength batch+256*tile)+256 < 2^31
    simpa only [Nat.mul_succ,Nat.add_assoc] using hLimit
  obtain ⟨ack⟩ := openingProbabilityAckOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
    (fun _ => hSingle)
  obtain ⟨c⟩ := ack.denominatorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  have c' : Softmax.OpeningDenominatorCursor p l X g 1 cap past := hOne ▸ c
  have hw : warpIndex l g < 8 := by have := stage.isLt; omega
  have hCuQ := (hFrame.metadataProtected hp).1
  have hNotice := c'.noticesOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  have hOrdinal := c'.singleVisitPublicationOrdinal hp hMax hCuQ hg hw hCap.1 hCap.2 hPast hNotice
  obtain ⟨hPublication,hSum,hMax⟩ :=
    c'.publishSingleVisitAtCursor hp hMax hCuQ hg hw hCap.1 hCap.2 hPast
  exact ⟨c'.cursor.pos,c'.sum,c'.maximum,hPublication,hOrdinal,hSum,hMax,c'.valid⟩

/-- The actual single-visit publication records both terminal words. -/
theorem singleVisitSoftmaxTerminalWordsOfMaximal
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    let warp : Fin 8 := ⟨warpIndex l g,by have := stage.isLt; omega⟩
    ∃ i sum maximum, Thread.Scores.Publishes X (g,i+2) .final ∧
      (Thread.Scores.before X (g,i+2)).notices = 1 ∧
      X.Writes (g,i) (Softmax.statsAcc l g warp 2) (fl sum).toBytes ∧
      X.Writes (g,i+1) (Softmax.statsAcc l g warp 3) (Softmax.scoreValue maximum).toBytes := by
  obtain ⟨i,sum,mx,hNotice,hOrdinal,hSum,hMax,_⟩ :=
    singleVisitSoftmaxTerminalWordsWithMassOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
      hSingle
  exact ⟨i,sum,mx,hNotice,hOrdinal,hSum,hMax⟩

/-- Every active softmax lane of a single-visit tile records its final statistics. -/
theorem singleVisitSoftmaxTerminalPublicationOfMaximal
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 < 2) :
    ∃ i, Thread.Scores.Publishes X (g,i) .final := by
  obtain ⟨i,_,_,hNotice,_,_,_⟩ :=
    singleVisitSoftmaxTerminalWordsOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi hSingle
  exact ⟨i+2,hNotice⟩

end PTX.Kernels.TmlFa4Fwd.Progress
