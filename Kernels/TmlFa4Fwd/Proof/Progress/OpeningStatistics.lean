-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxBiasRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningStatisticsReplay
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningStatisticsRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg stage hRole hb hLo

/-- Every active softmax lane has an opening statistics cursor in a maximal prefix. -/
theorem openingStatisticsCursorOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    Nonempty (Softmax.OpeningStatisticsCursor p l X g stage) := by
  obtain ⟨_,_,⟨arrival⟩,hReleased⟩ :=
    openingSoftmaxBiasRendezvousOfAllStages hp hMax hFrame hg stage hRole hb hLo hHi
  exact arrival.statisticsOfMaximal hp hMax hFrame hg hb hLo hHi
    (hReleased.imp_right (fun ⟨Y,hY,hTrace,_,hReady⟩ => ⟨Y,hY,hTrace,hReady⟩))

/-- Every active softmax lane publishes its initial statistics in a maximal prefix. -/
theorem openingStatisticsOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ i, Thread.Scores.Publishes X (g,i) .first := by
  obtain ⟨cursor⟩ := openingStatisticsCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  exact ⟨cursor.index,cursor.published⟩

/-- The opening statistics arrival of an active lane can return in a maximal
history with the same trace, using the recorded arrivals of its warp peers. -/
theorem openingStatisticsReleasedHistory (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hPub : Thread.Scores.Publishes X (g,(X.tr g).length-1) .first) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  have hWarp : Prologue.warpIndex l g < 8 := by have := stage.isLt; omega
  apply Thread.Scores.openingStatisticsReleasedHistoryOfWarp hp hMax hFrame hg hWarp _ hPub
  intro peer hPeer
  have hRole' : Prologue.warpIndex l peer/4 = stage.val := by
    simpa only [Prologue.warpIndex,← hPeer.2] using hRole
  exact openingStatisticsOfMaximal hp hMax hFrame hPeer.1.2.1 stage
    hRole' hb (hPeer.1.2.2 ▸ hLo) (hPeer.1.2.2 ▸ hHi)

end PTX.Kernels.TmlFa4Fwd.Progress
