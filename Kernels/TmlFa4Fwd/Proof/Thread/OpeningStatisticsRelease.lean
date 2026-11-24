-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof

/-- After all lanes of an active softmax warp publish their first statistics, its
arrive-only barrier can return without waiting for the correction warp. -/
theorem openingStatisticsReleasedHistoryOfWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g : Nat} (hg : g < l.threads) (hWarp : Prologue.warpIndex l g < 8)
    (hPeers : ∀ peer, SameWarp l g peer → ∃ i, Publishes X (peer,i) .first)
    (hPub : Publishes X (g,(X.tr g).length-1) .first) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Step.Released l Y g := by
  have hInitial {h j : Nat} (hw : Prologue.warpIndex l h < 8)
      (he : Publishes X (h,j) .first) : (before X (h,j)).notices = 0 :=
    let w : Fin 8 := ⟨Prologue.warpIndex l h,hw⟩
    (notificationOrdinal hp hMax.1 hw).trans
      (firstOrdinal hp hMax.1 he (statsBarrierSources hp hMax.1 w))
  apply statisticsReleasedHistoryOfWarp hp hMax hFrame hg hWarp .first 0 _ hPub
    (hInitial hWarp hPub)
  intro peer hPeer
  obtain ⟨i,he⟩ := hPeers peer hPeer
  have hPeerWarp : Prologue.warpIndex l peer < 8 := by
    rw [Prologue.warpIndex,← hPeer.2]
    exact hWarp
  exact ⟨i,he,hInitial hPeerWarp he⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
