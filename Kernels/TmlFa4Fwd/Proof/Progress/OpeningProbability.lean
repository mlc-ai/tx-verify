-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningProbabilityReplay

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX

/-- Every active softmax lane has issued its first delayed Tensor Memory wait. -/
theorem openingProbabilityWaitCursorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : Prologue.warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    Nonempty (Softmax.OpeningProbabilityWaitCursor p l X g stage) := by
  obtain ⟨statistics⟩ := openingStatisticsCursorOfMaximal hp hMax hFrame hg stage hRole hb hLo hHi
  apply statistics.probabilityWaitOfMaximal hp hg
  intro hEnd
  have hj : statistics.index = (X.tr g).length-1 := by omega
  exact openingStatisticsReleasedHistory hp hMax hFrame hg stage hRole hb hLo hHi
    (hj ▸ statistics.published)

end PTX.Kernels.TmlFa4Fwd.Progress
