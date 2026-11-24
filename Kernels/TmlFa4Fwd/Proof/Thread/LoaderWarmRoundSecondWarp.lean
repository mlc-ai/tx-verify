-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- Warp 15 bypasses the Bias block, passes the V poll of warm round `round` and publishes
the round's V packet. The release hypothesis is the MMA's return of the earlier generations
of the V slot. -/
theorem WarmRoundKeyPublished.valuePublishedSecondWarpOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 15) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)))
    (c : WarmRoundKeyPublished p l X g batch round) :
    Nonempty (WarmRoundValuePublished p l X g batch round) := by
  obtain ⟨done,hDone⟩ :=
    c.valueAcquireSecondWarpOfMaximal hp hMax hFrame hg hw hb hLo hHi hReleased
  have hBias : loaderPhaseWord (warmBiasPhase (warpIndex l g) round) =
      loaderPhaseWord (warmBiasPhase (warpIndex l g) (round+1)) := by
    simp [warmBiasPhase,hw]
  exact warmRoundValuePublishedOfMaximal hp hMax hg (by omega) hb hLo hHi hBias c.rank done
    (fun lane hl => (hDone lane hl).2)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
