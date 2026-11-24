-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleRoundReadProgress
public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleLoopFrame
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The first actual rescale join supplies the recurrent loop's lane frame
and initial remaining-trip count. -/
theorem FirstRescaleReached.asLoopWait {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch : Nat} (hg : g < l.threads)
    (hRep : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (c : FirstRescaleReached p l X g batch (laneOf l g)) :
    ∃ d : RescaleWaitReached l X g 0 (rescaleLoopFacts (correctionRescaleFrame p l g batch)
        (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) (laneOf l g)),
      d.index = c.index := by
  have self : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have hWait := c.waited
  rw [self] at hWait
  obtain ⟨e,he,ha⟩ := hWait
  have site := Thread.correctionRescaleWaitSite ha
  have kind := Thread.correctionStatsWait hp hX he ha
  have obs : X.get (g,c.index) = some ⟨statsBarrierPc 0 true,.bar (statsBarrierId l g 0)
      (some 64) .sync⟩ := by
    rw [he]
    obtain ⟨pc,k⟩ := e
    change pc = _ at site
    change k = _ at kind
    rw [site,kind]
  exact ⟨⟨c.index,c.state,c.ending,obs,
    by rw [← correctionRescaleFrame_ready hRep]; exact c.ready,
    by simpa only [self] using c.recorded,by simpa only [self] using c.remaining⟩,rfl⟩

end PTX.Kernels.TmlFa4Fwd.Correction
