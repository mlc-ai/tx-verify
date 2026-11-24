-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.Thread.ReadyPollPublication
public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitReadyPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof Epilogue Prologue

/-- The third ready acquire needs a completed generation from the third cache slot. -/
theorem singleVisitNoSlotTwoAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch g index : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 = 1) :
    ¬ Thread.Mma.ReadyPoll l X g index 2 0 true .cta := by
  intro hPoll
  obtain ⟨source, hPublication⟩ := Thread.Loader.publicationOfReadyPollZero hp hX 2 hPoll
  exact Thread.Loader.singleVisitNoSlotTwoPublication hp hX hDone hFrame hb hLo hHi hTrip
    (i := source) hPublication

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
