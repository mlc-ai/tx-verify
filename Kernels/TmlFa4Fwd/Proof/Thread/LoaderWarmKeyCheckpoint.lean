-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The first warm key packet has returned its ready arrivals for all physical lanes. -/
structure WarmFirstKeyPublished (p : Params) (l : Launch) (X : Execution) (g batch : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1138 (warmFirstKeyCarry p l g batch) shuffles votes ends
  published : ∀ lane < 32, ∃ i, i+1 = reached.pos lane ∧
    X.AsyncArrive (warpLane l g lane,i) (readyObject l (warpLane l g lane) 2) true

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
include hp hMax hg hw hb hLo hHi hTrips

/-- The reached first cache pages progress through all key vectors, commit and ready arrival. -/
theorem WarmFirstPages.keyPublishedWithRankOfMaximal (c : WarmFirstPages p l X g batch) :
    ∃ next : WarmFirstKeyPublished p l X g batch, next.shuffles = c.shuffles+32 := by
  obtain ⟨done,hPublished⟩ := c.publishKeyOfMaximal hp hMax hg hw hb hLo hHi hTrips
  exact ⟨⟨c.shuffles+32,c.votes,c.ends,done,hPublished⟩,rfl⟩

/-- The first warm key publication is also available without its shuffle rank. -/
theorem WarmFirstPages.keyPublishedOfMaximal (c : WarmFirstPages p l X g batch)
    : Nonempty (WarmFirstKeyPublished p l X g batch) := by
  obtain ⟨next,_⟩ := c.keyPublishedWithRankOfMaximal hp hMax hg hw hb hLo hHi hTrips
  exact ⟨next⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
