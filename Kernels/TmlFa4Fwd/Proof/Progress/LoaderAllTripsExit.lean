-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundExit
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderSteadyRoundExit
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderRoundDrainExit
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundTailProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread.Loader Protocol.Loader Protocol.Bias
open PTX.Kernels.TmlFa4Fwd.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hFrame hg hw hb hLo

/-- Both loader warps of a scheduled multi-visit CTA publish every use of the tile and exit,
given the MMA releases of the cache slots, the softmax releases of the Bias slots, and the
final query release. -/
theorem loaderPublishesAndExits (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g
      (2*Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1+3))
    (hBias : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1))
    (hTail : warpIndex l g = 14 → warmTailSkips p l g batch = false →
      BiasEmptyReleased l X (g/l.block) 0 (warmRounds p l g batch+1))
    (hQuery : warpIndex l g = 14 → UnitRelease X (secondQueryEmpty l (g/l.block))) :
    Thread.Exited X g := by
  let T := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have hWarm : warmRounds p l g batch = min (T-1) 9 := rfl
  by_cases hShort : T ≤ 10
  · exact warmRoundsLoaderExit hp hMax hFrame hg hw hb hLo hHi hTrips hShort hReleased hBias
      hQuery
  · have hLong : 11 ≤ T := by omega
    obtain ⟨⟨d⟩,_⟩ := warmTailDoneOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
      (hReleased.mono (by omega)) hBias hTail
    obtain ⟨hEntry,hUses,_⟩ := steadyRoundsDrainEntry hp hMax hFrame hg hw hb hLo hHi hLong
      (hReleased.mono (by omega)) d
    exact loaderExitOfDrainEntry hp hMax hFrame hg hw hHi hb (by omega) hEntry hUses hReleased
      hQuery

end PTX.Kernels.TmlFa4Fwd.Progress
