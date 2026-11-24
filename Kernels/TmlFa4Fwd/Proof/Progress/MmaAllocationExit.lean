-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.IdleAllocationRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIdleRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Mma

/-- Once the actual allocator warp relinquishes and the other allocation users arrive,
the maximal execution records deallocation and exit without a prior exit assumption. -/
theorem mmaExitsOfRelinquishAndArrivals {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12) (hCuQ : DrainCuQProtected p X)
    (hMma : MmaWarpRelinquished l X (g/l.block))
    (hRows : ∀ lane < l.threads, warpIndex l lane < 12 → lane/l.block = g/l.block →
      ∃ j, FinalAllocationArrival X (lane,j) .arrive) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  have hFinal : MmaWarpAtFinalAllocation l X (g/l.block) := by
    intro lane hLane hWarp hCta
    exact mmaFinalAllocationPrefix hp hMax hLane hWarp (hCta.symm ▸ hMma)
  apply mmaExitsOfFinalAllocation hp hMax hg hw hFinal
  intro lane hLane _ hCta hLast
  obtain ⟨Y,hY,hSame,_,hReady⟩ := finalAllocationCanReleaseOfArrivals hp hMax hLane hCuQ
    (fun peer hPeer hWarp hPeerCta => by
      have hSameCta := hPeerCta.trans hCta
      by_cases hMma : warpIndex l peer = 12
      · obtain ⟨j,hj⟩ := (hFinal peer hPeer hMma hSameCta).arrived
        exact ⟨j,.sync,hj⟩
      · obtain ⟨j,hj⟩ := hRows peer hPeer (by omega) hSameCta
        exact ⟨j,.arrive,hj⟩) hLast
  exact ⟨Y,hY,hSame,hReady⟩

end PTX.Kernels.TmlFa4Fwd.Progress
