-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTerminalOutput
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaAllocationExit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainSearch
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationTerminalExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Mma

/-- After its two terminal output commits, a single-visit MMA warp finishes
its request scan and records a relinquish prefix in every lane. -/
theorem singleVisitMmaWarpRelinquishesOfMaximal
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {cta batch : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1) :
    MmaWarpRelinquished l X cta := by
  intro lane hLane hWarp hCta
  obtain ⟨drain⟩ := singleVisitMmaDrainNeighborsOfMaximal hp hMax hFrame hLane hWarp hb
    (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hSingle)
  exact drain.relinquishOfMaximal hp hMax (hFrame.metadataProtected hp).1 hLane hWarp

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRows : ∀ lane < l.threads, warpIndex l lane < 12 → lane/l.block = g/l.block →
      ∃ j, FinalAllocationArrival X (lane,j) .arrive)
include hp hMax hFrame hg hw hb hLo hHi hSingle hRows

/-- The single-visit allocator deallocates and exits once the row roles
record their actual arrivals for this CTA. -/
theorem singleVisitMmaExitsOfArrivals :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  exact mmaExitsOfRelinquishAndArrivals hp hMax hg hw (hFrame.metadataProtected hp).1
    (singleVisitMmaWarpRelinquishesOfMaximal hp hMax hFrame hb hLo hHi hSingle) hRows

/-- The same actual deallocation releases row lanes in the allocator's CTA. -/
theorem singleVisitMmaDeallocatesOfArrivals :
    ∃ j, Deallocation X (g,j) := by
  obtain ⟨i,⟨site,kind⟩,hi,hKind⟩ :=
    singleVisitMmaExitsOfArrivals hp hMax hFrame hg hw hb hLo hHi hSingle hRows
  change kind = .exit at hKind
  subst kind
  obtain ⟨j,_,hj⟩ := mmaDeallocBeforeExit hp hMax.1 hw hi
  exact ⟨j,Deallocation.ofKind hj rfl⟩

end PTX.Kernels.TmlFa4Fwd.Progress
