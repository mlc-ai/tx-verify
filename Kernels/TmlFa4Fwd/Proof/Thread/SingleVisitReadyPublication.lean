-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderSingleBiasVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFacts
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.AsyncCopy Epilogue Prologue

/-- A selected one-visit CTA has no loader publication to the third cache slot. -/
theorem singleVisitNoSlotTwoPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch owner : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ owner / l.block)
    (hHi : owner / l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (owner / l.block)).1 = 1)
    {i : EvId} : ¬ X.AsyncArrive i (Thread.Loader.readyObject l owner 2) true := by
  rintro ⟨pc,he⟩
  obtain ⟨g,j⟩ := i
  obtain ⟨⟨site,hPc⟩,_,_,hCta⟩ := Loader.actualAsyncArrival hX he
  change owner / l.block = g / l.block at hCta
  have hSites : pc ∈ [674,904] ∨ 905 ≤ pc ∧ pc < 1744 := by
    rw [hPc]
    fin_cases site <;> decide
  rcases hSites with hPriming | hRecurring
  · have hAddr := congrArg Loc.addr (Loader.loaderStartupAsyncAddress hp hX he hPriming)
    change l.sharedBase + 48 = l.sharedBase + (if pc = 674 then 32 else 40) at hAddr
    split_ifs at hAddr <;> omega
  · apply PTX.Kernels.TmlFa4Fwd.Loader.singleVisitLoaderEventNotRecurring hp hX hDone hb
      (hCta ▸ hLo) (hCta ▸ hHi) (hCta ▸ hTrip)
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) he hRecurring
    simp [Ends]

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
