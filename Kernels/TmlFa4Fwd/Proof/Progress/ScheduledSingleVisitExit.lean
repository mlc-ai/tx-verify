-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitLoaderRetire
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterSelection
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningOutputDrain
import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitRowRetire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread.Loader

set_option maxRecDepth 4096 in
/-- A scheduled single-visit CTA retires both loader warps in every maximal execution,
including CTA assignments reached through any number of request groups. -/
theorem scheduledSingleVisitLoaderExitOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    Thread.Exited X g := by
  obtain ⟨hCache,hQuery⟩ :=
    singleVisitLoaderDrainReadyOfMaximal hp hMax hFrame hg hb hLo hHi hSingle
  obtain ⟨neighbors⟩ :=
    singleVisitLoaderDrainNeighborsOfMaximal hp hMax hFrame hg hw hb hLo hHi hSingle
  have hActive := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  exact neighbors.exitOfScheduledCta hp hMax hg hw (hFrame.metadataProtected hp).1
    hActive hCache (fun _ => hQuery)


/-- Every role of a scheduled single-visit CTA retires from the actual maximal trace. -/
theorem scheduledSingleVisitExitsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    Thread.Exited X g := by
  by_cases hRow : warpIndex l g < 13
  · exact singleVisitRowsAndMmaExitOfMaximal hp hMax hOutputs (NamedBar.cta_lt hg)
      hb hLo hHi hSingle g hg rfl hRow
  by_cases hStore : warpIndex l g = 13
  · exact singleVisitOutputExitsOfMaximal hp hMax hOutputs hg hStore hb hLo hHi hSingle
  exact scheduledSingleVisitLoaderExitOfMaximal hp hMax (hOutputs X hMax.1)
    hg (by omega) hb hLo hHi hSingle

end PTX.Kernels.TmlFa4Fwd.Progress
