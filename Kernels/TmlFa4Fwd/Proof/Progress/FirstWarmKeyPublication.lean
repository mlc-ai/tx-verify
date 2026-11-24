-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningValueAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyCheckpoint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- Both scheduled loader warps publish the first warm key packet for any repeated KV tile. -/
theorem openingAndFirstWarmKeyPublishedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hWarm : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    Nonempty (Thread.Loader.WarmFirstKeyPublished p l X g batch) := by
  obtain ⟨started⟩ := openingLoaderWarmCacheOfMaximal hp hMax hFrame hg hw hb hLo hHi hWarm
  obtain ⟨pages⟩ := started.refreshPagesOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact pages.keyPublishedOfMaximal hp hMax hg hw hb hLo hHi hWarm

end PTX.Kernels.TmlFa4Fwd.Progress
