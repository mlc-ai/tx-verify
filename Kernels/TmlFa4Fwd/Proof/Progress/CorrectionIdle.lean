-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionIdleArrival
public import Kernels.TmlFa4Fwd.Proof.Protocol.IdleOutputFree

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

/-- Every correction lane of an idle CTA records its final allocation arrival for any batch. -/
theorem idleCorrectionReachesFinalAllocationForBatches {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j, Thread.FinalAllocationArrival X (g,j) .arrive :=
  Correction.idleFinalArrivalForBatchesOfPhaseZero hp hMax hg hLo hHi hCuQ hIdle
    (Protocol.Output.idleFreePhaseZeroOfAllGroups hp hMax (NamedBar.cta_lt hg) 1 hCuQ hIdle)

end PTX.Kernels.TmlFa4Fwd.Progress
