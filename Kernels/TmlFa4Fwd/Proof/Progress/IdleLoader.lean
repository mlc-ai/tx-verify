-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleElection
public import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

/-- Both loader warps of any idle CTA record their exits in a maximal execution. -/
theorem idleLoaderExitsForBatches {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g / l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit :=
  Loader.idleLoaderExitForBatchesOfPhaseZero hp hMax hg hw hCuQ hIdle
    (fun obj => Protocol.Loader.idleReleasePhaseZeroForBatches hp hMax
      (NamedBar.cta_lt hg) obj hCuQ hIdle)

end PTX.Kernels.TmlFa4Fwd.Progress
