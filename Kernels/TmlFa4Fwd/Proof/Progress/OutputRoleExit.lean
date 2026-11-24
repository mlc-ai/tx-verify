-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OutputWriteback
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainLaterProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

/-- In an active CTA, both correction cohorts force completion of all output
stores, output stage releases, and the output warp's final drain and exit. -/
theorem outputExitsOfPublishedCohorts {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X)
    (hActive : g/l.block < tilePrefix p p.batch * p.heads)
    (hPublished : ∀ stage : Fin 2, ∀ row < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) row,j) stage) :
    Thread.Exited X g :=
  outputDrainExitsOfMaximal hp hMax hg hCuQ hActive
    (outputWritebackOfPublishedCohorts hp hMax hg hw hCuQ hActive hPublished)

end PTX.Kernels.TmlFa4Fwd.Progress
