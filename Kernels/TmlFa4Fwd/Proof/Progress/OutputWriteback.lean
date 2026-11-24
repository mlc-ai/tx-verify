-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputWritebackRetireProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputStoreProgress
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

/-- A scheduled output warp completes both writeback stages once both correction cohorts
publish. Its issued TMA operations drain by the verified output source protocol. -/
theorem outputWritebackOfPublishedCohorts {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
    (hPublished : ∀ stage : Fin 2, ∀ row < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) row,j) stage) :
    OutputWritebackDrained p l X g :=
  outputWritebackDrainedOfMaximal hp hMax hg hw hCuQ hActive hPublished
    (fun _ _ _ h => Protocol.Output.actualStoreFullyDone hp hMax h (syncGuarded hp hMax.1 hCuQ))

/-- The published surfaces enable all 32 actual release credits for each output stage. -/
theorem outputFreeCreditsOfPublishedCohorts {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g = 13) (hCuQ : DrainCuQProtected p X)
    (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hPublished : ∀ stage : Fin 2, ∀ row < 128, ∃ j,
      Thread.CorrectionReady X (Thread.Output.sourceLane l (g,0) row,j) stage) :
    ∀ stage : Fin 2, ∀ lane : Fin 32, ∃ j,
      Thread.Output.FreeCredit l X (g/l.block) stage
        (Thread.Output.outputLane l (g/l.block) lane,j) :=
  (outputWritebackDrainedWithCreditsOfMaximal hp hMax hg hw hCuQ hActive hPublished
    (fun _ _ _ h => Protocol.Output.actualStoreFullyDone hp hMax h (syncGuarded hp hMax.1 hCuQ))).2

end PTX.Kernels.TmlFa4Fwd.Progress
