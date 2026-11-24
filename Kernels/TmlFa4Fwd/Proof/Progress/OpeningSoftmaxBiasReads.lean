-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxBias
public import Kernels.TmlFa4Fwd.Proof.Thread.SelectedOpeningBiasReads
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

/-- An active softmax lane in either stage acquires and unpacks all opening Bias
words in a maximal execution. The words are those of its selected launch row. -/
theorem openingSoftmaxBiasReadsOfAllStages {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Thread.Scores.FirstBiasAcquire l X g j stage ∧
      Nonempty (Softmax.OpeningBiasReadLane p l X g batch stage j) := by
  obtain ⟨j,hWait,⟨opening⟩⟩ := openingSoftmaxBiasLaneOfAllStages hp hMax hFrame
    hg stage hRole hb hLo hHi
  have hCuQ := (hFrame.metadataProtected hp).1
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  have hGuard := syncGuarded hp hMax.1 hCuQ
  refine ⟨j,hWait,opening.readsOfMaximal hp hMax hGuard hCuQ hWait hg hWarp hb hLo hHi ?_⟩
  intro w a data loc hw ha hs
  rcases hFrame w a data loc hw ha hs with hOut | ⟨q,hq,head,hh,k,hk,rfl⟩
  · exact .inl hOut
  · exact .inr (lseByte_in hq hh hk)

end PTX.Kernels.TmlFa4Fwd.Progress
