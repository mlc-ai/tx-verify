-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSoftmaxBiasRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningBiasAffineNumerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue

/-- Every active lane returns from the opening Bias rendezvous, reads the launch
scales, and computes its affine logits from the actual score and Bias words. -/
theorem openingSoftmaxAffineOfAllStages {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2)
    (hRole : warpIndex l g/4 = stage.val) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, Nonempty (Softmax.OpeningAffineLane p l X g batch stage j) := by
  obtain ⟨j,_,⟨arrival⟩,hReleased⟩ :=
    openingSoftmaxBiasRendezvousOfAllStages hp hMax hFrame hg stage hRole hb hLo hHi
  obtain ⟨entry⟩ := arrival.firstFmaOfMaximal hp hg
    (hReleased.imp_right (fun ⟨Y,hMax,hTrace,_,hReady⟩ => ⟨Y,hMax,hTrace,hReady⟩))
  exact ⟨j,entry.affineOfPrefix hp hMax.1 hFrame hb hLo hHi⟩

end PTX.Kernels.TmlFa4Fwd.Progress
