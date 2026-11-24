-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxIdleArrival
public import Kernels.TmlFa4Fwd.Proof.Protocol.IdleStatisticsCredit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- Every idle softmax lane reaches the final allocation rendezvous for any batch size. -/
theorem idleSoftmaxReachesFinalAllocationForBatches {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hCuQ : DrainCuQProtected p X) (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j, Thread.FinalAllocationArrival X (g,j) .arrive := by
  have hc : g/l.block < l.grid := NamedBar.cta_lt hg
  obtain ⟨j,_,_,he,_,_,_⟩ := Softmax.idleFinalArrivalPrefixOfAllGroups hp hMax hg hw hCuQ hIdle
    (fun stage => Protocol.Statistics.idleStatisticsPhaseZero hp hMax hc stage hIdle)
  exact ⟨j,he⟩

end PTX.Kernels.TmlFa4Fwd.Progress
