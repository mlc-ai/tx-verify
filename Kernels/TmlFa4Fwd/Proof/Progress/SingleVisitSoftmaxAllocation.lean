-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitSoftmaxCreditHandoff
public import Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitSecondTerminalCredits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Protocol.Statistics

/-- Every active softmax lane on a single-visit tile reaches the final allocation
rendezvous in the maximal execution. -/
theorem singleVisitSoftmaxFinalArrivalsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hOutputs : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hOne : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  have hFrame := hOutputs X hMax.1
  obtain ⟨hCuQ,hUsedK⟩ := hFrame.metadataProtected hp
  have hCount := countedExitCreditBound hp hMax.1 hCuQ hUsedK
  have hDeps := creditDependenciesOfCountedExitBound hp hMax.1 hCount
  let stage := Softmax.stageOf ⟨warpIndex l g,hw⟩
  have hCta : g/l.block < l.grid := NamedBar.cta_lt hg
  have hCredit (s : Fin 2) : TerminalCorrectionCredits l X (g/l.block) s 1 := by
    fin_cases s
    · exact singleVisitFirstTerminalCreditsOfMaximal hp hMax hFrame hCta hb hLo hHi hOne
    · exact singleVisitSecondTerminalCreditsOfMaximal hp hMax hOutputs hCta hb hLo hHi hOne
  exact singleVisitSoftmaxAllocationOfCorrectionCredits hp hMax hFrame hDeps
    hg hw hb hLo hHi hOne (hCredit stage)

end PTX.Kernels.TmlFa4Fwd.Progress
