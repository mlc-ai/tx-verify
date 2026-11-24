-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionEntryProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof Prologue

/-- Each correction lane issues the opening joint probability credit for both stages. -/
theorem openingJointProbabilityCreditOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12) (stage : Fin 2) :
    ∃ j, Thread.Scores.ProbabilityCredit l X (g,j) (g/l.block) stage 0 := by
  obtain ⟨_,_,_,hZero,hOne,_,_,_,_⟩ := schedulerEntryOfMaximal hp hMax hg hLo hHi
  fin_cases stage
  · exact ⟨7,7752,hZero⟩
  · exact ⟨8,7754,hOne⟩

end PTX.Kernels.TmlFa4Fwd.Correction
