-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleCreditFrontier
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityAck
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Protocol.Statistics

/-- The first repeated stage-zero score publication frees the stage-one
opening denominator. This direction does not require the stage-one repeat. -/
theorem openingSecondAckOfRepeatedFirstPublications {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (role : warpIndex l g/4 = 1)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (published : SoftmaxStagePublishedThrough l X (g/l.block) 0 1) :
    Nonempty (Softmax.OpeningProbabilityAck l X g) := by
  have first : SoftmaxStagePublishedThrough l X (g/l.block) 1 0 := by
    intro h hh hc w
    obtain ⟨i,pub⟩ := openingStatisticsOfMaximal hp hMax (frame X hMax.1) hh 1 w
      hb (hc.symm ▸ lo) (hc.symm ▸ hi)
    exact ⟨i,_,pub,Nat.zero_le _⟩
  have credits := statisticsCreditsOfRescalePublications hp hMax frame (NamedBar.cta_lt hg)
    hb lo hi 0 multiple 0 published first
  obtain ⟨q,k⟩ := (frame X hMax.1).metadataProtected hp
  have deps := creditDependenciesOfCountedExitBound hp hMax.1 (countedExitCreditBound hp hMax.1 q k)
  have advanced := statisticsPhaseAdvancedOfCredits hp hMax.1 deps 1 credits
  let w : Fin 8 := ⟨warpIndex l g,by omega⟩
  have s : Softmax.stageOf w = 1 := Fin.ext role
  obtain ⟨elected⟩ := openingProbabilityTailElectionOfMaximal hp hMax (frame X hMax.1)
    hg 1 role hb lo hi
  obtain ⟨joined⟩ := elected.joinOfMaximal hp hMax hg role
  exact joined.acknowledgeOfMaximal hp hMax q hg rfl (s.symm ▸ advanced)

end PTX.Kernels.TmlFa4Fwd.Progress
