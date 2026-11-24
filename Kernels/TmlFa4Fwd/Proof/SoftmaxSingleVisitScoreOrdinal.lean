-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPhase
public import Kernels.TmlFa4Fwd.Proof.Thread.ScoreProbabilityGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof Epilogue Thread.Scores

/-- No score notification of the selected one-visit CTA can be a positive generation. -/
theorem singleVisitScoreCommitOrdinalZero {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    {batch cta : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1)
    {i : EvId} {stage : Fin 2} {spec : TcCommit.Spec} {rank : Fin 16}
    (hScore : ScoreCommit l X i cta stage spec rank) : scoreCommitOrdinal l X cta stage i = 0 := by
  by_contra hPositive
  have hOrdinal := Nat.pos_of_ne_zero hPositive
  have hOwner := (scoreCommitActor hp hX hScore).1
  obtain ⟨bank,_,hBank,he⟩ := positiveScoreCommitRepeats hp hX hScore hOrdinal
  obtain ⟨g,index⟩ := i
  apply singleVisitNoLateSteadyEvent hp hX hDone hFrame hb
    (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip) he
  change 2355 ≤ (Mma.commitSite (Mma.qkCommitSite bank)).pc ∧
    (Mma.commitSite (Mma.qkCommitSite bank)).pc < 2534
  revert hBank
  fin_cases bank <;> decide

end PTX.Kernels.TmlFa4Fwd.Softmax
