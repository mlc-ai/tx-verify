-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleCreditFrontier
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringProbabilityCohorts
import Kernels.TmlFa4Fwd.Proof.Thread.RescaleProbabilityExtent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Thread.Scores Protocol.Scores

/-- The paired row groups deliver the exact main-P cohort for a steady MMA visit.
Only the current stage's softmax main arrivals and the two statistics publication
counts are needed. Correction's contribution includes its real priming arrival. -/
theorem repeatedMainProbabilityCohortOfPublications {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (round : Nat) (active : round+1 < Mma.trips p batch (assignedCoordinates p batch cta).1)
    (stage : Fin 2) (zero : SoftmaxStagePublishedThrough l X cta 0 (round+1))
    (one : SoftmaxStagePublishedThrough l X cta 1 (round+stage.val))
    (soft : ∀ g < l.threads, g/l.block = cta → warpIndex l g < 8 →
      warpIndex l g/4 = stage.val → ∃ i, ProbabilityCredit l X (g,i) cta stage 0 ∧
        probabilityOrdinal l X cta stage 0 (g,i) = round+1) :
    ProbabilityCohort l X cta stage 0 (round+1) := by
  apply mainProbabilityCohortOfProducers hp stage
  intro g ctaEq role
  have hg : g < l.threads :=
    (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).mp (ctaEq.symm ▸ hc)
  rcases role with sm | corr
  · exact soft g hg ctaEq sm.1 sm.2
  · apply probabilityCreditOfExtent hp hMax.1 stage 0
    rw [← ctaEq]
    apply Correction.probabilityExtentOfPairedReturns hp hMax hg corr stage round
    intro k hk
    have weaker {s : Fin 2} {a b : Nat} (ab : a ≤ b)
        (pub : SoftmaxStagePublishedThrough l X cta s b) :
        SoftmaxStagePublishedThrough l X cta s a := by
      intro h hh eq w
      obtain ⟨i,r,hr,n⟩ := pub h hh eq w
      exact ⟨i,r,hr,ab.trans n⟩
    exact pairedRescaleCreditsOfPublications hp hMax frame hb lo hi k (by omega) stage
      (weaker (by omega) zero) (weaker (by omega) one) g hg ctaEq corr

end PTX.Kernels.TmlFa4Fwd.Progress
