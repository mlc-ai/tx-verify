-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseEntry
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStageFrame
import Kernels.TmlFa4Fwd.Flow.Code.Part141

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.Assumption Epilogue

noncomputable section

/-- The first stage's nonzero predicate survives normalization. The second stage reads its
own sum again at PC9074 for the LSE selection. -/
theorem secondLsePredicate {l : Launch} {g : Nat} {t : TState} {F : List (Nat × Value)}
    (sum : ℝ) (ht : At t 9074 F) (hSum : t.regs 1653 = some (fl sum))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ 742) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u 9075 ((742, .pred (decide (sum ≠ 0))) :: F) := by
  obtain ⟨u, hRun, hu⟩ := secondLsePredicateRun (l := l) (g := g) sum ht hSum hFresh
  exact ⟨u, run_rtg hRun, hu⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
