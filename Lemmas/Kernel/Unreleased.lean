-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Released

@[expose] public section

/-! # The blocking last event of a thread that is not released

A thread whose last event is not released (`Step.Released` fails) has a last event that blocks
(`Kind.resume = .blocking false`: a CTA or cluster barrier operation, a register request, a group
wait, a Tensor Memory allocation-management event or a warp-collective `tcgen05` event) and is not
ready (`unreleased_cases`): one of its needs (`KindNeeds`) is not filled. A kernel's progress
argument discharges each kind separately. -/

namespace PTX.Descent

open PTX

variable {L : Launch} {X : Execution} {g : Nat}

/-- **The failing part of a release**: a blocking last event that is not ready. -/
theorem unreleased_cases (h : ¬ Step.Released L X g) :
    ∃ pc k, X.get (g, (X.tr g).length - 1) = some ⟨pc, k⟩ ∧ k.resume = .blocking false ∧
      ¬ Ready L X (g, (X.tr g).length - 1) := by
  by_contra hc
  exact h ⟨fun pc k hq hk => by
    by_contra hr
    exact hc ⟨pc, k, hq, hk, hr⟩⟩

end PTX.Descent
