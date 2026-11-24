-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.CommitOrder
public import Lemmas.Step.WfInOrder
public import Lemmas.Execution.ExecutionGrowth
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # The commit-order constraint survives extensions that notify in order

A proof tool for progress. The constraint of ASM-COMMIT-ORDER (`commitPerformedAt sites`) holds
of an extension `Y` of `X` whose new commit arrive-ons follow, at the sites `sites`, the previous
commit's (`Execution.NotifiedInOrder`), when it holds of `X` and every arrive-on of `X` is a
commit's (`AsyncCopy.CommitOk`, part of every consistent execution)
(`commitPerformedAt_extend`). An arrive-on of the next commit that `X` already performed is a
commit event of `X`, so the selected commit and the commits between are events of `X` too, and
`X`'s constraint applies; a new one follows the selected commit's in `Y` by the order. -/

namespace PTX.Assumption

/-- **The commit-order constraint survives an extension that notifies in order.** -/
theorem commitPerformedAt_extend {sites : List Nat} {sel : Nat → Bool} {X Y : Execution}
    (hsel : ∀ pc, sites.contains pc = true → sel pc = true)
    (hX : commitPerformedAt sites X) (hok : AsyncCopy.CommitOk X) (hle : X.le Y)
    (hord : X.NotifiedInOrder sel Y) : commitPerformedAt sites Y := by
  intro g j j' pc sp r he hs hjj hc hbetween hr
  by_cases hold : r ∈ X.tcNotified (g, j')
  · obtain ⟨⟨s', -, ⟨pc', he'⟩, -⟩, -⟩ := hok (g, j') r hold
    have hlen := len_of_get he'
    have hjX : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩ := by
      have hx : X.get (g, j) = some (X.tr g)[j] :=
        List.getElem?_eq_getElem (show j < (X.tr g).length by simp at hlen; omega)
      rw [hx, ← he, Execution.le_get hle hx]
    have hbX : ∀ k, j < k → k < j' → ¬ ∃ s, X.Commit (g, k) s := by
      rintro k hk1 hk2 ⟨s, pck, hk⟩
      exact hbetween k hk1 hk2 ⟨s, pck, Execution.le_get hle hk⟩
    exact hle.2.2.2.2.2.2.2.2.2.2.2.2 _
      (hX g j j' pc sp r hjX hs hjj ⟨s', pc', he'⟩ hbX hold)
  · exact hord (g, j') r hr hold j pc sp he (hsel pc hs) hjj hbetween

end PTX.Assumption
