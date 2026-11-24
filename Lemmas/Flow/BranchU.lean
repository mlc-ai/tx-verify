-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc

@[expose] public section

namespace PTX.Flow.SegU
open PTX.Proof

/-- Consume the control predicate at a branch and retain the remaining register facts. -/
theorem branch {K A L g pc pred target uni F} (pick : Bool)
    (hc : K.code[pc]? = some ⟨some (pred,false), .bra target uni⟩)
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) : SegU K A L g pc ((pred,.pred pick) :: F)
      (if pick then target else pc + 1) F := by
  intro t ht
  obtain ⟨u, hl, hu⟩ := run_bra hc pick ht ht.2.2.2.2.1 (hL t) hA
  exact .inl ⟨u, run_rtg hl, hu.mono hu.2.2.2.2.2⟩

end PTX.Flow.SegU
