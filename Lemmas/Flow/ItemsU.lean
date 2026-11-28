-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutRun
public import Lemmas.Flow.OutLit
public import Lemmas.Flow.Havoc

@[expose] public section

/-! # A run of items as a piece that continues or dies

A proof tool. `SegD.xouts` (`OutRun.lean`) gives a run of items from facts by any value function to
the facts by the values after the run, under the run's condition and otherwise a dead thread; a
site machine's step takes a piece that continues to its end or is dead (`SegU`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A run of items, as a piece of a site machine**: from the facts by `V` to the facts by the
values after the run. -/
theorem SegU.of_items {pc : Nat} {items : List XItem} {liveS liveT : List Nat}
    {V : Nat → Value} (hat : OAt K A L g pc items) (hloc : xLocalB items = true)
    (hreads : xReadsB liveS items = true) (hreq : xReq V items = true)
    (hcov : ∀ r ∈ liveT, r ∈ xWrites items ∨ r ∈ liveS) :
    SegU K A L g pc (factsFrom liveS V) (pc + items.length)
      (factsFrom liveT (xFinal V items)) := by
  have h := SegD.xouts (K := K) (A := A) (L := L) (g := g) hat.code hreads hreq hloc hat.rules hcov
  intro t ht
  by_cases c : xCond V items
  · obtain ⟨u, hr, hu⟩ := (h t ht).1 c
    exact .inl ⟨u, run_rtg hr, hu⟩
  · exact .inr ((h t ht).2 c)

end PTX.Flow
