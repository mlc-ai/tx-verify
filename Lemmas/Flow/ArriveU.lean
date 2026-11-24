-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- An arrival clears its discarded state word and then crosses the local instructions. -/
theorem arriveU {d dn : C.D} {base r : Nat} {off : Int} {tx count : Opnd}
    {cluster release : Bool} {scope : MbarScope}
    (hc : K.code[C.pc d]? =
      some ⟨none,.mbarArrive base off tx count cluster release scope (some r)⟩)
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (seg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    obtain rfl := fires_arrive_next hf
    have ht := at_of_atD h hs hacc
    obtain ⟨u, hl, hu⟩ := landsU (u := PTX.next (mbarStateDest t (some r)))
      ⟨congrArg (·+1) ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
        holds_update ht.2.2.2.2 (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))⟩
      seg hi hs' hacc'
    exact .inl (.inr ⟨dn, u, hn e, hl, hu⟩)

end PTX.Flow.Code
