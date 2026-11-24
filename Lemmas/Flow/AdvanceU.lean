-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A scalar event advances, after which the intervening instructions may fault. -/
theorem advanceU {d dn : C.D} {op : Op} (hc : K.code[C.pc d]? = some ⟨none,op⟩)
    (hl : op.isLocal = false)
    (ha : ∀ {t u e}, Fires (C.pc d) (eventTmpl A L g t op) e (some u) → u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (seg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    obtain rfl := ha hf
    obtain ⟨u, hl, hu⟩ := landsU (At.next (at_of_atD h hs hacc)) seg hi hs' hacc'
    exact .inl (.inr ⟨dn, u, hn e, hl, hu⟩)

end PTX.Flow.Code
