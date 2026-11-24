-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.TcSteps

@[expose] public section
namespace PTX.Flow.Code
open PTX.Proof

variable {K A L g} {C : Code K A L g}

/-- The store substep of a Tensor Memory store crosses its local tail even if an unpack faults. -/
theorem tensorStoreU {d dn : C.D} {ta ss sh} (wait : Bool)
    (hc : K.code[C.pc d]? = some ⟨none,.tcSt ta ss sh⟩)
    (hw : A.any (·.tcStWaitLd (C.pc d)) = wait) (hs : C.sub d = if wait then 1 else 0)
    (ha : C.acc d = []) (hn : ∀ e, C.next d e = some (some dn))
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (seg : SegU K A L g (C.pc d+1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_,hc,rfl,trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    cases wait with
    | false =>
      obtain rfl := fires_tcSt_next (h.1 ▸ hw) hf
      obtain ⟨u,ht,hu⟩ := landsU (At.next (at_of_atD h hs ha)) seg hi hs' ha'
      exact .inl (.inr ⟨dn,u,hn _,ht,hu⟩)
    | true =>
      have ht : t.sub = 1 := h.2.1.trans hs
      have hw' : A.any (·.tcStWaitLd t.pc) = true := h.1 ▸ hw
      simp only [eventTmpl, tcStTmpl, hw', ht, ↓reduceIte, Nat.one_ne_zero] at hf
      obtain rfl := fires_tcStTmpl_next hf
      obtain ⟨u,ht,hu⟩ := landsU (u := PTX.next {t with sub := 0})
        (At.next ⟨h.1,rfl,h.2.2.1.trans ha,h.2.2.2.1,h.2.2.2.2⟩) seg hi hs' ha'
      exact .inl (.inr ⟨dn,u,hn _,ht,hu⟩)

end PTX.Flow.Code
