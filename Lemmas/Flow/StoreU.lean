-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A continuing scalar store crosses its local tail independently of the bytes it wrote. -/
theorem scalarStoreU {d dn : C.D} {a : MemAccess}
    (hc : K.code[C.pc d]? = some ⟨none,.mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hst : a.kind = .store) (hlen : a.srcs.length = 1)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (ha : C.acc d = [])
    (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (seg : SegU K A L g (C.pc d+1) (C.facts d) (C.pc dn) (C.facts dn)) : C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
    rw [afterStore_last (by rw [h.2.1, hs, hlen]; decide)]
    obtain ⟨u, ht, hu⟩ := landsU (u := {t with pc := t.pc+1, sub := 0})
      ⟨congrArg (·+1) h.1, rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩ seg hi hs' ha'
    exact .inl (.inr ⟨dn,u,hn _,ht,hu⟩)

end PTX.Flow.Code
