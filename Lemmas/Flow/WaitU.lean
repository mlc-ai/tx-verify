-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LandsU

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem waitU {d : C.D} {dst : Bool → C.D} {r base off par acq sc}
    (hc : K.code[C.pc d]? = some ⟨none,.mbarWait r base off par acq sc⟩)
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m q ok s, C.next d ⟨C.pc d, .wait m q ok acq s⟩ = some (some (dst ok)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ok, C.sub (dst ok) = 0)
    (ha' : ∀ ok, C.acc (dst ok) = []) (hi : ∀ ok, C.inv (dst ok))
    (seg : ∀ ok, SegU K A L g (C.pc d+1) ((r,.pred ok) :: C.facts d)
      (C.pc (dst ok)) (C.facts (dst ok))) : C.StepAtU d where
  site := fun _ => ⟨_, hc, rfl, trivial⟩
  step := by
    intro t e u ins h _ hins hf
    obtain rfl := Option.some.inj (hins.symm.trans hc)
    rw [← h.1] at hf
    obtain ⟨m,q,ok,s,rfl,rfl⟩ := fires_wait hf
    rw [h.1]
    have ht := At.set (r := r) (v := .pred ok) (at_of_atD h hs ha)
      (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
    obtain ⟨u, hl, hu⟩ := landsU ht (seg ok) (hi ok) (hs' ok) (ha' ok)
    exact .inl (.inr ⟨dst ok, u, hn m q ok s, hl, hu⟩)

end PTX.Flow.Code
