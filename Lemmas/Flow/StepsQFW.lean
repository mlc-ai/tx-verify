-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFP

@[expose] public section

/-! # A poll under `StepForQP`

`waitF` (`Lemmas/Flow/StepsQF.lean`) for the step obligation with `P` of the state after the
event. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A poll that writes the predicate `r`, with the fact `P` of the state after it. -/
theorem waitFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d : C.D}
    {dst : Bool → C.D} {r base : Nat} {off : Int} {par : Opnd} {acq : Bool} {sc : MbarScope}
    (hc : K.code[C.pc d]? = some ⟨none, .mbarWait r base off par acq sc⟩)
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m q ok s, C.next d ⟨C.pc d, .wait m q ok acq s⟩ = some (some (dst ok)))
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : ∀ ok, C.sub (dst ok) = 0)
    (ha' : ∀ ok, C.acc (dst ok) = []) (hi : ∀ ok, C.inv (dst ok))
    (hq : afterF qt (C.pc d) [(r, .old .pred)] = true)
    (seg : ∀ ok, SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1)
      ((r, .pred ok) :: C.facts d) (C.pc (dst ok)) (C.facts (dst ok))) (e : Event) :
    C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hins hQ _ hf hPu
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  rw [← h.1] at hf
  obtain ⟨m, q, ok, s, rfl, rfl⟩ := fires_wait hf
  rw [h.1]
  have ht := At.set (r := r) (v := .pred ok) (at_of_atD h hs ha)
    (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
  have hQ' : QTF qt (PTX.next (setReg t r (.pred ok))) :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1])
      (fun r' hr' => by simp [PTX.next, setReg, Function.update_of_ne (by simpa using hr')])
      (fun p hp => by
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨ok, by simp [PTX.next, setReg]⟩) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t) ht ⟨hQ', hPu⟩ (seg ok)
    (hi ok) (hs' ok) (ha' ok)
  exact .inl ⟨dst ok, t', hn m q ok s, hr, hg, hq'.1⟩

end PTX.Flow.Code
