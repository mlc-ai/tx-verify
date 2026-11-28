-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFP

@[expose] public section

/-! # `advanceFP` for an instruction whose continuation reads the pc of the state

A tensor-memory store continues at the next pc when no assumption makes it wait on a load, a
fact about `t.pc`; the twin of `advanceFP` hands that equation to the continuation lemma. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem advanceFPt {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d dn : C.D}
    {op : Op} {gd : Option (Nat × Bool)} (hc : K.code[C.pc d]? = some ⟨gd, op⟩)
    (ha : ∀ {t u e}, t.pc = C.pc d → Fires (C.pc d) (eventTmpl A L g t op) e (some u) →
      u = PTX.next t)
    (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0) (hacc : C.acc d = [])
    (hs' : C.sub dn = 0) (hacc' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (seg : SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) (C.facts d) (C.pc dn)
      (C.facts dn)) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hins hQ _ hf hPu
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := ha h.1 hf
  have hQ' : QTF qt (PTX.next t) :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r _ => rfl)
      (fun p hp => by simp at hp) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t)
    (At.next (at_of_atD h hs hacc)) ⟨hQ', hPu⟩ seg hi hs' hacc'
  exact .inl ⟨dn, t', hn e, hr, hg, hq'.1⟩

end PTX.Flow.Code
