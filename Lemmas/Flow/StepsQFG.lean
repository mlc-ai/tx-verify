-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQFP

@[expose] public section

/-! # The strict step of a possibly guarded scalar store, with a fact of the lane -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc PTX.Flow.Tagged PTX.Flow.TyG

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- The twin of `scalarStoreF` for a store that may be guarded, under `StepForQP`. -/
theorem scalarStoreFP {qt : Nat → EnvF} {Wf : Event → Prop} {P : TState → Prop} {d dn : C.D}
    {a : MemAccess} {gd : Option (Nat × Bool)}
    (hc : K.code[C.pc d]? = some ⟨gd, .mem a⟩) (hst : a.kind = .store)
    (hlen : a.srcs.length = 1) (hn : ∀ e, C.next d e = some (some dn)) (hs : C.sub d = 0)
    (ha : C.acc d = []) (hs' : C.sub dn = 0) (ha' : C.acc dn = []) (hi : C.inv dn)
    (hq : afterF qt (C.pc d) [] = true)
    (seg : SegQ K A L g (fun t => QTF qt t ∧ P t) (C.pc d + 1) (C.facts d) (C.pc dn)
      (C.facts dn)) (e : Event) : C.StepForQP (QTF qt) P Wf d e := by
  intro t u ins h _ hins hQ _ hf hPu
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨_, _, rfl, rfl⟩ := fires_st hst hf
  rw [afterStore_last (by rw [h.2.1, hs, hlen]; decide)] at hPu ⊢
  have hQ' : QTF qt { t with pc := t.pc + 1, sub := 0 } :=
    QTF.after1 hQ h.1 (by show t.pc + 1 = C.pc d + 1; rw [h.1]) (fun r _ => rfl)
      (fun p hp => by simp at hp) hq
  obtain ⟨t', hr, hg, hq'⟩ := landQ (Q := fun t => QTF qt t ∧ P t)
    (u := {t with pc := t.pc + 1, sub := 0})
    ⟨congrArg (· + 1) h.1, rfl, h.2.2.1.trans ha, h.2.2.2.1, h.2.2.2.2⟩ ⟨hQ', hPu⟩ seg hi hs' ha'
  exact .inl ⟨dn, t', hn _, hr, hg, hq'.1⟩

end PTX.Flow.Code
