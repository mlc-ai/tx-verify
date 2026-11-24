-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CodeU
public import Lemmas.Flow.Havoc
public import Lemmas.Flow.Step.Combinators

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem goodU_of_dead (d : C.D) {u : TState}
    (hd : Machine.Dead (K := K) (A := A) (L := L) (g := g) u) :
    ∃ s, Relation.ReflTransGen (Tau K A L g) u s ∧ C.GoodU (some d) s := by
  obtain ⟨s, f, hl, hf⟩ := hd
  exact ⟨s, hl, Or.inr ⟨f, hf⟩⟩

theorem landsU {d : C.D} {u : TState} {a : Nat} {F : List (Nat × Value)}
    (hu : At u a F) (hl : SegU K A L g a F (C.pc d) (C.facts d)) (hi : C.inv d)
    (hs : C.sub d = 0) (ha : C.acc d = []) :
    ∃ s, Relation.ReflTransGen (Tau K A L g) u s ∧ C.GoodU (some d) s := by
  rcases hl u hu with ⟨s, ht, hp, hsub, hacc, hf, hF⟩ | hd
  · exact ⟨s, ht, Or.inl ⟨⟨hp, hsub.trans hs.symm, hacc.trans ha.symm, hf, hF⟩, hi⟩⟩
  · exact goodU_of_dead d hd

/-- Ignore the destination of a scalar load. Malformed bytes can fault immediately and a
successfully rebuilt value can fault during the subsequent local instructions. -/
theorem step_loadU {d d' : C.D} {a : MemAccess} {r : Nat}
    (hc : K.code[C.pc d]? = some ⟨none, .mem a⟩) (hl : (Op.mem a).isLocal = false)
    (hk : a.kind = .load) (hnc : a.nc = false) (he : a.ext = .same) (hr : a.regs = [r])
    (hs : C.sub d = 0) (ha : C.acc d = []) (hs' : C.sub d' = 0) (ha' : C.acc d' = [])
    (hn : ∀ x bs, C.next d ⟨C.pc d, .rd x bs⟩ = some (some d')) (hi : C.inv d')
    (hoff : r ∉ (C.facts d).map Prod.fst)
    (hseg : SegU K A L g (C.pc d + 1) (C.facts d) (C.pc d') (C.facts d')) : C.StepAtU d where
  site := fun _ => ⟨_, hc, hl, trivial⟩
  step := by
    intro t e u ins hat _ hc' hf
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain ⟨x, bs, rfl, rfl⟩ := fires_load hk hnc hf he
    refine .inl (.inr ⟨d', ?_⟩)
    rw [hr]
    suffices h : ∃ s, Relation.ReflTransGen (Tau K A L g) (afterLoad t [r] bs) s ∧
        C.GoodU (some d') s by
      obtain ⟨s, h⟩ := h
      exact ⟨s, hn x bs, h⟩
    cases hv : rebuild 3 bs with
    | error f =>
      apply goodU_of_dead
      exact Machine.dead_of_fault (f := f) (by simp only [afterLoad, hv])
    | ok v =>
      have ht := at_of_atD hat hs ha
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
      apply landsU _ hseg hi hs' ha'
      exact ⟨congrArg (· + 1) ht.1, rfl, rfl, ht.2.2.2.1,
        holds_update ht.2.2.2.2 fun p hp he => hoff (he ▸ List.mem_map_of_mem hp)⟩

end PTX.Flow.Code
