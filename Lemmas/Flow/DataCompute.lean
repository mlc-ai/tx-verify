-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataCarry
public import Lemmas.Flow.ReachSegU

@[expose] public section

/-! # A `Reach` of carried facts and facts a control segment computes

A proof tool, generic over the kernel. From facts `F` at `p`, the first state that performs an
event holds the facts `C` that the code from `p` on does not write (`Reach.region`) and the facts
`N` that a segment to `q` computes (`SegU`) and the code from `q` on does not write; so it holds
every fact `G` that is in one of them (`Reach.carry_new`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem Reach.carry_new (hA : RulesFrame A) {p q : Nat} {F G0 C N G : List (Nat × Value)}
    (hC : regionB K p 574 (C.map Prod.fst) = true) (hN : regionB K q 574 (N.map Prod.fst) = true)
    (hS : ∀ pc, p ≤ pc → pc ≤ 574 → Assumption.SegFreePc A pc) (hpq : p ≤ q) (hq : q ≤ 574)
    (hFC : ∀ R, Holds R F → Holds R C) (hseg : SegU K A L g p F q G0)
    (hGN : ∀ R, Holds R G0 → Holds R N) (hG : ∀ x ∈ G, x ∈ C ∨ x ∈ N) : Reach K A L g p F G := by
  have hS' : ∀ pc, q ≤ pc → pc ≤ 574 → Assumption.SegFreePc A pc := fun pc h1 h2 =>
    hS pc (by omega) h2
  have r1 : Reach K A L g p F C := Reach.region hA hC hS le_rfl (by omega) hFC
  have r2 : Reach K A L g p F N :=
    SegU.reach_then hseg (Reach.region hA hN hS' le_rfl hq hGN)
  intro u hu
  rcases r1 u hu with a | d
  · rcases r2 u hu with b | d
    · refine .inl fun t' hr hs => holds_of_mem fun r v hm => ?_
      rcases hG _ hm with h | h
      · exact holds_mem (a t' hr hs) h
      · exact holds_mem (b t' hr hs) h
    · exact .inr d
  · exact .inr d

/-- A segment's goal may be narrowed to some of its facts. -/
theorem SegU.mono_goal {s q : Nat} {F G G' : List (Nat × Value)} (h : SegU K A L g s F q G)
    (hG : ∀ x ∈ G', x ∈ G) : SegU K A L g s F q G' := by
  intro t ht
  rcases h t ht with ⟨u, hr, hu⟩ | hd
  · exact .inl ⟨u, hr, At.mono hu (holds_of_mem fun r v hm => holds_mem hu.2.2.2.2 (hG _ hm))⟩
  · exact .inr hd

end
end PTX.Flow.Code

namespace PTX.Flow
open PTX PTX.Proof

/-- A register written with a new value joins the facts that do not name it. -/
theorem holds_update_cons {R : Nat → Option Value} {F : List (Nat × Value)} {r : Nat} {x : Value}
    (h : Holds R F) (hn : r ∉ F.map Prod.fst) :
    Holds (Function.update R r (some x)) ((r, x) :: F) := by
  refine ⟨Function.update_self .., holds_of_mem fun r' v' hm => ?_⟩
  have hne : r' ≠ r := fun e => hn (by
    subst e; exact List.mem_map_of_mem (f := Prod.fst) hm)
  rw [Function.update_of_ne hne]
  exact holds_mem h hm

/-- Two registers written with new values keep the facts that do not name them. -/
theorem holds_update_update {R : Nat → Option Value} {F : List (Nat × Value)} {r p : Nat}
    {x y : Value} (h : Holds R F) (hr : r ∉ F.map Prod.fst) (hp : p ∉ F.map Prod.fst) :
    Holds (Function.update (Function.update R r (some x)) p (some y)) F := by
  refine holds_of_mem fun r' v' hm => ?_
  have h1 : r' ≠ p := fun e => hp (by subst e; exact List.mem_map_of_mem (f := Prod.fst) hm)
  have h2 : r' ≠ r := fun e => hr (by subst e; exact List.mem_map_of_mem (f := Prod.fst) hm)
  rw [Function.update_of_ne h1, Function.update_of_ne h2]
  exact holds_mem h hm

end PTX.Flow
