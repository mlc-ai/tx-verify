-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutRunCond
public import Lemmas.Flow.SegDead
public import Lemmas.Flow.RunFrame
public import Lemmas.Flow.ItemsU

@[expose] public section

/-! # Local paths through a piece

`SegD` says what a piece does from its start: under its condition the steps reach its end, else
the thread is dead. A state the local steps reach beyond the piece (a state of the lane between two
events) tells more: the piece's condition holds (the steps went through it) and the state goes on
from the piece's end. `PathD n s F b G C` is that statement: every state at pc `b` or beyond that
the local steps reach from a state at `s` with facts `F` satisfies `C` and is reached from the end
`run n` of the piece, which has the facts `G`. Pieces compose when the end of the first is not
beyond the end of the second (`PathD.comp`); a generated piece (`PathD.outs_lit`) is a path by
`xRun_path`, a single step is one when its pc moves forward (`PathD.of_seg1`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Every state beyond the piece that the local steps reach is reached from its end. -/
def PathD (K : Kernel) (A : List Assumption) (L : Launch) (g n s : Nat) (F : List (Nat × Value))
    (b : Nat) (G : List (Nat × Value)) (C : Prop) : Prop :=
  ∀ t, At t s F → ∀ t', Relation.ReflTransGen (Tau K A L g) t t' → b ≤ t'.pc →
    C ∧ ∃ t1, run K A L g n t = some t1 ∧ At t1 b G ∧ Relation.ReflTransGen (Tau K A L g) t1 t'

namespace PathD

/-- Two paths that meet at a checkpoint not beyond the end of the second. -/
theorem comp {m n s p b : Nat} {F G H : List (Nat × Value)} {C₁ C₂ : Prop}
    (h1 : PathD K A L g m s F p G C₁) (h2 : PathD K A L g n p G b H C₂) (hpb : p ≤ b) :
    PathD K A L g (m + n) s F b H (C₁ ∧ C₂) := by
  intro t ht t' hr hb
  obtain ⟨c1, t1, r1, a1, q1⟩ := h1 t ht t' hr (hpb.trans hb)
  obtain ⟨c2, t2, r2, a2, q2⟩ := h2 t1 a1 t' q1 hb
  exact ⟨⟨c1, c2⟩, t2, run_comp r1 r2, a2, q2⟩

/-- The same path from more facts, to fewer or restated ones. -/
theorem weaken {n s b : Nat} {F F' G G' : List (Nat × Value)} {C : Prop}
    (h : PathD K A L g n s F b G C) (hF : ∀ R, Holds R F' → Holds R F)
    (hG : ∀ R, Holds R G → Holds R G') : PathD K A L g n s F' b G' C := by
  intro t ht t' hr hb
  obtain ⟨c, t1, r1, a1, q1⟩ := h t (At.mono ht (hF _ ht.2.2.2.2)) t' hr hb
  exact ⟨c, t1, r1, At.mono a1 (hG _ a1.2.2.2.2), q1⟩

/-- A single exact step whose pc moves forward. -/
theorem of_seg1 {s b : Nat} {F G : List (Nat × Value)} (h : Seg K A L g 1 s F b G)
    (hsb : s < b) : PathD K A L g 1 s F b G True := by
  intro t ht t' hr hb
  obtain ⟨u, hu, hAt⟩ := h t ht
  refine ⟨trivial, u, hu, hAt, ?_⟩
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨c, hc, hct⟩
  · exact absurd (ht.1 ▸ hsb) (by omega)
  · have e : tauStep K A L g t = some c := tauStep_iff.mpr hc
    simp only [run, e, Option.bind_some] at hu
    exact (Option.some.inj hu) ▸ hct

/-- The same path under a weaker condition. -/
theorem mono_cond {n s b : Nat} {F G : List (Nat × Value)} {C C' : Prop}
    (h : PathD K A L g n s F b G C) (hC : C → C') : PathD K A L g n s F b G C' :=
  fun t ht t' hr hb => let ⟨c, r⟩ := h t ht t' hr hb; ⟨hC c, r⟩

/-- **A path with facts on registers its code does not write**: the facts `H` hold at both
ends. -/
theorem frame (hA : RulesFrame A) {n s b : Nat} {F G H : List (Nat × Value)} {C : Prop}
    {ins : List Instr} (h : PathD K A L g n s F b G C) (hcode : (K.code.drop s).take n = ins)
    (hlen : ins.length = n) (hB : frameB ins (H.map Prod.fst) = true)
    (hS : ∀ i < n, Assumption.SegFreePc A (s + i)) :
    PathD K A L g n s (F ++ H) b (G ++ H) C := by
  intro t ht t' hr hb
  have hF : At t s F := At.mono ht ((holds_append _ _ _).mp ht.2.2.2.2).1
  obtain ⟨c, t1, r1, a1, q1⟩ := h t hF t' hr hb
  refine ⟨c, t1, r1, ⟨a1.1, a1.2.1, a1.2.2.1, a1.2.2.2.1, (holds_append _ _ _).mpr
    ⟨a1.2.2.2.2, ?_⟩⟩, q1⟩
  have hH := ((holds_append _ _ _).mp ht.2.2.2.2).2
  have hfr := run_frame hA n s ins t t1 hcode hlen hB hS ht.1 ht.2.2.2.1 r1
  refine holds_of_mem fun r v hrv => ?_
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) hrv)]
  exact holds_mem hH hrv

/-- **A run of items** from facts by `V` to facts by the values after the run. -/
theorem of_items {pc : Nat} {items : List XItem} {liveS liveT : List Nat} {V : Nat → Value}
    (hat : OAt K A L g pc items) (hloc : xLocalB items = true)
    (hreads : xReadsB liveS items = true) (hreq : xReq V items = true)
    (hcov : ∀ r ∈ liveT, r ∈ xWrites items ∨ r ∈ liveS) :
    PathD K A L g items.length pc (factsFrom liveS V) (pc + items.length)
      (factsFrom liveT (xFinal V items)) (xCond V items) := by
  intro t ht t' hr hb
  obtain ⟨j, hj, t1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := xRun_path items V liveS t
    (by rw [ht.1]; exact hat.code) ht.2.2.2.1
    (fun r hr' => holds_mem ht.2.2.2.2 (mem_factsFrom hr')) hreads hreq hloc
    (by rw [ht.1]; exact hat.rules) t' hr
  have hjl : j = items.length := by
    by_contra hne
    have e : t1 = t' := h2.resolve_left hne
    subst e
    have := ht.1
    omega
  subst hjl
  rw [List.take_length] at h8 h9 h10
  refine ⟨h8, t1, h3, ⟨by rw [h4, ht.1], h5.trans ht.2.1, h6.trans ht.2.2.1,
    h7.trans ht.2.2.2.1, holds_of_pointwise fun r hr' => h10 r ?_⟩, h1⟩
  rcases hcov r hr' with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

/-- **A piece of items** as a path: the states beyond it come from its end. -/
theorem outs_lit {pc : Nat} {F G : List (Nat × Value)} {items : List XItem}
    (hat : OAt K A L g pc items) (hloc : xLocalB items = true)
    (hreads : xReadsB (F.map Prod.fst) items = true) (hreq : xReq (lookupD F) items = true)
    (hcov : (G.map Prod.fst).all (fun r => (xWrites items).contains r ||
      (F.map Prod.fst).contains r) = true)
    (hG : factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G) :
    PathD K A L g items.length pc F (pc + items.length) G (xCond (lookupD F) items) := by
  intro t ht t' hr hb
  have hF : Holds t.regs (factsFrom (F.map Prod.fst) (lookupD F)) :=
    holds_lookupD ht.2.2.2.2 (List.all_eq_true.mpr fun r hr => by simpa using hr)
  obtain ⟨j, hj, t1, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := xRun_path items (lookupD F)
    (F.map Prod.fst) t (by rw [ht.1]; exact hat.code) ht.2.2.2.1
    (fun r hr' => holds_mem hF (mem_factsFrom hr')) hreads hreq hloc
    (by rw [ht.1]; exact hat.rules) t' hr
  have hjl : j = items.length := by
    by_contra hne
    have e : t1 = t' := h2.resolve_left hne
    subst e
    have := ht.1
    omega
  subst hjl
  rw [List.take_length] at h8 h9 h10
  refine ⟨h8, t1, h3, ⟨by rw [h4, ht.1], h5.trans ht.2.1, h6.trans ht.2.2.1,
    h7.trans ht.2.2.2.1, ?_⟩, h1⟩
  rw [← hG]
  refine holds_of_pointwise fun r hr' => h10 r ?_
  have := List.all_eq_true.mp hcov r hr'
  simp only [Bool.or_eq_true, List.contains_iff_mem] at this
  rcases this with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

end PathD
end
end PTX.Flow
