-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc

@[expose] public section

/-! # Strict segments under an invariant

`SegQ Q a F b G`: from a state at `a` with facts `F` satisfying the invariant `Q`, local steps
reach a state at `b` with facts `G` that satisfies `Q`. Unlike `SegU` there is no dead
alternative: the landing is certain, which is what a strict window needs. The invariant is meant
to carry what the facts do not (that the registers a havoc stretch reads are defined). -/

namespace PTX.Flow

open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

def SegQ (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) (Q : TState → Prop)
    (a : Nat) (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) : Prop :=
  ∀ t, At t a F → Q t → ∃ u, Relation.ReflTransGen (Tau K A L g) t u ∧ At u b G ∧ Q u

variable {Q : TState → Prop} {a b c n : Nat} {F G H : List (Nat × Value)}

theorem SegQ.comp (h : SegQ K A L g Q a F b G) (h' : SegQ K A L g Q b G c H) :
    SegQ K A L g Q a F c H := by
  intro t ht hq
  obtain ⟨u, hr, hu, hqu⟩ := h t ht hq
  obtain ⟨s, hr', hs, hqs⟩ := h' u hu hqu
  exact ⟨s, hr.trans hr', hs, hqs⟩

/-- A strict segment that keeps the invariant. -/
theorem SegQ.of_seg (h : Seg K A L g n a F b G) (hq : ∀ {t u}, At t a F → Q t →
    Relation.ReflTransGen (Tau K A L g) t u → At u b G → Q u) : SegQ K A L g Q a F b G := by
  intro t ht hQ
  obtain ⟨u, hr, hu⟩ := h t ht
  have hr' := run_rtg hr
  exact ⟨u, hr', hu, hq ht hQ hr' hu⟩

/-- The segment of a state whose invariant does not change. -/
theorem SegQ.of_seg_inv (h : Seg K A L g n a F b G)
    (hq : ∀ {t u}, At t a F → Relation.ReflTransGen (Tau K A L g) t u → Q t → Q u) :
    SegQ K A L g Q a F b G :=
  SegQ.of_seg h fun ht hQ hr _ => hq ht hr hQ

end PTX.Flow
