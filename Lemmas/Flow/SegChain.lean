-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs

@[expose] public section

/-! # Segments chained at checkpoints

A proof tool. `Seg K A L g n s F b G` says: from every state at instruction `s` whose
registers satisfy `F`, `n` local steps reach a state at `b` whose registers satisfy `G`. It is
the statement `seg_fp h using tac` proves after `intro t h`, so a long local segment can be
cut at intermediate program counters (checkpoints) with intermediate facts, each piece proved
by `seg_fp` on its own, in its own file, and the pieces composed (`Seg.comp`, `seg_chain`).
The facts at a checkpoint are the kernel's choice, typically the registers live there valued
by the same table as the sites (`factsFrom (Flow.live mid) (valueOf …)`).

A piece may also be one branch on a predicate fact (`Seg.bra`), so a segment through a
conditional branch on a symbolic predicate is a chain: a piece up to the branch, the branch
with the predicate's value from the facts, a piece after it. A checkpoint's facts can be
restated (`Seg.weaken_end`, `Seg.weaken_start`), for instance after a case split on a value
the evaluation cannot decide. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- From every state at `s` with facts `F`, `n` local steps reach a state at `b` with facts
`G`. -/
def Seg (K : Kernel) (A : List Assumption) (L : Launch) (g n s : Nat)
    (F : List (Nat × Value)) (b : Nat) (G : List (Nat × Value)) : Prop :=
  ∀ t, At t s F → ∃ t', run K A L g n t = some t' ∧ At t' b G

namespace Seg

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem apply {n s b : Nat} {F G : List (Nat × Value)} (hs : Seg K A L g n s F b G)
    {t : TState} (h : At t s F) : ∃ t', run K A L g n t = some t' ∧ At t' b G :=
  hs t h

/-- No step. -/
theorem refl (s : Nat) (F : List (Nat × Value)) : Seg K A L g 0 s F s F :=
  fun t h => ⟨t, rfl, h⟩

/-- Two pieces that meet at a checkpoint. -/
theorem comp {m n s p b : Nat} {F G H : List (Nat × Value)} (h1 : Seg K A L g m s F p G)
    (h2 : Seg K A L g n p G b H) : Seg K A L g (m + n) s F b H := by
  intro t h
  obtain ⟨t1, hr1, h1'⟩ := h1 t h
  obtain ⟨t2, hr2, h2'⟩ := h2 t1 h1'
  exact ⟨t2, run_comp hr1 hr2, h2'⟩

/-- The same piece with its length written differently. -/
theorem of_len {m n s b : Nat} {F G : List (Nat × Value)} (h : Seg K A L g m s F b G)
    (hmn : m = n) : Seg K A L g n s F b G :=
  hmn ▸ h

/-- Fewer or restated facts at the end. -/
theorem weaken_end {n s b : Nat} {F G G' : List (Nat × Value)} (h : Seg K A L g n s F b G)
    (hG : ∀ R, Holds R G → Holds R G') : Seg K A L g n s F b G' := by
  intro t ht
  obtain ⟨t', hr, h'⟩ := h t ht
  exact ⟨t', hr, At.mono h' (hG _ h'.2.2.2.2)⟩

/-- More or restated facts at the start. -/
theorem weaken_start {n s b : Nat} {F F' G : List (Nat × Value)} (h : Seg K A L g n s F b G)
    (hF : ∀ R, Holds R F' → Holds R F) : Seg K A L g n s F' b G :=
  fun t ht => h t (At.mono ht (hF _ ht.2.2.2.2))

/-- A case split at the start: a segment from facts `F` that holds under each of two
hypotheses about the facts. -/
theorem cases {n s b : Nat} {F G : List (Nat × Value)} (P : Prop)
    (h1 : P → Seg K A L g n s F b G) (h2 : ¬ P → Seg K A L g n s F b G) :
    Seg K A L g n s F b G := by
  by_cases hp : P
  · exact h1 hp
  · exact h2 hp

/-- A conditional branch on a predicate fact `(p, .pred pick)`: one step to the target or to
the next instruction, keeping every fact. No assumption of `A` names the branch (`hL`). -/
theorem bra {pc target p : Nat} {uni pick : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : (p, Value.pred pick) ∈ F)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc := by seg_free_pc) :
    Seg K A L g 1 pc F (if pick then target else pc + 1) F :=
  fun t h => run_bra hc pick h (holds_mem h.2.2.2.2 hp) (hL t h.1) hA

/-- A segment is a sequence of local steps. -/
theorem rtg {n s b : Nat} {F G : List (Nat × Value)} (hs : Seg K A L g n s F b G)
    {t : TState} (h : At t s F) :
    ∃ t', Relation.ReflTransGen (Tau K A L g) t t' ∧ At t' b G := by
  obtain ⟨t', hr, h'⟩ := hs t h
  exact ⟨t', run_rtg hr, h'⟩

end Seg

/-- `seg_chain h [p₁, …, pₖ]` closes `∃ t', run K A L g n t = some t' ∧ At t' b G` from
`h : At t s F` and pieces `pᵢ : Seg K A L g nᵢ sᵢ Fᵢ bᵢ Gᵢ` that meet at their checkpoints
(`bᵢ = sᵢ₊₁`, `Gᵢ = Fᵢ₊₁`), when `n₁ + … + nₖ = n`. -/
syntax "seg_chain " term:max " [" term,+ "]" : tactic

macro_rules
  | `(tactic| seg_chain $h [$ps,*]) => do
    let ps := ps.getElems
    let mut acc := ps.back!
    for p in ps.pop.reverse do
      acc ← `(PTX.Flow.Seg.comp $p $acc)
    `(tactic| exact PTX.Flow.Seg.apply (PTX.Flow.Seg.of_len $acc (by first | rfl | omega)) $h)

end

end PTX.Flow
