-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutRun

@[expose] public section

/-! # Runs of local instructions checked against stated values

A proof tool for long straight-line runs of local instructions (`XItem`: the library's items and a
role's own readings), built so that the check of a run is evaluation of stated values, not a
search. A generator (`Tools/out_gen.py`) reads the PTX, cuts the run into pieces, and writes for
each piece the facts at its end as literal values: each register with the term the code computes,
in terms of the values at the start of the run. A piece is `SegD.outs_lit`: from the facts `F`
before it to the facts `G` after it, where

* every item's instruction, segment freedom and assumption reading are given item by item
  (`OAt`: a code lemma, and lemmas of the role the generator names);
* the reads, requirements, locality and coverage are Boolean checks on literals;
* `G` is the stated values, checked by `factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G`
  (evaluation: a register's value after the items is the term the items build from `F`'s values).

A piece's check uses only its own `F` and `G`, so pieces are independent and cost what their
length costs; `SegD.comp` composes them. The facts at the start of the run are `factsFrom live V`
for any value function `V` (the run is a template over the start values); `SegD.of_lookup` moves
it to the facts a role has. The condition of each piece (`xCond`: each outcome is no fault) and
the equalities of the stated terms to mathematical forms are the role's. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- The value of `r` in the fact list `F` (the first listed; a default where `r` is not listed). -/
def lookupD (F : List (Nat × Value)) (r : Nat) : Value := (F.lookup r).getD (.bits 32 0)

theorem lookup_holds {R : Nat → Option Value} :
    ∀ {F : List (Nat × Value)}, Holds R F → ∀ {r : Nat} {v : Value}, F.lookup r = some v →
      R r = some v
  | [], _, _, _, h => by simp [List.lookup] at h
  | (q, w) :: F, hH, r, v, h => by
    by_cases e : r = q
    · subst e
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact hH.1
    · have hb : (r == q) = false := by simpa using e
      simp only [List.lookup, hb] at h
      exact lookup_holds hH.2 h

theorem lookup_some : ∀ {F : List (Nat × Value)} {r : Nat}, r ∈ F.map Prod.fst →
    ∃ v, F.lookup r = some v
  | [], _, h => by simp at h
  | (q, w) :: F, r, h => by
    by_cases e : r = q
    · exact ⟨w, by simp [List.lookup, e]⟩
    · obtain ⟨v, hv⟩ := lookup_some (F := F) (r := r) (by simpa [e] using h)
      have hb : (r == q) = false := by simpa using e
      exact ⟨v, by simp only [List.lookup, hb, hv]⟩

/-- Facts by `lookupD` for listed registers hold where the listed facts hold. -/
theorem holds_lookupD {R : Nat → Option Value} {F : List (Nat × Value)} (h : Holds R F)
    {live : List Nat} (hl : live.all (fun r => (F.map Prod.fst).contains r) = true) :
    Holds R (factsFrom live (lookupD F)) := by
  refine holds_of_pointwise fun r hr => ?_
  have hk : r ∈ F.map Prod.fst := by simpa using List.all_eq_true.mp hl r hr
  obtain ⟨v, hv⟩ := lookup_some hk
  rw [show lookupD F r = v by simp [lookupD, hv]]
  exact lookup_holds h hv

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Item by item from `pc`: the item's instruction is at its pc, no assumption takes a segment
there, and the assumptions read it as `XItem.Rule` says. -/
def OAt (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) : Nat → List XItem → Prop
  | _, [] => True
  | pc, it :: its => (it.codeB K pc = true ∧ SegFreePc A pc ∧
      ∀ s : TState, s.pc = pc → it.Rule A L g s) ∧ OAt K A L g (pc + 1) its

theorem OAt.code : ∀ {pc : Nat} {items : List XItem}, OAt K A L g pc items →
    xCodeB K pc items = true
  | _, [], _ => rfl
  | _, _ :: _, h => by simp only [xCodeB, Bool.and_eq_true]; exact ⟨h.1.1, OAt.code h.2⟩

theorem OAt.rules : ∀ {pc : Nat} {items : List XItem}, OAt K A L g pc items →
    XRules A L g pc items
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨⟨h.1.2.1, h.1.2.2⟩, OAt.rules h.2⟩

/-- The code lemma `K.code[pc]? = some i` gives an item's instruction check when `i` is the
item's instruction (`hb`, by evaluation). -/
theorem XItem.codeB_of {pc : Nat} {i : Instr} {it : XItem} (h : K.code[pc]? = some i)
    (hb : OItem.instrB (some i) it.op = true) : it.codeB K pc = true := by
  simp only [XItem.codeB, h, hb]

/-- **A piece checked against stated values**: from the facts `F`, the items reach the facts `G`
under their condition (otherwise the thread is dead), where `G` is checked by evaluation. -/
theorem SegD.outs_lit {pc : Nat} {F G : List (Nat × Value)} {items : List XItem}
    (hat : OAt K A L g pc items) (hloc : xLocalB items = true)
    (hreads : xReadsB (F.map Prod.fst) items = true) (hreq : xReq (lookupD F) items = true)
    (hcov : (G.map Prod.fst).all (fun r => (xWrites items).contains r ||
      (F.map Prod.fst).contains r) = true)
    (hG : factsFrom (G.map Prod.fst) (xFinal (lookupD F) items) = G) :
    SegD K A L g items.length pc F (pc + items.length) G (xCond (lookupD F) items) := by
  have h := SegD.xouts (K := K) (A := A) (L := L) (g := g) (liveS := F.map Prod.fst)
    (liveT := G.map Prod.fst) hat.code hreads hreq hloc hat.rules (fun r hr => by
      have := List.all_eq_true.mp hcov r hr
      simpa [Bool.or_eq_true] using this)
  rw [hG] at h
  intro t ht
  exact h t ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    holds_lookupD ht.2.2.2.2 (List.all_eq_true.mpr fun r hr => by simpa using hr)⟩

/-- **The start of a run from a role's facts**: a piece from the facts `factsFrom live V` with
`V` the values `F` lists, for registers `F` lists, is a piece from `F`. -/
theorem SegD.of_lookup {n s b : Nat} {F G : List (Nat × Value)} {live : List Nat} {C : Prop}
    (h : SegD K A L g n s (factsFrom live (lookupD F)) b G C)
    (hl : live.all (fun r => (F.map Prod.fst).contains r) = true) :
    SegD K A L g n s F b G C := fun t ht =>
  h t ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_lookupD ht.2.2.2.2 hl⟩

end
end PTX.Flow
