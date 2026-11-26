-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.HavocTyped
public import Lemmas.Flow.BranchU
public import Lemmas.Flow.RunFrame

@[expose] public section

/-! # Strict segments under a tag invariant: branches and changes of table

* `SegQ.pick`: a segment may name one of its facts first.
* `SegQ.branch`: a branch on a predicate fact is a strict segment under `QT qt`, when the tags of
  the target's table are among those of the branch's (`tagsIn`).
* `SegQ.map`: a segment under one invariant is a segment under another that the states at its two
  ends relate (the divisors' nonzero tags enter this way). -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The tags `e'` are among the tags `e`. -/
def tagsIn (e' e : Env) : Bool := e'.all fun p => e.lookup p.1 == some p.2

theorem typed_of_tagsIn {e e' : Env} {t : TState} (h : tagsIn e' e = true) (ht : Typed e t) :
    Typed e' t := by
  intro r tg hr
  have hm := lookup_mem hr
  simp only [tagsIn, List.all_eq_true, beq_iff_eq] at h
  exact ht r tg (h _ hm)

theorem SegQ.pick {Q : TState → Prop} {a b : Nat} {F G : List (Nat × Value)} {r : Nat}
    {x : Value} (hm : (r, x) ∈ F) (h : SegQ K A L g Q a ((r, x) :: F) b G) :
    SegQ K A L g Q a F b G := fun t ht hq =>
  h t ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, holds_mem ht.2.2.2.2 hm, ht.2.2.2.2⟩ hq

theorem run_bra_regs {t : TState} {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩) (pick : Bool) (h : At t pc F)
    (hp : t.regs p = some (.pred pick))
    (hL : ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) :
    ∃ u, run K A L g 1 t = some u ∧ u.regs = t.regs ∧
      At u (if pick then target else pc + 1) F := by
  cases pick with
  | false =>
    refine ⟨skip t, ?_, rfl, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure]
  | true =>
    refine ⟨{t with pc := target}, ?_, rfl, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind, pure,
      Except.pure, hA.exec, execLocalRule_of_none hL, execLocal, Op.rule, execBranch, Op.isLocal]

/-- **A branch under the tag invariant.** -/
theorem SegQ.branch {qt : Nat → Env} {pc pred target : Nat} {uni : Bool}
    {F : List (Nat × Value)} (pick : Bool)
    (hc : K.code[pc]? = some ⟨some (pred, false), .bra target uni⟩)
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsIn (qt (if pick then target else pc + 1)) (qt pc) = true) :
    SegQ K A L g (QT qt) pc ((pred, .pred pick) :: F) (if pick then target else pc + 1) F := by
  intro t ht hQ
  obtain ⟨u, hl, hr, hu⟩ := run_bra_regs hc pick ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    ht.2.2.2.2.2⟩ ht.2.2.2.2.1 (hL t) hA
  refine ⟨u, run_rtg hl, hu.mono hu.2.2.2.2, ?_⟩
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  have : Typed (qt (if pick then target else pc + 1)) u := by
    intro r tg hr'
    rw [hr]
    exact typed_of_tagsIn hq hQ' r tg hr'
  simpa [QT, hu.1] using this

/-- A segment under one invariant is a segment under another, when they agree at its ends. -/
theorem SegQ.map {Q Q' : TState → Prop} {a b : Nat} {F G : List (Nat × Value)}
    (h : SegQ K A L g Q a F b G) (h0 : ∀ t, At t a F → Q' t → Q t)
    (h1 : ∀ t, At t b G → Q t → Q' t) : SegQ K A L g Q' a F b G := by
  intro t ht hq
  obtain ⟨u, hr, hu, hQ⟩ := h t ht (h0 t ht hq)
  exact ⟨u, hr, hu, h1 u hu hQ⟩

/-- **An exact piece that does not touch the tagged registers**: a strict segment whose stretch
writes none of the registers `qt b` tags (checked by `frameB`), and whose tags are among those
of `qt a`. -/
theorem SegQ.of_seg_frame {qt : Nat → Env} {a b n : Nat} {F G : List (Nat × Value)}
    (hA : RulesFrame A) (hseg : Seg K A L g n a F b G) (hn : n = b - a) (hlen : b ≤ K.code.length)
    (hab : a ≤ b) (hS : PlainSegs A a b)
    (hB : frameB ((K.code.drop a).take n) ((qt b).map Prod.fst) = true)
    (hq : tagsIn (qt b) (qt a) = true) : SegQ K A L g (QT qt) a F b G := by
  intro t ht hQ
  obtain ⟨u, hu, hAt⟩ := hseg t ht
  have hlen' : ((K.code.drop a).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  have hfr := run_frame hA n a _ t u rfl hlen' hB (fun i hi => hS (a + i) (by omega) (by omega))
    ht.1 ht.2.2.2.1 hu
  refine ⟨u, run_rtg hu, hAt, ?_⟩
  have hQ' : Typed (qt a) t := by simpa [QT, ht.1] using hQ
  have hT := typed_of_tagsIn hq hQ'
  intro r tg hr
  rw [hAt.1] at hr
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) (lookup_mem hr))]
  exact hT r tg hr

/-- A branch under the tag invariant whose target's tags may include some that the state's
facts give (`ex`). -/
theorem SegQ.branchEx {qt : Nat → Env} {pc pred target : Nat} {uni : Bool} {ex : Env}
    {F : List (Nat × Value)} (pick : Bool)
    (hc : K.code[pc]? = some ⟨some (pred, false), .bra target uni⟩)
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hex : ∀ t : TState, Holds t.regs F → Typed ex t)
    (hq : ∀ x ∈ qt (if pick then target else pc + 1),
      (qt pc).lookup x.1 = some x.2 ∨ ex.lookup x.1 = some x.2) :
    SegQ K A L g (QT qt) pc ((pred, .pred pick) :: F) (if pick then target else pc + 1) F := by
  intro t ht hQ
  obtain ⟨u, hl, hr, hu⟩ := run_bra_regs hc pick ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1,
    ht.2.2.2.2.2⟩ ht.2.2.2.2.1 (hL t) hA
  refine ⟨u, run_rtg hl, hu.mono hu.2.2.2.2, ?_⟩
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  have hE : Typed ex t := hex t ht.2.2.2.2.2
  have : Typed (qt (if pick then target else pc + 1)) u := by
    intro r tg hr'
    rw [hr]
    rcases hq _ (lookup_mem hr') with h | h
    · exact hQ' r tg h
    · exact hE r tg h
  simpa [QT, hu.1] using this

/-- A fact whose bit pattern is nonzero tags its register `nz`. -/
theorem typed_nz_of_fact {F : List (Nat × Value)} {t : TState} {r w : Nat} {x : BitVec 64}
    (hm : (r, .bits w x) ∈ F) (hz : x.toNat % 2 ^ w ≠ 0) (h : Holds t.regs F) :
    Typed [(r, .nz w)] t := by
  intro r' tg hl
  simp only [List.lookup] at hl
  split at hl
  · rename_i hr
    simp only [beq_iff_eq] at hr
    simp only [Option.some.injEq] at hl
    subst hl; subst hr
    exact ⟨x, holds_mem h hm, hz⟩
  · simp at hl

end PTX.Flow.Havoc
