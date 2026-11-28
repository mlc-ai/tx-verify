-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQOps
public import Lemmas.Flow.SegPieces

@[expose] public section

/-! # A guarded instruction whose guard fact is false is a strict step

`SegQ.skipG`: the instruction at `pc` is guarded by the predicate register `p`, which the facts
`F` hold false; it is skipped, the registers are unchanged, so the invariant `QT qt` carries over
when the tags at `pc + 1` are among those at `pc`. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem SegQ.skipG {qt : Nat → Env} {pc p : Nat} {neg pick : Bool} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨some (p, neg), op⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick)) (hg : (pick != neg) = false)
    (hF : ∀ R, Holds R F → Holds R G) (hq : tagsIn (qt (pc + 1)) (qt pc) = true) :
    SegQ K A L g (QT qt) pc F (pc + 1) G := by
  intro t ht hQ
  obtain ⟨u, hu, hAt⟩ := run_guardSkip (A := A) (L := L) (g := g) hc pick ht (hp _ ht.2.2.2.2) hg
  have hrun : run K A L g 1 t = some (skip t) := by
    have hreg := hp _ ht.2.2.2.2
    simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, hg, bind,
      Except.bind, pure, Except.pure]
  rw [hrun, Option.some.injEq] at hu
  subst hu
  refine ⟨skip t, run_rtg hrun, ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1,
    hF _ hAt.2.2.2.2⟩, ?_⟩
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  have hT := typed_of_tagsIn hq hQ'
  intro r tg hr
  rw [hAt.1] at hr
  exact hT r tg hr

/-- The same stretch, its start named by an equal program counter. -/
theorem SegQ.cast_start {Q : TState → Prop} {a a' b : Nat} {F G : List (Nat × Value)}
    (h : a = a') (hs : SegQ K A L g Q a' F b G) : SegQ K A L g Q a F b G := h ▸ hs

/-- **A branch under the negation of a predicate fact under the tag invariant**: it falls through
when the predicate holds and goes to its target when it does not; every fact is kept. -/
theorem SegQ.braNot {qt : Nat → Env} {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (pick : Bool) (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick))
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsIn (qt (if pick then pc + 1 else target)) (qt pc) = true) :
    SegQ K A L g (QT qt) pc F (if pick then pc + 1 else target) F := by
  intro t ht hQ
  have hreg := hp _ ht.2.2.2.2
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  have hT := typed_of_tagsIn hq hQ'
  cases pick with
  | true =>
    have hrun : run K A L g 1 t = some (skip t) := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure]
    refine ⟨skip t, run_rtg hrun, ⟨by simp [skip, ht.1], rfl, rfl, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
    intro r tg hr
    simp only [ite_true] at hr hT
    exact hT r tg (by simpa [skip, ht.1] using hr)
  | false =>
    have hrun : run K A L g 1 t = some { t with pc := target } := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure, hA.exec, execLocalRule_of_none (hL t), execLocal,
        Op.rule, execBranch, Op.isLocal]
    refine ⟨{ t with pc := target }, run_rtg hrun, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2⟩, ?_⟩
    intro r tg hr
    simp only [ite_false, Bool.false_eq_true] at hr hT
    exact hT r tg hr

end PTX.Flow.Havoc
