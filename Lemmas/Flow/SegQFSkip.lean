-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQSkip
public import Lemmas.Flow.SegQFH

@[expose] public section

/-! # Skipped instructions and negated branches under the float tag invariant

The twins of `SegQ.skipG` and `SegQ.braNot` (`Lemmas/Flow/SegQSkip.lean`) for `QTF qt`. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A guarded instruction whose guard fact is false is a strict step. -/
theorem SegQF.skipG {qt : Nat → EnvF} {pc p : Nat} {neg pick : Bool} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨some (p, neg), op⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick)) (hg : (pick != neg) = false)
    (hF : ∀ R, Holds R F → Holds R G) (hq : tagsInF (qt (pc + 1)) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F (pc + 1) G := by
  intro t ht hQ
  obtain ⟨u, hu, hAt⟩ := run_guardSkip (A := A) (L := L) (g := g) hc pick ht (hp _ ht.2.2.2.2) hg
  have hrun : run K A L g 1 t = some (skip t) := by
    simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hp _ ht.2.2.2.2, hg, bind,
      Except.bind, pure, Except.pure]
  rw [hrun, Option.some.injEq] at hu
  subst hu
  refine ⟨skip t, run_rtg hrun, ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, hF _ hAt.2.2.2.2⟩, ?_⟩
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  have := typedF_of_tagsIn hq hT
  exact fun r tg hr => this r tg (by simpa [skip, ht.1] using hr)

/-- A branch under the negation of a predicate fact: it falls through when the predicate holds
and goes to its target when it does not; every fact is kept. -/
theorem SegQF.braNot {qt : Nat → EnvF} {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (pick : Bool) (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick))
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsInF (qt (if pick then pc + 1 else target)) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F (if pick then pc + 1 else target) F := by
  intro t ht hQ
  have hreg := hp _ ht.2.2.2.2
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  have hT' := typedF_of_tagsIn hq hT
  cases pick with
  | true =>
    have hrun : run K A L g 1 t = some (skip t) := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure]
    refine ⟨skip t, run_rtg hrun, ⟨by simp [skip, ht.1], rfl, rfl, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
    exact fun r tg hr => hT' r tg (by simpa [skip, ht.1] using hr)
  | false =>
    have hrun : run K A L g 1 t = some { t with pc := target } := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure, hA.exec, execLocalRule_of_none (hL t), execLocal,
        Op.rule, execBranch, Op.isLocal]
    refine ⟨{ t with pc := target }, run_rtg hrun, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2⟩, ?_⟩
    exact fun r tg hr => hT' r tg (by simpa using hr)

/-- An unconditional branch under the float tag invariant. -/
theorem SegQF.jmp {qt : Nat → EnvF} {pc target : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .bra target uni⟩)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) (hq : tagsInF (qt target) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F target F := by
  intro t ht hQ
  have hr : run K A L g 1 t = some { t with pc := target } := by
    simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, pure, Except.pure, hA.exec,
      execLocalRule_of_none (hL t ht.1), execLocal, Op.rule, execBranch, Op.isLocal]
  refine ⟨{ t with pc := target }, run_rtg hr, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  exact fun r tg h => typedF_of_tagsIn hq hT r tg h

end PTX.Flow.TyG
