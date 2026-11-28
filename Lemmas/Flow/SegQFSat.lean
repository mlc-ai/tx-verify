-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFSkip

@[expose] public section

/-! # Jumps to a join under the float tag invariant (`tagsSatF`)

At a join the table of the target is the weakest tag the predecessors have in common (a
`.old (.bits 64)` serves `.dat64`, a `.old (.bits 32)` serves `.dat32`), so it need not be an
entry of the table of the jump: `tagsSatF tgt src` asks that every entry of `tgt` is served by the
tag of `src` (`TagF.sat`). The twins of `SegQF.skipG`, `SegQF.braNot` and `SegQF.jmp`
(`Lemmas/Flow/SegQFSkip.lean`) with this check. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- Every tag of `e'` is served by the tag `e` has for the register. -/
def tagsSatF (e' e : EnvF) : Bool := e'.all fun p => TagF.sat (e.lookup p.1) p.2

theorem typedF_of_tagsSat {e e' : EnvF} {t : TState} (h : tagsSatF e' e = true)
    (ht : TypedF e t) : TypedF e' t := by
  intro r tg hr
  have hs := List.all_eq_true.mp h _ (lookup_mem' hr)
  exact TagF.sat_ok hs (fun tg' h' => ht r tg' h')

/-- A guarded instruction whose guard fact is false is a strict step. -/
theorem SegQF.skipGS {qt : Nat → EnvF} {pc p : Nat} {neg pick : Bool} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨some (p, neg), op⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick)) (hg : (pick != neg) = false)
    (hF : ∀ R, Holds R F → Holds R G) (hq : tagsSatF (qt (pc + 1)) (qt pc) = true) :
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
  have := typedF_of_tagsSat hq hT
  exact fun r tg hr => this r tg (by simpa [skip, ht.1] using hr)

/-- A branch under the negation of a predicate fact: it falls through when the predicate holds
and goes to its target when it does not; every fact is kept. -/
theorem SegQF.braNotS {qt : Nat → EnvF} {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (pick : Bool) (hc : K.code[pc]? = some ⟨some (p, true), .bra target uni⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick))
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsSatF (qt (if pick then pc + 1 else target)) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F (if pick then pc + 1 else target) F := by
  intro t ht hQ
  have hreg := hp _ ht.2.2.2.2
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  have hT' := typedF_of_tagsSat hq hT
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
theorem SegQF.jmpS {qt : Nat → EnvF} {pc target : Nat} {uni : Bool} {F : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, .bra target uni⟩)
    (hL : ∀ (t : TState), t.pc = pc → ∀ a ∈ A, a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc) (hq : tagsSatF (qt target) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F target F := by
  intro t ht hQ
  have hr : run K A L g 1 t = some { t with pc := target } := by
    simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, pure, Except.pure, hA.exec,
      execLocalRule_of_none (hL t ht.1), execLocal, Op.rule, execBranch, Op.isLocal]
  refine ⟨{ t with pc := target }, run_rtg hr, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  exact fun r tg h => typedF_of_tagsSat hq hT r tg h

end PTX.Flow.TyG
