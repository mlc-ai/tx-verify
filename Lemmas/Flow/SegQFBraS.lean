-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFSat

@[expose] public section

/-! # A branch under a predicate fact that holds, under the tag invariant `tagsSatF`

The twin of `SegQF.braNotS` (`Lemmas/Flow/SegQFSat.lean`) for the guard `@p`: it goes to its target
when the predicate holds and falls through when it does not; every fact is kept. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem SegQF.braPS {qt : Nat → EnvF} {pc target p : Nat} {uni : Bool} {F : List (Nat × Value)}
    (pick : Bool) (hc : K.code[pc]? = some ⟨some (p, false), .bra target uni⟩)
    (hp : ∀ R, Holds R F → R p = some (.pred pick))
    (hL : ∀ t a, a ∈ A → a.localRule L g t (.bra target uni) = none)
    (hA : Assumption.SegFreePc A pc)
    (hq : tagsSatF (qt (if pick then target else pc + 1)) (qt pc) = true) :
    SegQ K A L g (QTF qt) pc F (if pick then target else pc + 1) F := by
  intro t ht hQ
  have hreg := hp _ ht.2.2.2.2
  have hT : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  have hT' := typedF_of_tagsSat hq hT
  cases pick with
  | false =>
    have hrun : run K A L g 1 t = some (skip t) := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure]
    refine ⟨skip t, run_rtg hrun, ⟨by simp [skip, ht.1], rfl, rfl, ht.2.2.2.1, ht.2.2.2.2⟩, ?_⟩
    exact fun r tg hr => hT' r tg (by simpa [skip, ht.1] using hr)
  | true =>
    have hrun : run K A L g 1 t = some { t with pc := target } := by
      simp [run, tauStep, out, ht.1, ht.2.2.2.1, hc, guardHolds, readReg, hreg, bind,
        Except.bind, pure, Except.pure, hA.exec, execLocalRule_of_none (hL t), execLocal,
        Op.rule, execBranch, Op.isLocal]
    refine ⟨{ t with pc := target }, run_rtg hrun, ⟨rfl, ht.2.1, ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2⟩, ?_⟩
    exact fun r tg hr => hT' r tg (by simpa using hr)

end PTX.Flow.TyG
