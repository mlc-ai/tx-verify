-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Successors that are an `if`

A proof tool, generic over `Flow.Code` (promoted from Inkling's proof). A
machine whose transition picks the successor site by a condition the thread's facts decide (a
predicate of the code, the election's outcome) writes it as `if c then d₁ else d₂`.
`site_cases` evaluates such a successor to the `if`, and its `lands_auto` then needs three things
the library version does not do:

* the sub-step and the accumulator of the successor are `0` and `[]` in both branches
  (`split <;> rfl`), not by `rfl` alone;
* the segment to an `if` is split on the condition first, as often as the `if`s nest
  (`ite_cases`), so that each piece ends at a literal site and its condition is a hypothesis for
  the segment tactic;
* an alternative that fails reports its failure: the last alternative is `fail`, so that no
  alternative runs with error recovery (which would admit a goal without an error).

The rule below extends `lands_auto` (a macro, so the library rule stays the fallback). -/

namespace PTX.Flow
open Lean Meta Elab Tactic

/-- `ite_cases`: split the goal on the condition of its first `if`; each branch has the condition
or its negation as a hypothesis and the `if` reduced. -/
elab "ite_cases" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let some it := ty.find? (·.isAppOfArity ``ite 5) | throwError "ite_cases: no if"
  let tc ← Term.exprToSyntax (it.getArg! 1)
  let hb := mkIdent (← mkFreshUserName `hb)
  Term.withoutErrToSorry <| evalTactic (← `(tactic| by_cases $hb:ident : $tc))
  let gs ← getGoals
  let mut out := []
  for g' in gs do
    setGoals [g']
    Term.withoutErrToSorry <| evalTactic (← `(tactic|
      simp only [$hb:ident, ite_true, ite_false, ↓reduceIte, Bool.false_eq_true,
        Bool.true_eq_false, Bool.not_eq_true]))
    out := out ++ (← getGoals)
  setGoals out

macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub =>
        first | try_rt rfl | ((repeat' split) <;> try_rt rfl) | fail "lands_auto: sub-step"
      case acc =>
        first | try_rt rfl | ((repeat' split) <;> try_rt rfl) | fail "lands_auto: accumulator"
      case seg =>
        intro _
        site_norm
        try dsimp only [PTX.Flow.Code.electFacts]
        try drop_norm
        seg_pre
        -- the walk first: it decides the segment's length or its cuts (and splits an `if` at
        -- the end) before any evaluation, so no evaluation is started that a symbolic branch
        -- would stop
        first
          | try_rt (seg_sym using $seg)
          | try_rt (seg_auto using $seg)
          | ((repeat' ite_cases) <;> try_rt (seg_auto using $seg))
          | fail "lands_auto: segment"
      case inv =>
        site_norm
        ($inv)))

end PTX.Flow
