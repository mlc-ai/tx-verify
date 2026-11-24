-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteCases

@[expose] public section

/-! # Family forms of a transported successor

A proof tool (Inkling request L-c). A machine regrouped into site families (a `Fin` index per
family) whose successor is transported from a flat machine (`next d e = (flat.next (old d)
e).map …`, with `old (fam k)` the flat site of member `k`) evaluates its successor only per member:
`old (fam k)` at a symbolic `k` does not reduce. A family form, an equation `∀ k, next (fam k) e =
form k e` stated once with the index symbolic, is proved member by member: `fin_family` splits the
index into its literals and closes each member by evaluation (`rfl`, after `site_norm`, or by the
role's lemmas). Reference reasoning then reads `form k e` and never the flat machine. -/

namespace PTX.Flow

/-- `fin_family [lemmas]`: a goal `∀ k : Fin n, …` (or with `k` already introduced) member by
member: the index's literals by `fin_cases`, each member closed by `rfl`, by `site_norm` and
`rfl`, or by `simp only [lemmas]`. -/
syntax "fin_family" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| fin_family) => `(tactic| fin_family [])
  | `(tactic| fin_family [$ls,*]) => `(tactic| (
      try intro k
      fin_cases k <;> first
        | rfl
        | (site_norm; rfl)
        | (simp only [$ls,*]; done)
        | (site_norm; simp only [$ls,*]; done)
        | fail "fin_family: a member does not evaluate"))

end PTX.Flow
