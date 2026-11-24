-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode

@[expose] public section

namespace PTX.Decode
open Syntax

/-- Resolve two adjacent slices with the same scope bindings and their original indices. -/
theorem resolveScopePart_append {resolveNested} {env : List Binding} {path : String}
    {start : Nat} {xs ys a b : List Statement}
    (hx : resolveScopePart resolveNested xs env path start = .ok a)
    (hy : resolveScopePart resolveNested ys env path (start + xs.length) = .ok b) :
    resolveScopePart resolveNested (xs ++ ys) env path start = .ok (a ++ b) := by
  simp only [resolveScopePart, List.zipIdx_append, List.mapM_append] at hx hy ⊢
  revert hx hy
  generalize (xs.zipIdx start).mapM (resolveScopeStmt resolveNested env path) = x
  generalize (ys.zipIdx (start + xs.length)).mapM (resolveScopeStmt resolveNested env path) = y
  cases x <;> cases y <;> simp_all [bind, Except.bind, pure, Except.pure,
    List.flatten_append]


private theorem scopeDepth_pos (body : List Statement) : 1 ≤ scopeDepth body := by
  induction body with
  | nil => decide
  | cons s ss ih => exact Nat.le_trans ih (Nat.le_max_right (statementDepth s) (scopeDepth ss))

/-- The depth bound of a concatenation is the maximum of the two bounds. -/
theorem scopeDepth_append (xs ys : List Statement) :
    scopeDepth (xs ++ ys) = max (scopeDepth xs) (scopeDepth ys) := by
  induction xs with
  | nil => simp [scopeDepth, Nat.max_eq_right (scopeDepth_pos ys)]
  | cons s ss ih => simp only [List.cons_append, scopeDepth, ih, Nat.max_assoc]

/-- Rebuild scope resolution from its checked depth, bindings and statement slices. -/
theorem resolveScopes_of_part {depth fuel : Nat} {body resolved : List Statement}
    {env : List Binding} (hd : depth = fuel + 1)
    (he : scopeBindings body [] "" = .ok env)
    (hp : resolveScopePart (resolveScopes fuel) body env "" 0 = .ok resolved) :
    resolveScopes depth body [] "" = .ok resolved := by
  simp only [hd, resolveScopes.eq_2, he, bind, Except.bind]
  exact hp

/-- Separate a successful scope-resolution certificate from the rest of preparation. -/
theorem prepare_of_resolved {globals : List (List String)} {f : Function}
    {body : List Statement} (he : f.header.take 2 = [".visible", ".entry"])
    (hn : needsScopeResolution f.body = true)
    (hs : resolveScopes (scopeDepth f.body) f.body [] "" = .ok body) :
    prepare globals f = prepareResolved globals f body := by
  simp [prepare, he, hn, hs, bind, Except.bind]

end PTX.Decode
