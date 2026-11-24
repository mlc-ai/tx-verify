-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteShape

/-! # `ref_cases … helpers [..]`

A transition whose successor at a site is the result of a helper function (`bump`) is closed by
the helper's lemma (`bump_ok`: `NextOk` with a stronger invariant), whose premise comes from the
invariant at the site; the role's tactic closes it. The site without a helper (`.b`) falls back to
the three-way split. -/

namespace PTX.Tests.RefHelpers
open PTX PTX.Flow

inductive Site
  | a
  | b
  deriving DecidableEq

structure D where
  site : Site
  n : Nat

def Ref (d : D) : Prop := d.n ≤ 10

/-- The helper: a successor with a larger count, or a death past the bound. -/
def bump (x : D) : Option (Option D) :=
  if x.n < 10 then some (some ⟨.b, x.n + 1⟩) else none

theorem bump_ok {x : D} (h : x.n < 10) : NextOk (fun d => Ref d ∧ 0 < d.n) (bump x) := by
  simp only [bump, h, ↓reduceIte, NextOk]
  refine ⟨by simp, by simp, fun d' hd => ?_⟩
  cases hd
  exact ⟨by simp only [Ref]; omega, by simp⟩

def next (d : D) (_ : Event) : Option (Option D) :=
  match d.site with
  | .a => bump d
  | .b => some (some d)

def Ev (_ : D) (e : Event) : Prop := e.kind = .exit

example (n : Nat) (s : Site) (hs : s = .a → n < 10) :
    ∀ {e : Event}, True → Ref ⟨s, n⟩ → True → Ev ⟨s, n⟩ e →
      next ⟨s, n⟩ e ≠ some none ∧ (next ⟨s, n⟩ e = none → Ends e) ∧
        ∀ d', next ⟨s, n⟩ e = some (some d') → Ref d' := by
  ref_cases s unfolding [Ev] trans [next] helpers [bump_ok]
    using (first | exact hs rfl | exact hJ)

end PTX.Tests.RefHelpers
