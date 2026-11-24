-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CausalThreadCount

@[expose] public section

/-! # The thread of a selector that polls an object

A proof tool. When any two threads of a selector that poll an object successfully are one,
`pollerOf` names that thread (or a given thread of the selector when none polls), so the
selector's records on the object are one thread's. -/

namespace PTX

noncomputable section

open Classical in
/-- The thread of selector `sel` that polls `m` successfully, if any; otherwise `dflt`. -/
def pollerOf (X : Execution) (sel : Nat → Bool) (m : Loc) (dflt : Nat) : Nat :=
  if h : ∃ g, sel g = true ∧ ∃ j pc p acq sc,
      X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ then Classical.choose h
  else dflt

theorem pollerOf_sel {X : Execution} {sel : Nat → Bool} {m : Loc} {dflt : Nat}
    (hd : sel dflt = true) : sel (pollerOf X sel m dflt) = true := by
  unfold pollerOf
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · exact hd

/-- A thread of the selector that polls `m` successfully is `pollerOf`, when any two such
threads are one. -/
theorem pollerOf_eq {X : Execution} {sel : Nat → Bool} {m : Loc} {dflt : Nat}
    (huniq : ∀ {g h j k pc pc' p p' acq acq' sc sc'}, sel g = true → sel h = true →
      X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩ →
      X.get (h, k) = some ⟨pc', .wait m p' true acq' sc'⟩ → g = h)
    {g j pc p : Nat} {acq : Bool} {sc : MbarScope} (hg : sel g = true)
    (he : X.get (g, j) = some ⟨pc, .wait m p true acq sc⟩) : g = pollerOf X sel m dflt := by
  unfold pollerOf
  split
  · rename_i h
    obtain ⟨hs, j', pc', p', acq', sc', he'⟩ := Classical.choose_spec h
    exact huniq hg hs he he'
  · rename_i h
    exact absurd ⟨g, hg, j, pc, p, acq, sc, he⟩ h

end
end PTX
