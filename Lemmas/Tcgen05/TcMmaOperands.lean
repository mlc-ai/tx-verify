-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Tcgen05.TcMmaValue
public import Mathlib.Tactic.ByContra
public import Core.Tc.TcMmaOperands

@[expose] public section

section
namespace PTX.TcMma
noncomputable section

/-- An initialized accumulator must exist even if nobody subsequently loads D. -/
theorem CompletedValues.has_initializer {L : Launch} {A : List Assumption} {X : Execution}
    {i : EvId} {cell : Cell} (h : CompletedValues L A X i)
    (hd : X.async.mmaDone i = true) (hc : X.MmaCell i cell) :
    ∃ first, Initializer L X first cell := by
  obtain ⟨v, hv⟩ := h hd cell hc
  exact hv.has_initializer

end
end PTX.TcMma
end

section
namespace PTX.TcMma

theorem makeOperands_matches {L : Launch} {issuer : Nat} {d : Descriptor}
    {a b : TcShared.Descriptor} {s : OperandSpec}
    (h : makeOperands L issuer d a b = some s) : s.MatchesLaunch L issuer := by
  unfold makeOperands at h
  obtain ⟨ctas, hctas, rest⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨lowCta, hlow, rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨highCta, hhigh, hs⟩ := Option.bind_eq_some_iff.mp rest
  have hs' : s = ⟨d, a, b, lowCta, highCta, none, {}⟩ := by simpa using hs.symm
  subst hs'
  exact ⟨ctas, hctas, hlow, hhigh⟩

end PTX.TcMma
end
