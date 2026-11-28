-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
public import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum

@[expose] public section

/-! # The running maxima of the value state are numbers or `-inf`

The running maximum, the round's new maximum and the maximum before the last update are numbers or
`-inf` (`NiVals`) at the first state, and the step of the machine keeps them when the words of the
shuffle of pc 1838 are. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control PTX.Assumption

noncomputable section

/-- **The maxima of a value state are numbers or `-inf`.** -/
structure NiVals (v : Vals) : Prop where
  m : (Kd.s .ni).Has v.m
  mx : (Kd.s .ni).Has v.mx
  mp : (Kd.s .ni).Has v.mp

theorem ni_init : NiVals ({} : Vals) :=
  ⟨init_has, SK.mono (a := .fl) (b := .ni) (by decide) zero_has, init_has⟩

/-- **The step keeps the maxima numbers**, given the words of the shuffle of pc 1838. -/
theorem ni_step {L : Launch} {d : D} {ev : Event} {s : Site} (hv : NiVals d.v)
    (h5 : d.c.site = .shfl5 → ∀ m a b c r ok, ev.kind = .shfl m a b c r ok →
      (Kd.s .ni).Has a ∧ (Kd.s .ni).Has r) : NiVals (record L d ev s) := by
  obtain ⟨hm, hmx, hmp⟩ := hv
  unfold record
  split
  · rename_i _ _ _ _ _ _ _ _ hs hk
    have h := h5 hs _ _ _ _ _ _ hk
    exact ⟨hm, mxWord_has hm h.1 h.2, hmp⟩
  all_goals (try dsimp only)
  all_goals (try split)
  all_goals first
    | exact ⟨hm, hmx, hmp⟩
    | exact ⟨init_has, hmx, hmp⟩
    | exact ⟨mNext_has hm hmx, hmx, hm⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
