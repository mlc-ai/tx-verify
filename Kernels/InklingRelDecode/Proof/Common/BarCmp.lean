-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Common.DataOrdinal

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

/-- **A Softmax state with no more fixed rendezvous than a half-CTA rendezvous is no later than
it**, strictly unless it is the same site of the same round, but for a state past the optional
rendezvous of its round, when the rendezvous is the optional one. -/
public theorem soft_bar_cmp {sh sE : Site} {ih iE lim : Nat} {vh vE : Carry}
    (hE : sE = .bar20 ∨ sE = .bar21 ∨ sE = .bar22 ∨ sE = .bar23 ∨ sE = .bar24)
    (fc : fixedCount ⟨sh, ih, vh⟩ ≤ fixedCount ⟨sE, iE, vE⟩)
    (epiH : sh = .epilogue → ih = lim) (loopE : iE < lim) :
    (time ⟨sh, ih, vh⟩ ≤ time ⟨sE, iE, vE⟩ ∧
      (time ⟨sh, ih, vh⟩ = time ⟨sE, iE, vE⟩ → sh = sE ∧ ih = iE)) ∨
    (sE = .bar24 ∧ ih = iE ∧ (sh = .stO ∨ sh = .waitStO ∨ sh = .bar20) ∧
      fixedCount ⟨sh, ih, vh⟩ = fixedCount ⟨sE, iE, vE⟩) := by
  unfold fixedCount at fc ⊢
  simp only at fc ⊢
  cases sh
  all_goals rcases hE with rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {decide := true}) [syncPosition, time, Site.position,
    Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride, Lib.Slots.enter, Lib.Slots.reuse,
    Lib.Slots.finish] at fc epiH ⊢
  all_goals omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax
