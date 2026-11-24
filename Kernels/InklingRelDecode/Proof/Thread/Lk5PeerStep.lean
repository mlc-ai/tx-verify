-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LkSm

@[expose] public section

/-!
# The numbers two lanes of a row share, along the softmax region's steps

The two lanes of a tile row (the lane and the lane `^ 16`) have the same entry numbers, running
maximum, lazy-rescale decision and new maximum (`pf`). This file states how a step of the region
changes them, for one thread:

* `step_pf`: a step from any site but `shfl5` keeps them, except the edge into the P store
  (`toBar20`), which is the only step that reaches `bar20` and replaces the maximum by `D.mNew`
  (`pfU`);
* `next_ne_setMaxReg`: no step reaches the region's first site;
* `Late`, `late_next`: the sites from the second exchange of the stage to the arrival; a step from
  one of them stays among them unless the iteration counter rises.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Lk

noncomputable section
set_option maxRecDepth 100000

/-- The numbers two lanes of a row share. -/
def pf (d : D) : Ent × Value × Bool × Value := (d.e, d.m, d.stg.kp, d.stg.mn)

/-- The shared numbers after the update of the running maximum. -/
def pfU (d : D) : Ent × Value × Bool × Value := (d.e, d.mNew, d.stg.kp, d.stg.mn)

theorem toBar20_pf {d d' : D} (h : toBar20 d = some (some d')) :
    d'.site = .bar20 ∧ pf d' = pfU d := by
  unfold toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · simp at h

theorem afterSetup_pf {L : Launch} {g : Nat} {d d' : D} (h : afterSetup L g d = some (some d')) :
    d'.site ≠ .bar20 ∧ pf d' = pf d := by
  unfold afterSetup at h
  split at h
  · simp at h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; exact ⟨by simp, rfl⟩)

/-- **A step from any site but `shfl5`**: the edge into the P store, or the shared numbers kept. -/
theorem step_pf {L : Launch} {g : Nat} {d d' : D} {e : Event} (h : next L g d e = some (some d'))
    (h5 : d.site ≠ .shfl5) :
    (d'.site = .bar20 ∧ pf d' = pfU d) ∨ (d'.site ≠ .bar20 ∧ pf d' = pf d) := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (have h' := toBar20_pf h; exact Or.inl ⟨h'.1, h'.2⟩)
    | (have h' := afterSetup_pf h; exact Or.inr ⟨h'.1, h'.2⟩)
    | (simp_all; done)
    | (simp only [Option.some.injEq] at h; subst h; exact Or.inr ⟨by simp [D.afterSum], rfl⟩)

theorem afterSetup_site_ne {L : Launch} {g : Nat} {d d' : D}
    (h : afterSetup L g d = some (some d')) : d'.site ≠ .setMaxReg := by
  unfold afterSetup at h
  split at h
  · simp at h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp)

/-- **No step reaches the region's first site.** -/
theorem next_ne_setMaxReg {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) : d'.site ≠ .setMaxReg := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp_all; done)
    | (have h' := afterSetup_site_ne h; exact h')
    | (have h' := (toBar20_pf h).1; rw [h']; simp)
    | (simp only [Option.some.injEq] at h; subst h; simp; done)
    | (simp only [Option.some.injEq] at h; subst h; simp [D.afterSum])

/-! ### The late sites of an iteration -/

/-- The sites from the second exchange of the stage to the arrival on `p_ready`. -/
def Late : Site → Bool
  | .shfl6 | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL
  | .shfl11 | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 | .tmemSt
  | .tmemWait | .bar21 | .arrive => true
  | _ => false

/-- **A step from a late site stays at a late site of the iteration, or ends the iteration.** -/
theorem late_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hl : Late d.site = true) (hi : d'.i = d.i) :
    Late d'.site = true := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp_all [Late]; done)
    | (have h' := (toBar20_pf h).1; rw [h']; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (exfalso
       unfold afterArrive afterSetup at h
       split at h
       · simp at h
       · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp at hi))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
