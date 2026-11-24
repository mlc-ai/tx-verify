-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Sm

@[expose] public section

/-!
# The softmax region's shuffles, counted by site and iteration

Each iteration of the loop has the shuffles `shfl4`, `shfl5`, `shfl6`, and from the second
iteration on `shfl7` to `shfl12` (the first iteration goes from `shfl6` to the P store); the O
rescale has none. So the number of shuffles of the region before a state is `smW d`: `smBase d.i`
for the iterations before, plus `smOff` of the site in its iteration.

* `smW_next`: a step adds one exactly at a shuffle site (`smShfl`), given that the sites between
  the sum's exchange and the O rescale are reached only from the second iteration on (`smMid`,
  kept by the step).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The shuffle sites of the region. -/
def smShfl : Site → Bool
  | .shfl4 | .shfl5 | .shfl6 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .shfl11 | .shfl12 => true
  | _ => false

/-- The sites from the sum's exchange to the end of the O rescale: second iteration on. -/
def smMid : Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- The shuffles of an iteration before its site. -/
def smOff (s : Site) (i : Nat) : Nat :=
  match s with
  | .ldS | .waitLd | .shfl5 => 1
  | .shfl6 => 2
  | .waitO | .bar22 | .shfl7 => 3
  | .shfl8 => 4
  | .shfl9 => 5
  | .shfl10 => 6
  | .store10 | .bar23 | .ldL | .shfl11 => 7
  | .shfl12 => 8
  | .ldO | .waitLdO | .bar24 | .stO | .waitStO => 9
  | .bar20 | .tmemSt | .tmemWait | .bar21 | .arrive => if i = 0 then 3 else 9
  | _ => 0

/-- The shuffles of the iterations before `i`: 3 in the first, 9 in each later one. -/
def smBase (i : Nat) : Nat := if i = 0 then 0 else 9 * i - 6

/-- **The region's shuffles before a state.** -/
def smW (d : D) : Nat := smBase d.i + smOff d.site d.i

theorem toBar20_inv {d d' : D} (h : toBar20 d = some (some d')) :
    d'.site = .bar20 ∧ d'.i = d.i := by
  unfold toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · cases h

theorem afterSetup_inv {L : Launch} {g : Nat} {d d' : D} (h : afterSetup L g d = some (some d')) :
    (d'.site = .nxt 0 ∨ d'.site = .waitS) ∧ d'.i = d.i := by
  unfold afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; simp)

theorem afterArrive_inv {L : Launch} {g : Nat} {d d' : D}
    (h : afterArrive L g d = some (some d')) :
    (d'.site = .nxt 0 ∨ d'.site = .waitS) ∧ d'.i = d.i + 1 := by
  unfold afterArrive at h
  exact afterSetup_inv h

theorem smBase_succ (i : Nat) : smBase (i + 1) = smBase i + (if i = 0 then 3 else 9) := by
  unfold smBase
  split <;> split <;> omega

/-- **A step of the region adds one shuffle exactly at a shuffle site.** -/
theorem smW_next {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) (hm : smMid d.site = true → 1 ≤ d.i) :
    smW d' = smW d + (if smShfl d.site then 1 else 0) ∧ (smMid d'.site = true → 1 ≤ d'.i) := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       (simp_all [smW, smOff, smShfl, smMid, D.afterSum, D.afterMax, D.afterMaxT]) <;>
         first | omega | exact smBase_succ _ | (split <;> omega))
    | (obtain ⟨h1, h2⟩ := afterSetup_inv h
       obtain ⟨s', en', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
       simp only at h1 h2
       subst h2
       rcases h1 with h1 | h1 <;> subst h1 <;>
         (simp_all [smW, smOff, smShfl, smMid]) <;>
           first | omega | exact smBase_succ _ | (split <;> omega))
    | (obtain ⟨h1, h2⟩ := afterArrive_inv h
       obtain ⟨s', en', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
       simp only at h1 h2
       subst h2
       rcases h1 with h1 | h1 <;> subst h1 <;>
         (simp_all [smW, smOff, smShfl, smMid, smBase_succ]) <;>
           first | omega | exact smBase_succ _ | (split <;> omega))
    | (obtain ⟨h1, h2⟩ := toBar20_inv h
       obtain ⟨s', en', i', m', l', cw', cv', w', v', sv', pf', stg'⟩ := d'
       simp only [D.afterSum] at h1 h2
       subst h1 h2
       (simp_all [smW, smOff, smShfl, smMid]) <;>
         first | omega | exact smBase_succ _ | (split <;> omega))

theorem smBase_le {i j : Nat} (h : i ≤ j) : smBase i ≤ smBase j := by
  unfold smBase
  split <;> split <;> omega

theorem smShfl_cases {s : Site} (h : smShfl s = true) :
    s = .shfl4 ∨ s = .shfl5 ∨ s = .shfl6 ∨ s = .shfl7 ∨ s = .shfl8 ∨ s = .shfl9 ∨
      s = .shfl10 ∨ s = .shfl11 ∨ s = .shfl12 := by
  cases s <;> simp_all [smShfl]

/-- The count of a shuffle site stays below the next iteration's base. -/
theorem shfl_lt_next {s : Site} {i : Nat} (hs : smShfl s = true)
    (hm : smMid s = true → 1 ≤ i) : smBase i + smOff s i < smBase (i + 1) := by
  rw [smBase_succ]
  rcases smShfl_cases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [smMid, smOff, true_implies] at hm ⊢ <;> split <;> omega

/-- **A count names one shuffle site and iteration.** -/
theorem shfl_inj {s s' : Site} {i i' : Nat} (hs : smShfl s = true) (hs' : smShfl s' = true)
    (hm : smMid s = true → 1 ≤ i) (hm' : smMid s' = true → 1 ≤ i')
    (h : smBase i + smOff s i = smBase i' + smOff s' i') : s = s' ∧ i = i' := by
  have h1 := shfl_lt_next hs hm
  have h2 := shfl_lt_next hs' hm'
  have hi : i = i' := by
    rcases Nat.lt_trichotomy i i' with hl | hl | hl
    · have := smBase_le (show i + 1 ≤ i' by omega)
      omega
    · exact hl
    · have := smBase_le (show i' + 1 ≤ i by omega)
      omega
  subst hi
  refine ⟨?_, rfl⟩
  have ho : smOff s i = smOff s' i := by omega
  rcases smShfl_cases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases smShfl_cases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [smOff]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
