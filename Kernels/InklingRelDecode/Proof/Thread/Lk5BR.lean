-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5BD

@[expose] public section

/-!
# The number of `bar24` states before a softmax state, from the decisions

`bar24` is on the rescale path of an iteration `i ≥ 1`, taken when the decision at `shfl12` is
not to keep the maximum. For a predicate `Dc` on the iterations (the decision of the CTA: `Dc j`
when iteration `j` keeps the maximum), `RD Dc d` is the number of rescale iterations before the
state `d`: the iterations `1 ≤ j < d.i` with `¬ Dc j`, and the iteration `d.i` itself once its
`bar24` is passed (`postR`).

* `JS Dc d`: the sites between the stage and the decision are in an iteration `i ≥ 1`, and the
  rescale path's sites in an iteration with `¬ Dc i`;
* `rd_next`: a step keeps `JS` and adds one to `RD` at `bar24`, given that the decision at
  `shfl12` is `Dc` (the step goes to `bar20` exactly when `Dc i`);
* `rd_leave`: at the step that leaves the loop, `RD` is the number of rescale iterations of the
  `num_iters` iterations.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX PTX.Proof PTX.Flow
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- The sites between the stage and the decision. -/
def mid : Sm.Site → Bool
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 => true
  | _ => false

/-- The sites of the rescale path. -/
def resc : Sm.Site → Bool
  | .ldO | .waitLdO | .bar24 | .stO | .waitStO => true
  | _ => false

/-- The sites after the rescale path's `bar24` (and the lazy path's equivalents). -/
def postR : Sm.Site → Bool
  | .stO | .waitStO | .bar20 | .tmemSt | .tmemWait | .bar21 | .arrive => true
  | _ => false

/-- The rescale iterations `1 ≤ j < n`. -/
def nResc (Dc : Nat → Prop) (n : Nat) : Nat := ((Finset.Ico 1 n).filter (fun j => ¬ Dc j)).card

/-- The rescale iterations before a softmax state. -/
def RD (Dc : Nat → Prop) (d : Sm.D) : Nat :=
  nResc Dc d.i + if postR d.site = true ∧ 1 ≤ d.i ∧ ¬ Dc d.i then 1 else 0

/-- The site facts that `RD` needs. -/
def JS (Dc : Nat → Prop) (d : Sm.D) : Prop :=
  (mid d.site = true ∨ resc d.site = true → 1 ≤ d.i) ∧ (resc d.site = true → ¬ Dc d.i)

theorem nResc_succ (Dc : Nat → Prop) (i : Nat) :
    nResc Dc (i + 1) = nResc Dc i + if 1 ≤ i ∧ ¬ Dc i then 1 else 0 := by
  unfold nResc
  by_cases h1 : 1 ≤ i
  · rw [Nat.Ico_succ_right_eq_insert_Ico h1, Finset.filter_insert]
    by_cases hd : Dc i
    · simp [hd]
    · simp only [hd, not_false_eq_true, ↓reduceIte, h1, and_self]
      rw [Finset.card_insert_of_notMem (by simp)]
  · have h0 : i = 0 := by omega
    subst h0
    simp

/-- **A softmax step keeps `JS` and adds one to `RD` at `bar24`.** -/
theorem rd_next {L : Launch} {g : Nat} {Dc : Nat → Prop} {d t : Sm.D} {e : Event}
    (h : Sm.next L g d e = some (some t)) (hJ : JS Dc d)
    (hD : d.site = .shfl12 → (t.site = .bar20 ↔ Dc d.i)) :
    JS Dc t ∧ RD Dc t = RD Dc d + if d.site = .bar24 then 1 else 0 := by
  obtain ⟨hJ1, hJ2⟩ := hJ
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;>
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [toBar20_iff] at h
       obtain ⟨-, rfl⟩ := h
       simp_all [JS, RD, mid, resc, postR, Sm.D.upd, Sm.D.afterSum] <;> omega)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       simp_all [JS, RD, mid, resc, postR, Sm.D.afterSum, nResc_succ] <;> omega)
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       split_ifs <;> simp_all [JS, RD, mid, resc, postR, Sm.D.afterSum, nResc_succ] <;> omega)

/-- **At the step that leaves the loop** (`DComp.leaves`), `RD` counts the rescale iterations of
the `num_iters` iterations and the state is not `bar24`. -/
theorem rd_leave {L : Launch} {g : Nat} {Dc : Nat → Prop} {d : Sm.D} {e : Event}
    (hl : DComp.leaves L g d e) : RD Dc d = nResc Dc d.e.r26 ∧ d.site ≠ .bar24 := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [DComp.leaves] at hl <;>
    first
    | exact absurd hl id
    | (simp only [RD, postR] at hl ⊢
       refine ⟨?_, by simp⟩
       first
       | (rw [hl.2, nResc_succ]; done)
       | (rw [hl.2]; simp; done)
       | (rw [hl.2.2]; simp; done)
       | (rw [hl.2, nResc_succ]; simp; done))

/-- The rescale iterations before a default-partition state (`n` the iterations of the loop). -/
def Rval (Dc : Nat → Prop) (n : Nat) : DComp.St → Nat
  | .sm d => RD Dc d
  | .epi _ => nResc Dc n
  | _ => 0

/-- The site facts of a default-partition state. -/
def JSx (Dc : Nat → Prop) : DComp.St → Prop
  | .sm d => JS Dc d
  | _ => True

/-- **A default-partition step keeps `JSx` and adds one to `Rval` at `bar24`.** -/
theorem rval_next {L : Launch} {g : Nat} {Q : Params} {Dc : Nat → Prop} {n : Nat}
    {s s' : DComp.St} {e : Event} (h : DComp.next L g Q s e = some (some s'))
    (hJ : JSx Dc s) (hn : ∀ d, s = .sm d → n = d.e.r26)
    (hD : ∀ d t, s = .sm d → d.site = .shfl12 → Sm.next L g d e = some (some t) →
      (t.site = .bar20 ↔ Dc d.i)) :
    JSx Dc s' ∧ Rval Dc n s' = Rval Dc n s + if isB24 s = true then 1 else 0 := by
  cases s with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, -, hf⟩ := Ledger.mapInv h
    split at hf <;> (subst hf; simp [JSx, Rval, isB24])
  | pro d =>
    obtain ⟨st, dt⟩ := d
    by_cases hb : st = ProA.Site.bar18
    · subst hb
      simp only [DComp.next, DComp.proNext, ite_true] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [JSx, JS, Rval, RD, nResc, isB24, SmEntry.d0, mid, resc, postR]
      · simp at h
    · simp only [DComp.next, DComp.proNext, hb, ite_false] at h
      obtain ⟨a, -, rfl⟩ := Ledger.mapInv h
      simp [JSx, Rval, isB24]
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · rename_i hlv
      simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := rd_leave (Dc := Dc) hlv
        simp [JSx, Rval, isB24, h1, h2, hn d rfl]
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := Ledger.mapInv h
      obtain ⟨h1, h2⟩ := rd_next ha hJ (fun hs => hD d a rfl hs ha)
      refine ⟨h1, ?_⟩
      simp only [Rval, h2, isB24, decide_eq_true_eq]
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, -, rfl⟩ := Ledger.mapInv h
    simp [JSx, Rval, isB24]

end
end PTX.Kernels.InklingRelDecode.Proof.Lk5B
