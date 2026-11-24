-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.NoStop
public import Kernels.RmsNorm.Proof.Arrivals

@[expose] public section

/-! # The progress of a thread

A state's progress `D.vt` orders the states of all threads alike: the rows, and in a row the
sites in their order (`D.ord`). The arrivals on each barrier and the shuffles before a state are
monotone functions of its progress (`bc0_eq`, `bc1_eq`, `sc_eq`, the shuffles for the warp's
`w0`), and a shuffle site is the last state with its number of shuffles (`sc_succ`). So a thread
that has fewer arrivals or shuffles than another, or as many shuffles but is not at the other's
shuffle site, has made less progress (`vt_lt_of_bc0`, `vt_lt_of_bc1`, `vt_lt_of_sc`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The progress of a state. -/
def D.vt (d : D) : Nat :=
  match d.site with
  | .shfl0 => 0
  | .exit => 100 * d.i + 99
  | _ => 100 * d.i + d.ord + 1

/-- The arrivals on barrier `0` before progress `v`. -/
def bc0Of (v : Nat) : Nat :=
  if v = 0 then 0 else
    2 * ((v - 1) / 100) + (if 31 ≤ (v - 1) % 100 then 1 else 0) +
      (if 39 ≤ (v - 1) % 100 then 1 else 0)

/-- The arrivals on barrier `1` before progress `v`. -/
def bc1Of (v : Nat) : Nat := if v = 0 then 0 else (v - 1) / 100

/-- The shuffles before progress `v` in a warp with `w0 = w`. -/
def scOf (w v : Nat) : Nat :=
  if v = 0 then 0 else
    1 + 5 * (1 + w) * ((v - 1) / 100) + min ((v - 1) % 100 - 24) 5 +
      w * min ((v - 1) % 100 - 32) 5

theorem bc0Of_mono {v v' : Nat} (h : v ≤ v') : bc0Of v ≤ bc0Of v' := by
  unfold bc0Of; split_ifs <;> omega

theorem bc1Of_mono {v v' : Nat} (h : v ≤ v') : bc1Of v ≤ bc1Of v' := by
  unfold bc1Of; split_ifs <;> omega

theorem scOf_mono {w v v' : Nat} (hw : w ≤ 1) (h : v ≤ v') : scOf w v ≤ scOf w v' := by
  unfold scOf
  split_ifs with h1 h2 h2
  · omega
  · omega
  · omega
  · have hq : (v - 1) / 100 ≤ (v' - 1) / 100 := Nat.div_le_div_right (by omega)
    rcases Nat.lt_or_eq_of_le hq with hlt | heq
    · have : 5 * (1 + w) * ((v - 1) / 100) + 5 * (1 + w) ≤ 5 * (1 + w) * ((v' - 1) / 100) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl <;> omega
    · rw [heq]
      have : (v - 1) % 100 ≤ (v' - 1) % 100 := by omega
      rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl <;> omega

variable {P : Params} {g : Nat} {d : D}

/-- The arithmetic of a state's counts: unfold them and its progress, by its site. -/
macro "vt_close" hi:ident hs:ident hx:ident : tactic => `(tactic| (
  have h1 := ($hi).sub.1
  have hb := ($hi).bfa
  have hb' := ($hi).bfb
  rcases $hs:ident : d.site <;>
    simp only [$hs:ident, D.bc0, D.bc1, D.sc, D.vt, D.ord, bc0Of, bc1Of, scOf, Site.vec,
      reduceCtorEq, false_implies, forall_const, true_implies, ne_eq, not_true_eq_false,
      Site.bfa.injEq, Site.bfb.injEq, forall_eq', Nat.add_one_ne_zero, ↓reduceIte]
      at h1 hb hb' $hx:ident ⊢ <;>
    (try simp only [w0] at hb' ⊢) <;> (try split_ifs at hb' ⊢) <;> omega))

theorem bc0_eq (hi : Inv P g d) (hx : d.site ≠ .exit) : d.bc0 = bc0Of d.vt := by
  vt_close hi hs hx

theorem bc1_eq (hi : Inv P g d) (hx : d.site ≠ .exit) : d.bc1 = bc1Of d.vt := by
  vt_close hi hs hx

theorem sc_eq (hi : Inv P g d) (hx : d.site ≠ .exit) : d.sc g = scOf (w0 g) d.vt := by
  vt_close hi hs hx

theorem w0_le' (g : Nat) : w0 g ≤ 1 := by unfold w0; split <;> omega

/-- **A shuffle site is the last state with its number of shuffles.** -/
theorem sc_succ (hi : Inv P g d) (hs : d.site.isShfl = true) :
    scOf (w0 g) (d.vt + 1) = scOf (w0 g) d.vt + 1 := by
  have hb := hi.bfa
  have hb' := hi.bfb
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.false_eq_true] at hs <;>
    simp only [hsd, D.vt, D.ord, scOf, Site.bfa.injEq, Site.bfb.injEq, forall_eq',
      Nat.add_one_ne_zero, ↓reduceIte] at hb hb' ⊢
  · simp
  · rcases (by have := w0_le' g; omega : w0 g = 0 ∨ w0 g = 1) with h0 | h0 <;> rw [h0] <;> omega
  · have : w0 g = 1 := by simp [w0, hb'.2]
    rw [this]; omega

variable {h : Nat} {dh : D}

/-- Two states of equal progress at a shuffle site are at that site of the same row. -/
theorem vt_same (hig : Inv P g d) (hih : Inv P h dh) (hxh : dh.site ≠ .exit)
    (hs : d.site.isShfl = true) (he : dh.vt = d.vt) :
    dh.site = d.site ∧ (d.site ≠ .shfl0 → dh.i = d.i) := by
  have h1 := hih.sub.1
  have hb := hih.bfa
  have hb' := hih.bfb
  have gb := hig.bfa
  have gb' := hig.bfb
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.false_eq_true] at hs <;>
    rcases hsh : dh.site <;>
    simp only [hsd, hsh, D.vt, D.ord, Site.vec, reduceCtorEq, false_implies, forall_const,
      ne_eq, not_true_eq_false, not_false_eq_true, Site.bfa.injEq, Site.bfb.injEq,
      forall_eq', and_true, false_and] at h1 hb hb' gb gb' he hxh ⊢ <;> omega

theorem vt_lt_of_bc0 (hig : Inv P g d) (hih : Inv P h dh) (hxg : d.site ≠ .exit)
    (hxh : dh.site ≠ .exit) (hlt : dh.bc0 < d.bc0) : dh.vt < d.vt := by
  rw [bc0_eq hig hxg, bc0_eq hih hxh] at hlt
  by_contra hle
  exact absurd (bc0Of_mono (Nat.le_of_not_lt hle)) (by omega)

theorem vt_lt_of_bc1 (hig : Inv P g d) (hih : Inv P h dh) (hxg : d.site ≠ .exit)
    (hxh : dh.site ≠ .exit) (hlt : dh.bc1 < d.bc1) : dh.vt < d.vt := by
  rw [bc1_eq hig hxg, bc1_eq hih hxh] at hlt
  by_contra hle
  exact absurd (bc1Of_mono (Nat.le_of_not_lt hle)) (by omega)

/-- **A lane with at most the shuffles of a lane at a shuffle site, not at that site of its row,
has made less progress.** -/
theorem vt_lt_of_sc (hig : Inv P g d) (hih : Inv P h dh) (hxh : dh.site ≠ .exit)
    (hs : d.site.isShfl = true) (hw : w0 h = w0 g) (hle : dh.sc h ≤ d.sc g)
    (hne : ¬ (dh.site = d.site ∧ (d.site ≠ .shfl0 → dh.i = d.i))) : dh.vt < d.vt := by
  have hxg : d.site ≠ .exit := by intro h0; rw [h0] at hs; cases hs
  rw [sc_eq hig hxg, sc_eq hih hxh, hw] at hle
  by_contra hge
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hge) with hlt | heq
  · have := scOf_mono (w0_le' g) (show d.vt + 1 ≤ dh.vt by omega)
    rw [sc_succ hig hs] at this
    omega
  · exact hne (vt_same hig hih hxh hs heq.symm)

end
end PTX.Kernels.RmsNorm.Proof
