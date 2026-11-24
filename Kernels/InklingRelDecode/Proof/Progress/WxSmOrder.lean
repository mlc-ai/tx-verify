-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtTime
public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign

@[expose] public section

/-!
# The softmax region's barrier-0 count orders its states in time

The number of barrier-0 events before a softmax state, when the decisions of a CTA agree, is
`2 + C0 + phi site i + RD Dc d` (`Interface.Kk.cnt_val`). This file compares that count with the
virtual time `Wt.smT`: two softmax states of one CTA (one decision table `Dc`, both with the site
facts `JS`), the second at a `bar.sync 0, 128` site, satisfy

* `sm_lt`: if the first state's count plus its own barrier-0 event is at most the second's count,
  the first state is strictly earlier;
* `sm_le`: if the first state's count is at most the second's, the first state is no later.

The argument: a state of a later iteration has made at least two more barrier-0 events than any
barrier site of an earlier iteration (`phi_lo`, `phi_bar_hi`, `nResc_mono`); a state of an earlier
iteration is at an earlier slot; in one iteration the count rises at each barrier site in the
order of the sites' times (a case split on the two sites and the iteration's decision).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- The setup sites of the softmax region, before its loop. -/
def setup : Sm.Site → Bool
  | .setMaxReg | .bar0 | .pre _ => true
  | _ => false

/-- The time of a loop site: its slot's softmax band and its position. -/
theorem smT_loop {d : Sm.D} (h : setup d.site = false) :
    smT d = slot d.i + bandS + (90 - Bound.Sm.pos d.site) := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp_all [setup, smT]

/-- A setup site is before slot `0`'s softmax band. -/
theorem smT_setup {d : Sm.D} (h : setup d.site = true) : smT d < slot 0 + bandS := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp_all [setup, smT]
  all_goals (try (rename_i j; have := j.isLt))
  all_goals wt_omega

/-- Every state is timed below the end of its iteration's band. -/
theorem smT_hi (d : Sm.D) : smT d ≤ slot d.i + bandS + 90 := by
  by_cases h : setup d.site = true
  · have := smT_setup h
    wt_omega
  · rw [smT_loop (by simpa using h)]
    omega

/-- A loop site's count is at least `4 i - 2` (the site facts make the middle sites of the first
iteration impossible). -/
theorem phi_lo {Dc : Nat → Prop} {d : Sm.D} (hJ : JS Dc d) (h : setup d.site = false)
    (hi : 1 ≤ d.i) : 4 * (d.i : Int) - 2 ≤ phi d.site d.i := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp_all [setup, phi] <;> omega

/-- A barrier site's count is at most `4 i + 1`. -/
theorem phi_bar_hi {s : Sm.Site} (h : smB0 s = 2) (i : Nat) : phi s i ≤ 4 * (i : Int) + 1 := by
  cases s <;> simp_all [smB0, phi] <;> omega

/-- The barrier sites are loop sites. -/
theorem bar_loop {s : Sm.Site} (h : smB0 s = 2) : setup s = false := by
  cases s <;> simp_all [smB0, setup]

/-- The rescale count of a state is at least the rescale iterations before its iteration. -/
theorem rd_ge (Dc : Nat → Prop) (d : Sm.D) : nResc Dc d.i ≤ RD Dc d := by
  unfold RD
  omega

/-- The increment of a softmax state: its own barrier-0 event. -/
def smInc (s : Sm.Site) : Int := if smB0 s = 2 then 1 else 0

variable {Dc : Nat → Prop} {d1 d : Sm.D} (hJ1 : JS Dc d1) (hJ : JS Dc d) (hb : smB0 d.site = 2)
include hJ1 hJ hb

/-- **In one iteration, a count at most a barrier site's (plus the state's own event) is an earlier
site.** -/
theorem same_iter_lt (hi : d1.i = d.i) (h1 : setup d1.site = false)
    (h : phi d1.site d1.i + (RD Dc d1 : Int) + smInc d1.site ≤ phi d.site d.i + RD Dc d) :
    Bound.Sm.pos d.site < Bound.Sm.pos d1.site := by
  obtain ⟨hJa, hJb⟩ := hJ1
  obtain ⟨hJc, hJd⟩ := hJ
  obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only at hi h hJa hJb hJc hJd h1 hb ⊢
  subst hi
  by_cases hD : Dc i1 <;>
  cases s <;> simp only [smB0] at hb <;> (try exact absurd hb (by decide)) <;>
    cases s1 <;> simp only [setup] at h1 <;> (try exact absurd h1 (by decide)) <;>
    simp_all [phi, RD, postR, smInc, smB0, mid, resc, Bound.Sm.pos] <;>
    (try rename_i j; have := j.isLt) <;> (try split_ifs at h) <;> omega

/-- **The softmax states in count order are in time order (strict).** -/
theorem sm_lt (h : phi d1.site d1.i + (RD Dc d1 : Int) + smInc d1.site ≤ phi d.site d.i + RD Dc d) :
    smT d1 < smT d := by
  have hd := smT_loop (bar_loop hb)
  by_cases hs : setup d1.site = true
  · have := smT_setup hs
    rw [hd]
    wt_omega
  have hs' : setup d1.site = false := by simpa using hs
  rcases lt_trichotomy d1.i d.i with hlt | heq | hgt
  · have := smT_hi d1
    rw [hd]
    have : slot d1.i + span ≤ slot d.i := by unfold slot; nlinarith
    wt_omega
  · have := same_iter_lt hJ1 hJ hb heq hs' h
    rw [hd, smT_loop hs', heq]
    have := Bound.Sm.pos_le d.site
    have : Bound.Sm.pos d1.site ≤ 90 := by
      obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
      cases s1 <;> simp_all [setup, Bound.Sm.pos]
    omega
  · exfalso
    have h1 := phi_lo hJ1 hs' (by omega)
    have h2 := phi_bar_hi hb d.i
    have h3 := rd_ge Dc d1
    have h4 := rd_le Dc d
    have h5 := nResc_mono Dc (show d.i + 1 ≤ d1.i by omega)
    have h6 : (RD Dc d : Int) ≤ (RD Dc d1 : Int) := by exact_mod_cast (h4.trans h5).trans h3
    have h7 : (0 : Int) ≤ smInc d1.site := by unfold smInc; split_ifs <;> omega
    have h8 : (d.i : Int) + 1 ≤ d1.i := by exact_mod_cast hgt
    omega

/-- **In one iteration, a count at most a barrier site's is a site no later.** -/
theorem same_iter_le (hi : d1.i = d.i) (h1 : setup d1.site = false)
    (h : phi d1.site d1.i + (RD Dc d1 : Int) ≤ phi d.site d.i + RD Dc d) :
    Bound.Sm.pos d.site ≤ Bound.Sm.pos d1.site := by
  obtain ⟨hJa, hJb⟩ := hJ1
  obtain ⟨hJc, hJd⟩ := hJ
  obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only at hi h hJa hJb hJc hJd h1 hb ⊢
  subst hi
  by_cases hD : Dc i1 <;>
  cases s <;> simp only [smB0] at hb <;> (try exact absurd hb (by decide)) <;>
    cases s1 <;> simp only [setup] at h1 <;> (try exact absurd h1 (by decide)) <;>
    simp_all [phi, RD, postR, mid, resc, Bound.Sm.pos] <;>
    (try rename_i j; have := j.isLt) <;> (try split_ifs at h) <;> omega

/-- **The softmax states in count order are in time order.** -/
theorem sm_le (h : phi d1.site d1.i + (RD Dc d1 : Int) ≤ phi d.site d.i + RD Dc d) :
    smT d1 ≤ smT d := by
  by_cases hs : setup d1.site = true
  · exact (sm_lt hJ1 hJ hb (by
      have : smInc d1.site = 0 := by
        obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
        cases s1 <;> simp_all [setup, smInc, smB0]
      omega)).le
  have hs' : setup d1.site = false := by simpa using hs
  rcases lt_or_ge d1.i d.i with hlt | hge
  · have := smT_hi d1
    rw [smT_loop (bar_loop hb)]
    have : slot d1.i + span ≤ slot d.i := by unfold slot; nlinarith
    wt_omega
  rcases eq_or_lt_of_le hge with heq | hgt
  · have := same_iter_le hJ1 hJ hb heq.symm hs' h
    rw [smT_loop (bar_loop hb), smT_loop hs', ← heq]
    have : Bound.Sm.pos d1.site ≤ 90 := by
      obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
      cases s1 <;> simp_all [setup, Bound.Sm.pos]
    omega
  · exfalso
    have h1 := phi_lo hJ1 hs' (by omega)
    have h2 := phi_bar_hi hb d.i
    have h3 := rd_ge Dc d1
    have h4 := rd_le Dc d
    have h5 := nResc_mono Dc (show d.i + 1 ≤ d1.i by omega)
    have h6 : (RD Dc d : Int) ≤ (RD Dc d1 : Int) := by exact_mod_cast (h4.trans h5).trans h3
    have h8 : (d.i : Int) + 1 ≤ d1.i := by exact_mod_cast hgt
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
