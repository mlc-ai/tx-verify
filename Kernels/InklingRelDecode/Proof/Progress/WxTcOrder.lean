-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WxTcCount
public import Kernels.InklingRelDecode.Proof.Progress.WxSmOrder
public import Kernels.InklingRelDecode.Proof.Progress.WtMonoRoles

@[expose] public section

/-!
# The warp-collective `tcgen05` count orders the states of a region in time

For two states of one region, the second at a warp-collective `tcgen05` site, a count (`tcF` plus
`4 RD`, `WxTcCount.lean`) at most the second's is an earlier or equal state, and strictly earlier
when the first state's own event of the class is added (`c = tcB`):

* `sm_tc_cmp`: the softmax region, with the site facts `JS` and one decision table;
* `epi_tc_cmp`: the epilogue, with one `num_iters < 1` flag (`sk`);
* `ds_tc_cmp`: the common start (warp 0).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Lk5B PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- The softmax sites of the class. -/
def smTc (s : Sm.Site) : Bool :=
  decide (s = .ldS ∨ s = .waitLd ∨ s = .tmemSt ∨ s = .tmemWait ∨ s = .ldO ∨ s = .waitLdO ∨
    s = .stO ∨ s = .waitStO)

/-- The epilogue sites of the class. -/
def epTc (s : Epi.Site) : Bool := decide (s = .ld ∨ s = .waitLd ∨ s = .dealloc)

/-- The common start's sites of the class. -/
def dsTcB (s : DStart.Site) : Bool := decide (s = .alloc ∨ s = .relinq)

theorem dTc_sm (d : Sm.D) : Lk.dTc (.sm d) = smTc d.site := rfl
theorem dTc_epi (d : Epi.D) : Lk.dTc (.epi d) = epTc d.site := rfl
theorem dTc_ds (d : DStart.D) : Lk.dTc (.dstart d) = dsTcB d.site := rfl

theorem tc_loop {s : Sm.Site} (h : smTc s = true) : setup s = false := by
  cases s <;> simp_all [smTc, setup]

theorem tc_late {s : Sm.Site} (h : smTc s = true) : Sm.LateSite s := by
  cases s <;> simp_all [smTc, Sm.LateSite]

theorem smO_tc (s : Sm.Site) (h : smTc s = true) : smO s ≤ 3 := by
  cases s <;> simp_all [smO, smTc]

/-- The bit of the class, as a number. -/
def bit (b : Bool) : Nat := if b then 1 else 0

/-- **One iteration of the softmax region.** -/
theorem same_iter_tc {Dc : Nat → Prop} {d1 d : Sm.D} {c : Nat} (hJ1 : JS Dc d1) (hJ : JS Dc d)
    (ht : smTc d.site = true) (hi : d1.i = d.i) (h1 : setup d1.site = false)
    (hc : c = 0 ∨ c = bit (smTc d1.site))
    (h : smO d1.site + 4 * RD Dc d1 + c ≤ smO d.site + 4 * RD Dc d) :
    Bound.Sm.pos d.site ≤ Bound.Sm.pos d1.site ∧
      (c = bit (smTc d1.site) → Bound.Sm.pos d.site < Bound.Sm.pos d1.site) := by
  obtain ⟨hJa, hJb⟩ := hJ1
  obtain ⟨hJc, hJd⟩ := hJ
  obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only at hi h hJa hJb hJc hJd h1 ht hc ⊢
  subst hi
  by_cases hD : Dc i1 <;>
  cases s <;> simp only [smTc] at ht <;> (try exact absurd ht (by decide)) <;>
    cases s1 <;> simp only [setup] at h1 <;> (try exact absurd h1 (by decide)) <;>
    simp_all [smO, RD, postR, smTc, bit, mid, resc, Bound.Sm.pos] <;>
    (try rename_i j; have := j.isLt) <;> (try split_ifs at h) <;> omega

/-- **The softmax states in count order are in time order.** -/
theorem sm_tc_cmp {Dc : Nat → Prop} {d1 d : Sm.D} {c : Nat} (hJ1 : JS Dc d1) (hJ : JS Dc d)
    (ht : smTc d.site = true) (hc : c = 0 ∨ c = bit (smTc d1.site))
    (h : 4 * d1.i + smO d1.site + 4 * RD Dc d1 + c ≤ 4 * d.i + smO d.site + 4 * RD Dc d) :
    smT d1 ≤ smT d ∧ (c = bit (smTc d1.site) → smT d1 < smT d) := by
  have hd := smT_loop (tc_loop ht)
  by_cases hs : setup d1.site = true
  · have := smT_setup hs
    rw [hd]
    constructor <;> (try intro) <;> wt_omega
  have hs' : setup d1.site = false := by simpa using hs
  rcases lt_trichotomy d1.i d.i with hlt | heq | hgt
  · have := smT_hi d1
    rw [hd]
    have : slot d1.i + span ≤ slot d.i := by unfold slot; nlinarith
    constructor <;> (try intro) <;> wt_omega
  · obtain ⟨h1, h2⟩ := same_iter_tc hJ1 hJ ht heq hs' hc (by rw [heq] at h; omega)
    rw [hd, smT_loop hs', heq]
    have : Bound.Sm.pos d1.site ≤ 90 := by
      obtain ⟨s1, e1, i1, m1, l1, cw1, cv1, w1, v1, sv1, pf1, stg1⟩ := d1
      cases s1 <;> simp_all [setup, Bound.Sm.pos]
    have := Bound.Sm.pos_le d.site
    exact ⟨by omega, fun hc' => by have := h2 hc'; omega⟩
  · exfalso
    have h3 := rd_ge Dc d1
    have h4 := rd_le Dc d
    have h5 := nResc_mono Dc (show d.i + 1 ≤ d1.i by omega)
    have h6 := smO_tc d.site ht
    omega

/-- **The epilogue's states in count order are in time order.** -/
theorem epi_tc_cmp {d1 d : Epi.D} {w c : Nat} (hsk : d1.sk = d.sk)
    (hl1 : Epi.epLoad d1.site = true → d1.sk = false) (hl : Epi.epLoad d.site = true → d.sk = false)
    (ht : epTc d.site = true) (hw : d.site = .dealloc → w = 1)
    (hc : c = 0 ∨ c = bit (epTc d1.site))
    (h : epO d1.sk w d1.site + c ≤ epO d.sk w d.site) :
    epiT d1 ≤ epiT d ∧ (c = bit (epTc d1.site) → epiT d1 < epiT d) := by
  obtain ⟨s1, pr1, o1, sk1⟩ := d1
  obtain ⟨s, pr, o, sk⟩ := d
  simp only at hsk hl1 hl ht hw hc h ⊢
  subst hsk
  simp only [epiT]
  cases sk1 <;>
  cases s <;> simp only [epTc] at ht <;> (try exact absurd ht (by decide)) <;>
    cases s1 <;>
    simp_all [epO, epTc, bit, Epi.epLoad, Bound.Epi.siteRank] <;>
    (try rename_i j; have := j.isLt) <;> omega

/-- **The common start's states in count order are in time order** (warp 0). -/
theorem ds_tc_cmp {L : Launch} {g : Nat} {d1 d : DStart.D} {c : Nat} (hg : g % L.block < 32)
    (ht : dsTcB d.site = true) (hc : c = 0 ∨ c = bit (dsTcB d1.site))
    (h : dsTc L g d1.site + c ≤ dsTc L g d.site) :
    dstartT d1 ≤ dstartT d ∧ (c = bit (dsTcB d1.site) → dstartT d1 < dstartT d) := by
  obtain ⟨s1, tm1⟩ := d1
  obtain ⟨s, tm⟩ := d
  simp only at ht hc h ⊢
  cases s <;> simp only [dsTcB] at ht <;> (try exact absurd ht (by decide)) <;>
    cases s1 <;> simp_all [dsTc, dsTcB, bit, w0, dstartT] <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
