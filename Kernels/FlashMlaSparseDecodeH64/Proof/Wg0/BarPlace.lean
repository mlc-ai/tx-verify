-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarSite
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time

@[expose] public section

/-! # Warpgroup 0's barriers by ordinal: barrier and place

With `R` blocks, the role's `o`-th barrier event (`o` from `0`) is block `o / 3`'s barrier
`o % 3` (`o < 3 R`: barrier 9, the warp pair's, barrier 9), then the epilogue's six barrier-9
events and barrier 12 (`idAt R p o`, `p` the warp's parity). Its site's place is `barPlace R o`
(`Wg0/Time.lean`): block `r` at `wg0Blk0 + stride * r` plus `0`, `17`, `35`; the epilogue at
`wg0EpiBlk0 + stride * R` plus `0`, `2` and `42 + 38 c`; barrier 12 at `endPlace`; past the
last, `endPlace + 3`.

* `bar_kind`: the barrier event of a barrier site is on barrier `idAt R p (barOrd d)`;
* `place_barPlace`: a state is no later than the place of its next barrier (`barOrd d`), strictly
  off a barrier site; `place_atBar`: at a barrier site it is there;
* `barPlace_lt`: the places rise with the ordinal up to barrier 12. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **The barrier of the role's `o`-th barrier event**, with `R` blocks and warp parity `p`. -/
def idAt (R p o : Nat) : Nat :=
  if o < 3 * R then (if o % 3 = 1 then 10 + p else 9) else if o < 3 * R + 6 then 9 else 12

/-- **The place of the role's `o`-th barrier site**, with `R` blocks. -/
def barPlace (R o : Nat) : Nat :=
  if o < 3 * R then
    wg0Blk0 + stride * (o / 3) + (if o % 3 = 0 then 0 else if o % 3 = 1 then 17 else 35)
  else if o = 3 * R then wg0EpiBlk0 + stride * R
  else if o = 3 * R + 1 then wg0EpiBlk0 + stride * R + 2
  else if o < 3 * R + 6 then wg0EpiBlk0 + stride * R + 42 + 38 * (o - 3 * R - 2)
  else if o = 3 * R + 6 then endPlace else endPlace + 3

/-- **The places rise with the ordinal** up to barrier 12. -/
theorem barPlace_lt {R o o' : Nat} (hR : R < 2 ^ 26) (h : o < o') (h' : o ≤ 3 * R + 6) :
    barPlace R o < barPlace R o' := by
  unfold barPlace
  simp only [wg0Blk0, wg0EpiBlk0, endPlace, endSlot, loopBase, stride, blockCap, wg0Off, w0Epi,
    wg0Org]
  split_ifs <;> omega

theorem barPlace_mono {R o o' : Nat} (hR : R < 2 ^ 26) (h : o ≤ o') (h' : o ≤ 3 * R + 6) :
    barPlace R o ≤ barPlace R o' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact Nat.le_refl _
  · exact (barPlace_lt hR h h').le

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- A loop site's offset from its block's frame is below its next barrier's (`0`, `17`, `35`,
the next frame), strictly off a barrier site. -/
theorem loop_tab (d : D) (hk : d.site.reg = .loop) :
    d.site.ord + elOff d + (if d.site.isBar then 0 else 1) ≤
      (if d.site.bidx = 0 then 0 else if d.site.bidx = 1 then 17 else if d.site.bidx = 2 then 35
        else 92) ∧ d.site.bidx ≤ 3 ∧ (d.site.isBar = true → d.site.bidx ≤ 2 ∧
        (if d.site.bidx = 0 then 0 else if d.site.bidx = 1 then 17 else 35) ≤
          d.site.ord + elOff d) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [Site.reg, reduceCtorEq] at hk <;>
    simp only [Site.ord, Site.bidx, Site.isBar, elOff, w0Wv, w0Wq, w0ArrV, w0ArrS,
      Nat.reduceEqDiff, ↓reduceIte, Bool.false_eq_true] <;>
    (try have := ‹Fin _›.isLt) <;> (try have := ‹Fin 4›.isLt) <;> (repeat' split) <;>
    (try simp only [imp_self, implies_true, false_implies, and_true]) <;> omega

/-- An epilogue site's offset is below its next barrier's (`0`, `2`, `42 + 38 c`, `160`),
strictly off a barrier site. -/
theorem epi_tab (d : D) (hk : d.site.reg = .epi) (hb : d.site ≠ .ebar) :
    d.site.ord + elOff d + (if d.site.isBar then 0 else 1) ≤
      (if d.site.bidx = 0 then 0 else if d.site.bidx = 1 then 2
        else if d.site.bidx < 6 then 42 + 38 * (d.site.bidx - 2) else 160) ∧
      d.site.bidx ≤ 6 ∧
      (d.site.isBar = true → d.site.bidx < 6 ∧
        (if d.site.bidx = 0 then 0 else if d.site.bidx = 1 then 2 else 42 + 38 * (d.site.bidx - 2))
          ≤ d.site.ord + elOff d) := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases s <;> simp only [Site.reg, reduceCtorEq] at hk <;> simp only [ne_eq, not_true_eq_false,
    reduceCtorEq, not_false_eq_true] at hb
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals simp [Site.ord, Site.bidx, Site.isBar, elOff, chunkBase, w0Wsv]
  all_goals omega

/-- The set-up's sites are before every barrier. -/
theorem setup_tab (s : Site) (hk : s.reg = .setup) : s.ord ≤ 5 ∧ s.bidx = 0 ∧ s.isBar = false := by
  cases s <;> simp only [Site.reg, reduceCtorEq] at hk <;> decide

/-- Only the closing sites are of the final region. -/
theorem fin_tab (s : Site) (hk : s.reg = .fin) : s = .dealloc ∨ s = .exit := by
  cases s <;> simp_all [Site.reg]

set_option linter.unusedSimpArgs false in
/-- **A state is no later than its next barrier** (`barOrd d`), strictly off a barrier site, and
at a barrier site it is there; the ordinal is at most `3 R + 7`, at a barrier site `3 R + 6`. -/
theorem place_barPlace {d : D} {n : Cnt → Nat} (hJ : RefCore L g d n) (hL : LaunchOk P L g d) :
    place d + (if d.site.isBar then 0 else 1) ≤ barPlace (blocksOf P L (g / L.block)) (barOrd d) ∧
      (d.site.isBar = true → place d = barPlace (blocksOf P L (g / L.block)) (barOrd d) ∧
        barOrd d ≤ 3 * blocksOf P L (g / L.block) + 6) ∧
      barOrd d ≤ 3 * blocksOf P L (g / L.block) + 7 := by
  have h26 := rounds_lt d.l0 d.l1
  by_cases hx : d.site = .ebar ∨ d.site = .dealloc ∨ d.site = .exit
  · have hR := rounds_blocks hL (by rcases hx with h | h | h <;> simp [h, Site.lens])
    rcases hx with hx | hx | hx <;>
      simp only [place, barOrd, hx, Site.reg, Site.bidx, Site.isBar, hR, barPlace,

        Bool.false_eq_true, ↓reduceIte, false_implies, true_implies, and_true,
        true_and] at h26 ⊢ <;>
      split_ifs <;> omega
  rw [place_reg (by tauto)]
  cases hk : d.site.reg
  · obtain ⟨ho, hb, hi⟩ := setup_tab d.site hk
    simp only [regPlace, barOrd, hk, hb, hi, barPlace, wg0Blk0, wg0EpiBlk0, loopBase, wg0Off,
      w0Epi, wg0Org, stride,
      Bool.false_eq_true, ↓reduceIte, false_implies, true_implies, and_true, true_and]
    split_ifs <;> omega
  · have hR := rounds_blocks hL (by
      cases hs : d.site <;> simp_all [Site.reg, Site.lens])
    have hT := loop_tab d hk
    have hJ' := hJ
    unfold RefCore at hJ'
    rw [hk] at hJ'
    obtain ⟨r, ⟨-, -, hr, hbi, -⟩, -⟩ := hJ'
    simp only [Control.D.words] at hbi hr
    have hr1 : d.bi.toNat - 1 = r := by rw [hbi, toNat_W (by omega)]; rfl
    rw [hR] at hr
    cases hb : d.site.isBar <;>
      simp only [regPlace, barOrd, hk, hr1, barPlace, wg0Blk0, wg0EpiBlk0, loopBase,
        wg0Off, w0Epi, wg0Org, stride, hb,
        Bool.false_eq_true, ↓reduceIte, false_implies, true_implies, and_true,
        true_and] at hT ⊢ <;>
      split_ifs at hT ⊢ <;> omega
  · have hR := rounds_blocks hL (by
      cases hs : d.site <;> simp_all [Site.reg, Site.lens])
    have hT := epi_tab d hk (fun h => hx (.inl h))
    cases hb : d.site.isBar <;>
      simp only [regPlace, barOrd, hk, hR, barPlace, wg0Blk0, wg0EpiBlk0, loopBase, wg0Off,
        w0Epi, wg0Org, stride, endPlace, endSlot, blockCap, hb,
        Bool.false_eq_true, ↓reduceIte, false_implies, true_implies, and_true,
        true_and] at hT h26 ⊢ <;>
      split_ifs at hT ⊢ <;> omega
  · rcases fin_tab _ hk with h | h <;> exact absurd (by simp [h]) hx

/-- The barrier sites by pc: `wg0_sync` off the block's second barrier and before barrier 12,
the warp pair's at the block's second, barrier 12 last. -/
theorem bar_site_pc {s : Site} (hs : s.isBar = true) :
    (s.pc ∈ [256, 569, 1154, 1156, 1342, 1502, 1659, 1817] →
        (s.reg = .loop → s.bidx ≠ 1) ∧ (s.reg = .epi → s.bidx < 6)) ∧
      (s.pc = 475 → s.reg = .loop ∧ s.bidx = 1) ∧ (s.pc = 1835 → s.reg = .epi ∧ s.bidx = 6) := by
  cases s <;> simp only [Site.isBar, Bool.false_eq_true] at hs
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **The barrier event of a barrier site** is on barrier `idAt R p (barOrd d)`, `R` the CTA's
blocks and `p` the warp word's parity. -/
theorem bar_kind {w : BitVec 64} {d : D} {n : Cnt → Nat} {e : Event} (hu : ∀ f, e.kind ≠ .ub f)
    (hev : EvK P L g w d e) (hb : Execution.isBar e = true) (hJ : RefCore L g d n)
    (hL : LaunchOk P L g d) : ∃ c, e.kind =
      .bar (idAt (blocksOf P L (g / L.block)) ((barW w).toNat - 10) (barOrd d)) c .sync := by
  have hW := barW_cases w
  have hK := evK_bar hu hev hb
  have hsb : d.site.isBar = true := isBar_of_pc (hK.imp (fun h => h.1)
    fun h => h.imp (fun h => h.1) fun h => h.1)
  obtain ⟨h9, hP, h12⟩ := bar_site_pc hsb
  rcases bar_ord hsb hJ hL with ⟨hreg, hbx, r, hr, ho⟩ | ⟨hreg, ho⟩ <;> rw [ho] <;>
    rcases hK with ⟨hpc, hk⟩ | ⟨hpc, hk⟩ | ⟨hpc, hk⟩ <;> rw [hk]
  · have := (h9 hpc).1 hreg
    exact ⟨some 128, by unfold idAt; congr 1; split_ifs <;> omega⟩
  · have := (hP hpc).2
    exact ⟨some 64, by unfold idAt; congr 1; split_ifs <;> omega⟩
  · have := (h12 hpc).1
    rw [hreg] at this
    cases this
  · have := (h9 hpc).2 hreg
    exact ⟨some 128, by unfold idAt; congr 1; split_ifs <;> omega⟩
  · have := (hP hpc).1
    rw [hreg] at this
    cases this
  · have := (h12 hpc).2
    exact ⟨none, by unfold idAt; congr 1; split_ifs <;> omega⟩

/-- **A barrier site fires a barrier event** (or undefined behaviour). -/
theorem evK_barSite {w : BitVec 64} {d : D} {e : Event} (hs : d.site.isBar = true)
    (hu : ∀ f, e.kind ≠ .ub f) (hev : EvK P L g w d e) : Execution.isBar e = true := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  cases s <;> simp only [Site.isBar, Bool.false_eq_true] at hs <;> unfold EvK at hev <;>
    simp only at hev <;> rw [hev] <;> rfl

/-- The barriers of the ordinals are 9 to 12. -/
theorem idAt_range (R o : Nat) {p : Nat} (hp : p < 2) : 9 ≤ idAt R p o ∧ idAt R p o ≤ 12 := by
  unfold idAt
  split_ifs <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
