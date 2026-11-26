-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefBar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc

@[expose] public section

/-! # Warpgroup 0's barrier sites by their ordinal

At a barrier site the state's ordinal is block `r`'s barrier `bidx` (`3 r + bidx`, `r` below the
CTA's block count `blocksOf`, `bidx ≤ 2`) or the epilogue's (`3 R + bidx`) (`bar_ord`). A barrier
site is fixed by its region and `bidx` (`bar_pc`), so two lanes of one CTA at barrier sites of one
ordinal are at one pc (`bar_ord_pc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- **The ordinal of a barrier site**: block `r`'s or the epilogue's. -/
theorem bar_ord {d : D} {n : Cnt → Nat} (hs : d.site.isBar = true) (hJ : RefCore L g d n)
    (hL : LaunchOk P L g d) :
    (d.site.reg = .loop ∧ d.site.bidx ≤ 2 ∧
        ∃ r, r < blocksOf P L (g / L.block) ∧ barOrd d = 3 * r + d.site.bidx) ∨
      (d.site.reg = .epi ∧ barOrd d = 3 * blocksOf P L (g / L.block) + d.site.bidx) := by
  have hR := rounds_blocks hL
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  simp only [RefCore, Control.D.words] at hJ hR ⊢
  cases s <;> simp only [Site.isBar, Bool.false_eq_true] at hs
  case bar0 | bar1 | bar2 =>
    simp only [Site.reg, Site.idx, RefAt] at hJ
    obtain ⟨r, ⟨-, h26, hr, hbi, -⟩, -⟩ := hJ
    dsimp only at h26 hr hbi
    subst hbi
    have hr1 := toNat_W (show r + 1 < 2 ^ 64 by omega)
    rw [hR (by decide)] at hr
    refine .inl ⟨rfl, by decide, r, hr, ?_⟩
    simp only [barOrd, Site.reg, Site.bidx, hr1]
    omega
  all_goals
    refine .inr ⟨rfl, ?_⟩
    simp only [barOrd, Site.reg, hR (by simp [Site.lens])]

/-- The sites of the barrier pcs are the barrier sites. -/
theorem isBar_of_pc {s : Site}
    (h : s.pc ∈ [256, 569, 1154, 1156, 1342, 1502, 1659, 1817] ∨ s.pc = 475 ∨ s.pc = 1835) :
    s.isBar = true := by
  revert h
  cases s
  all_goals repeat' (rename_i x; fin_cases x)
  all_goals decide

/-- **A barrier site is fixed by its region and its place.** -/
theorem bar_pc {s s' : Site} (hs : s.isBar = true) (hs' : s'.isBar = true) (hr : s.reg = s'.reg)
    (hb : s.bidx = s'.bidx) : s.pc = s'.pc := by
  cases s <;> simp only [Site.isBar, Bool.false_eq_true] at hs <;>
    cases s' <;> simp only [Site.isBar, Bool.false_eq_true] at hs' <;>
    simp_all [Site.reg, Site.bidx, Fin.val_inj] <;> omega

/-- **Two states of one CTA at barrier sites of one ordinal are at one pc.** -/
theorem bar_ord_pc {h : Nat} {d d' : D} {n n' : Cnt → Nat} (hc : g / L.block = h / L.block)
    (hs : d.site.isBar = true) (hJ : RefCore L g d n) (hL : LaunchOk P L g d)
    (hs' : d'.site.isBar = true) (hJ' : RefCore L h d' n') (hL' : LaunchOk P L h d')
    (ho : barOrd d = barOrd d') : d.site.pc = d'.site.pc := by
  have h1 := bar_ord hs hJ hL
  have h2 := bar_ord hs' hJ' hL'
  rw [← hc] at h2
  refine bar_pc hs hs' ?_ ?_ <;>
    rcases h1 with ⟨k1, b1, r1, hr1, o1⟩ | ⟨k1, o1⟩ <;>
    rcases h2 with ⟨k2, b2, r2, hr2, o2⟩ | ⟨k2, o2⟩ <;>
    (try rw [k1, k2]) <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
