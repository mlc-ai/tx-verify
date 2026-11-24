-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WtMono

@[expose] public section

/-!
# The slots and bands of the virtual time

The slot schedule of `WtTime.lean` puts the loader's iteration `i` in the band `[slot i, slot i +
100)`, the MMA warp's in `[slot i + 100, slot i + 200)` and the softmax region's in
`[slot i + 200, slot i + 300)`. The band lemmas (`loaderT_band` and the others) state this for the
states of the loop; the waits' lag proofs (`Wk*`, `Wm*`, `Wv*`, `Wn*`) compare times through them
(the development notes, "Progress layer: the virtual time"). The prologue's copies and arrivals (the
first `num_pre` uses of the KV ring) and the setup before the loop are before every slot
(`pre_lt_slot`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

/-! ### Slots -/

theorem slot_lt_slot {i i' : Nat} (h : i < i') : slot i + span ≤ slot i' := by
  unfold slot span
  have := Nat.mul_le_mul_left 400 (show i + 1 ≤ i' from h)
  omega

theorem slot_le_slot {i i' : Nat} (h : i ≤ i') : slot i ≤ slot i' := by
  unfold slot
  have := Nat.mul_le_mul_left span h
  omega

/-! ### The bands -/

/-- The loader's loop sites are in the loader band of their slot. -/
theorem loaderT_band (d : Loader.D) (h : d.site.inLoop = true) :
    slot d.i ≤ loaderT d ∧ loaderT d < slot d.i + bandM := by
  obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
  cases s <;> simp only [Loader.Site.inLoop, Bool.false_eq_true] at h <;>
    simp only [loaderT, Bound.Loader.pos] <;> wt_omega

/-- The MMA warp's loop sites are in the MMA band of their slot. -/
theorem mmaT_band (d : Mma.D) (h : Mma.QkSite d.site ∨ Mma.PvSite d.site) :
    slot d.i + bandM ≤ mmaT d ∧ mmaT d < slot d.i + bandS := by
  obtain ⟨s, i, n, tm, pro⟩ := d
  cases s <;> simp only [Mma.QkSite, Mma.PvSite, or_self, or_false, false_or] at h <;>
    simp only [mmaT, Bound.Mma.pos] <;> wt_omega

/-- The softmax region's loop sites are in the softmax band of their slot. -/
theorem smT_band (d : Sm.D) (h : Sm.LateSite d.site) :
    slot d.i + bandS ≤ smT d ∧ smT d < slot d.i + span := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [Sm.LateSite] at h <;> simp only [smT, Bound.Sm.pos] <;> wt_omega

/-- A loop site of the softmax region that is not a setup site: the loop's bias loads and the
`LateSite`s. -/
theorem smT_loop_band (d : Sm.D) (h : ∀ k, d.site ≠ .pre k) (h1 : d.site ≠ .setMaxReg)
    (h2 : d.site ≠ .bar0) : slot d.i + bandS ≤ smT d ∧ smT d < slot d.i + span := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | exact absurd rfl (h _)
    | (simp only [smT, Bound.Sm.pos]; wt_omega)

/-- The setup before the loop is before every slot. -/
theorem smT_setup_lt (d : Sm.D) (h : d.site = .setMaxReg ∨ d.site = .bar0 ∨ ∃ k, d.site = .pre k) :
    smT d < loop0 := by
  obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only at h
  rcases h with rfl | rfl | ⟨k, rfl⟩ <;> simp only [smT] <;> wt_omega

/-! ### Before the loop -/

/-- **Every time before the loop is before every slot**: the prologue's, the common start's, the
setup of the loader, the MMA warp and the softmax region (the times of `DStart`, `ProA`, and the
sites before `slot 0`). -/
theorem pre_lt_slot (i : Nat) : c1 + 4 + 4 * 63 < slot i := by
  unfold c1 slot loop0
  omega

end

end PTX.Kernels.InklingRelDecode.Proof.Progress.Wt
