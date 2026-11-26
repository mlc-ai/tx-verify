-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds

@[expose] public section

/-! # Warpgroup 0's places against its arrivals

The state-level core of the time facts of `Wg0/Export/Time.lean`: a state is no later than its
block's arrivals or has made all of them (`Wg0.early_core`), and a state at the end of the code
has made every arrival of the CTA's blocks (`Wg0.fin_core`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {y : Nat}

private theorem setup_le (d : Wg0.Control.D) (h : d.site.reg = .setup) : Wg0.place d ≤ 5 := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [Wg0.Site.reg, reduceCtorEq] at h <;>
    simp [Wg0.place, Wg0.regPlace, Wg0.Site.reg, Wg0.Site.ord, w0ArrL]

private theorem loop_le (d : Wg0.Control.D) (h : d.site.reg = .loop) :
    d.site.ord + Wg0.elOff d ≤ w0ArrS ∧ (d.site.idx ≤ 2 → d.site.ord + Wg0.elOff d ≤ w0ArrV) := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [Wg0.Site.reg, reduceCtorEq] at h <;>
    simp only [Wg0.Site.ord, Wg0.elOff, Wg0.Site.idx, w0ArrS, w0ArrV, w0Wv, w0Wq] <;>
    (try have := ‹Fin _›.isLt) <;> omega

private theorem epi_le (d : Wg0.Control.D) (h : d.site.reg = .epi) (hi : d.site.idx ≠ 1) :
    Wg0.place d = Wg0.regPlace d .epi ∧ d.site.ord + Wg0.elOff d ≤ 5 := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [Wg0.Site.reg, reduceCtorEq] at h <;>
    simp only [Wg0.Site.idx, ne_eq, not_true_eq_false] at hi <;>
    simp [Wg0.place, Wg0.Site.reg, Wg0.Site.ord, Wg0.elOff, w0Wsv]

private theorem lens_of (d : Wg0.Control.D) (h : d.site.reg = .epi ∨ d.site.reg = .fin) :
    2 ≤ d.site.lens := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp_all [Wg0.Site.reg, Wg0.Site.lens]

/-- A state is at a place no later than its block's arrivals, or it has made all its arrivals
(the epilogue after the SV poll and the end: the arrivals of the CTA's `blocksOf` blocks). -/
theorem Wg0.early_core {d : Wg0.Control.D} {n : Wg0.Cnt → Nat}
    (hc : Wg0.RefCore L y d n) (hL : Wg0.LaunchOk P L y d) :
    (∃ a r i, (∀ l, n (.arrive l) = Wg0.arrCnt (Wg0.objs L y) a r i l) ∧
      (a = false → Wg0.place d ≤ 5) ∧ Wg0.place d ≤ wg0Blk0 + stride * r + w0ArrS ∧
      (i ≤ 2 → Wg0.place d ≤ wg0Blk0 + stride * r + w0ArrV)) ∨
    (∀ l, n (.arrive l) = Wg0.arrCnt (Wg0.objs L y) true (blocksOf P L (y / L.block)) 0 l) := by
  unfold Wg0.RefCore Wg0.RefAt at hc
  have k1 : wg0Blk0 = 252 := rfl
  have k2 : wg0EpiBlk0 = 216 := rfl
  have k3 : w0ArrS = 74 := rfl
  have k4 : w0ArrV = 36 := rfl
  have k5 : stride = 128 := rfl
  cases hk : d.site.reg <;> rw [hk] at hc
  · have := setup_le d hk
    exact .inl ⟨false, 0, 0, hc.2, fun _ => this, (by omega), fun _ => (by omega)⟩
  · obtain ⟨r, ⟨-, hR, hr, hbi, -⟩, hC⟩ := hc
    obtain ⟨h1, h2⟩ := loop_le d hk
    have hpl : Wg0.place d = wg0Blk0 + stride * r + d.site.ord + Wg0.elOff d := by
      rw [Wg0.place_reg (by refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp [h, Wg0.Site.reg] at hk),
        hk]
      simp only [Wg0.regPlace, Wg0.Control.D.words] at hbi ⊢
      rw [hbi, PTX.Flow.Arith32.toNat_W (by omega), Nat.add_sub_cancel]
    exact .inl ⟨true, r, _, hC.2, fun h => (by cases h), (by omega),
      fun hi => (by have := h2 hi; omega)⟩
  · obtain ⟨-, hC⟩ := hc
    simp only [Wg0.Control.D.words] at hC
    rw [Wg0.rounds_blocks hL (lens_of d (.inl hk))] at hC
    by_cases hi : d.site.idx = 1
    · exact .inr hC.2
    · simp only [hi, ↓reduceIte] at hC
      obtain ⟨hpl, h5⟩ := epi_le d hk hi
      simp only [Wg0.regPlace, Wg0.rounds_blocks hL (lens_of d (.inl hk))] at hpl
      exact .inl ⟨true, _, 0, hC.2, fun h => (by cases h), (by omega), fun _ => (by omega)⟩
  · obtain ⟨-, hC⟩ := hc
    simp only [Wg0.Control.D.words] at hC
    rw [Wg0.rounds_blocks hL (lens_of d (.inr hk))] at hC
    exact .inr hC.2

/-- A state at the end of the code: every arrival of the CTA's blocks made. -/
theorem Wg0.fin_core {d : Wg0.Control.D} {n : Wg0.Cnt → Nat}
    (hc : Wg0.RefCore L y d n) (hL : Wg0.LaunchOk P L y d) (hk : d.site.reg = .fin) :
    ∀ l, n (.arrive l) = Wg0.arrCnt (Wg0.objs L y) true (blocksOf P L (y / L.block)) 0 l := by
  unfold Wg0.RefCore Wg0.RefAt at hc
  rw [hk] at hc
  obtain ⟨-, hC⟩ := hc
  simp only [Wg0.Control.D.words] at hC
  rw [Wg0.rounds_blocks hL (lens_of d (.inr hk))] at hC
  exact hC.2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
