-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeTc
import Lemmas.Flow.CtlStepsU
import Lemmas.Flow.VoteAnyMask

@[expose] public section

/-! # Warpgroup 0's events by state: the set-up and the block loop

One declaration per site family (`w0_shape`, then the inversion lemma of its instruction). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem shapeAt_smr (d : D) (hs : d.site = .smr) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_setMaxReg (P := fun e : Event => ∃ inst, e.kind = .setMaxReg true 224 inst) hf
    (by decide) (fun inst => ⟨inst, rfl⟩)

theorem shapeAt_nc (d : D) (hs : d.site = .sink ∨ d.site = .lenA ∨ d.site = .lenB) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | hs | hs <;> cases hs <;> w0_shape <;> exact fires_ncLoad_kind hf

theorem shapeAt_bwait (d : D) (hs : d.site = .bwait) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_bulkWait (L := L) (g := g) (P := fun e : Event => e.kind = .bulkWait .read 0) hf rfl

theorem shapeAt_arrL (d : D) (hs : d.site = .arrL) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_arrive_reg (by rw [hpc]; decide) (rg 938) hf

theorem shapeAt_arrV (d : D) (hs : d.site = .arrV) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_arrive_reg (by rw [hpc]; decide) (rg 1000) hf

theorem shapeAt_arrS (d : D) (hs : d.site = .arrS) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_arrive_reg (by rw [hpc]; decide) (rg 1717) hf

theorem shapeAt_wv (d : D) (hs : d.site = .wv) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_wait_reg (by rw [hpc]; decide) (rg 974) (rg 975) hf

theorem shapeAt_wq (d : D) (hs : d.site = .wq) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_wait_reg (by rw [hpc]; decide) (rg 977) (rg 978) hf

/-- The barrier-9 sites of the loop (the head and the row exchange). -/
theorem shapeAt_bar9 (hp : Pre P L m) (d : D) (hs : d.site = .bar0 ∨ d.site = .bar2) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | hs <;> cases hs
  · w0_bar9 972 973
  · w0_bar9 998 999

theorem shapeAt_bar1 (hp : Pre P L m) (d : D) (hs : d.site = .bar1) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_barSyncNR (P := fun e : Event => e.kind = .bar (barW w).toNat (some 64) .sync) hf
    (readBits_reg (rg 996)) (barW_lt w) (readBits_reg (rg 997)) (by decide) (by decide)
    (by rw [hp.block]; decide) rfl

/-- The `tcgen05` fences of the loop. -/
theorem shapeAt_tcFence (d : D)
    (hs : d.site = .tcfa ∨ d.site = .rsf ∨ d.site = .tcfb ∨ d.site = .rsfb ∨ d.site = .fpx) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | hs | hs | hs | hs <;> cases hs <;> w0_shape <;>
    (simp only [eventTmpl, Fires] at hf; exact congrArg Event.kind hf.1)

theorem shapeAt_sld (d : D) (hs : ∃ a k, d.site = .sld a k) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨a, k, hs⟩ := hs
  cases hs
  cases a <;> fin_cases k
  · w0_tcld 400 986
  · w0_tcld 432 987
  · w0_tcld 400 984
  · w0_tcld 432 985

theorem shapeAt_rld (d : D) (hs : ∃ c, d.site = .rld c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_tcld 0 1263
  · w0_tcld 64 1392
  · w0_tcld 128 1521
  · w0_tcld 192 1650

theorem shapeAt_rst (d : D) (hs : ∃ c, d.site = .rst c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_tcst 0 1263
  · w0_tcst 64 1392
  · w0_tcst 128 1521
  · w0_tcst 192 1650

/-- The Tensor Memory load waits of the loop. -/
theorem shapeAt_ldWait (hp : Pre P L m) (d : D) (hs : d.site = .sldw ∨ ∃ c, d.site = .rldw c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | ⟨c, hs⟩ <;> cases hs
  · w0_shape
    exact shape_tcWaitLd (P := fun e : Event => e.kind = .tc .waitLd) hf
      (by rw [hp.block]) rfl
  · fin_cases c <;> w0_shape <;>
      exact shape_tcWaitLd (P := fun e : Event => e.kind = .tc .waitLd) hf
        (by rw [hp.block]) rfl

theorem shapeAt_rstw (d : D) (hs : ∃ c, d.site = .rstw c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c <;> w0_shape <;>
    exact shape_tcWaitSt (P := fun e : Event => e.kind = .tc .waitSt ∨ ∃ f, e.kind = .ub f) hf
      (.inl rfl) (fun f => .inr ⟨f, rfl⟩)

/-- The shared reads of the loop at their exact words: the valid-mask word (`%r543`), the peer
reads (`%r17` plus the read's offset, two 8-byte elements), the row maxima (`%r14`). -/
theorem shapeAt_rd (d : D) (hs : d.site = .vm ∨ (∃ k, d.site = .pld k) ∨ d.site = .mld) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | ⟨k, hs⟩ | hs <;> cases hs
  · w0_shapeS
    change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact fires_rd_at (rg 1001) rfl rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf
  · fin_cases k <;> w0_shapeS <;>
    · change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
      exact ⟨hi, fires_rd_at (rg 475) (by decide) rfl hsub hf⟩
  · w0_shapeS
    change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
    exact fires_rd_at (rg 472) rfl rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf

/-- The shared writes of the loop at their exact words: the peer stores (`pstW`, 16 bytes), the
row maximum (`%r13`), the P stores (`%r16` plus the store's offset, four 4-byte elements). -/
theorem shapeAt_wr (d : D) (hs : (∃ k, d.site = .pst k) ∨ d.site = .mst ∨ ∃ k, d.site = .ost k) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with ⟨k, hs⟩ | hs | ⟨k, hs⟩ <;> cases hs
  · fin_cases k <;> w0_shapeS <;>
    · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
      exact fires_wr_at (regs_of_factsFrom hF (by decide +kernel)) rfl rfl
        (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf
  · w0_shapeS
    change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    exact fires_wr_at (rg 471) rfl rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf
  · fin_cases k <;> w0_shapeS <;>
    · change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
      exact ⟨hi, fires_wr_at (rg 474) (by decide) rfl hsub hf⟩

theorem shapeAt_vote (d : D) (hs : d.site = .vote) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_cont (P := fun e : Event =>
    (∃ p r, e.kind = .voteMode .any (2 ^ 32 - 1) p r) ∨ ∃ f, e.kind = .ub f) hf ⟨nofun, nofun⟩
    (fun _ hf' => by
      obtain ⟨p, r, rfl⟩ := fires_voteAnyU_mask (readBits_reg (rg 1112)) hf'
      exact .inl ⟨p, r, rfl⟩) (fun f => .inr ⟨f, rfl⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
