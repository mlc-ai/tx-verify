-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ShapeBase
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # Warpgroup 2's events by state: the set-up, the polls, the arrivals, the barrier, the exit -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem shapeAt_smr (d : D) (hs : d.site = .smr) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact shape_setMaxReg (P := fun e : Event => ∃ inst, e.kind = .setMaxReg true 208 inst) hf
    (by decide) fun inst => ⟨inst, rfl⟩

theorem shapeAt_len (d : D) (hs : d.site = .lenA ∨ d.site = .lenB) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  rcases hs with hs | hs <;> cases hs <;> dq_open <;>
  · refine shape_cont (P := fun e : Event => (∃ a bs, e.kind = .nc a bs) ∨ ∃ f, e.kind = .ub f)
      hf ⟨nofun, nofun⟩ (fun u hf' => ?_) (fun f => .inr ⟨f, rfl⟩)
    dsimp only [code, Site.pc] at hf'
    rw [← hpc] at hf'
    obtain ⟨loc, bs, -, he, -⟩ := Code.fires_nc rfl rfl rfl rfl rfl rfl (by rw [hpc]; decide) hf'
    exact .inl ⟨loc, bs, by rw [he]⟩

theorem shapeAt_wq (d : D) (hs : d.site = .wq) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 2434) (rg 2435) hf

theorem shapeAt_wraw (d : D) (hs : d.site = .wraw) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 2458) (rg 2459) hf

theorem shapeAt_wsv (d : D) (hs : d.site = .wsv) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact fires_wait_reg (by rw [hpc]; decide) (rg 2461) (rg 2462) hf

theorem shapeAt_fpx (d : D) (hs : d.site = .fpx) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

theorem shapeAt_arrD (hp : Pre P L m) (d : D) (hs : d.site = .arrD) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact shape_arrive
    (P := fun e : Event => e.kind = .arrive (smLoc L g (readyW L sb) 0) 0 1 true .cta)
    hf (by rw [hpc]; decide) rfl rfl (mbarLoc_bits (rg 2783) (ring_m8 hp sb (by decide))) rfl

theorem shapeAt_arrF (hp : Pre P L m) (d : D) (hs : d.site = .arrF) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact shape_arrive
    (P := fun e : Event => e.kind = .arrive (smLoc L g (freeW L sb) 0) 0 1 true .cta)
    hf (by rw [hpc]; decide) rfl rfl (mbarLoc_bits (rg 2784) (ring_m8 hp sb (by decide))) rfl

theorem shapeAt_bar (hp : Pre P L m) (d : D) (hs : d.site = .bar) :
    (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  exact shape_barSyncN_block (P := fun e : Event => e.kind = .bar 12 none .sync) hf
    (readW (rg 2878)) (by decide) (readW (rg 2879)) (by rw [hp.block]; rfl) (by rw [hp.block])
    rfl

theorem shapeAt_exit (d : D) (hs : d.site = .exit) : (code P L g w).ShapeAt (EvK L g) d := by
  obtain ⟨s, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases hs
  dq_open
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
