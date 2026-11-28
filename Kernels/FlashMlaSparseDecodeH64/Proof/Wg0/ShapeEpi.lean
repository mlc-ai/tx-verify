-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Stage
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.ShapeTc
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid

@[expose] public section

/-! # Warpgroup 0's events by state: the epilogue

One declaration per site family (`w0_shape`, then the inversion lemma of its instruction). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}

theorem shapeAt_ebar9 (hp : Pre P L m) (d : D) (hs : d.site = .ebar0 ∨ d.site = .ebar1) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | hs <;> cases hs <;> w0_bar9 1725 1726

theorem shapeAt_obar (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .obar c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_bar9 1906 1907
  · w0_bar9 2077 2078
  · w0_bar9 2247 2150
  · w0_bar9 2416 2417

theorem shapeAt_ebar (hp : Pre P L m) (d : D) (hs : d.site = .ebar) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_barSyncN_block (P := fun e : Event => e.kind = .bar 12 none .sync) hf
    (readBits_reg (rg 2425)) (by decide) (readBits_reg (rg 2426)) (by rw [hp.block]; rfl)
    (by rw [hp.block]) rfl

theorem shapeAt_wsv (d : D) (hs : d.site = .wsv) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact fires_wait_reg (by rw [hpc]; decide) (rg 1736) (rg 2954) hf

/-- The fences of the epilogue. -/
theorem shapeAt_eFence (d : D) (hs : d.site = .efa ∨ ∃ c, d.site = .ofpx c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | ⟨c, hs⟩ <;> cases hs
  · w0_shape
    simp only [eventTmpl, Fires] at hf
    exact congrArg Event.kind hf.1
  · fin_cases c <;> w0_shape <;>
      (simp only [eventTmpl, Fires] at hf; exact congrArg Event.kind hf.1)

theorem shapeAt_old (d : D) (hs : ∃ c, d.site = .old c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_tcld 0 1809
  · w0_tcld 64 1980
  · w0_tcld 128 2150
  · w0_tcld 192 2319

theorem shapeAt_oldw (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .oldw c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c <;> w0_shape <;>
    exact shape_tcWaitLd (P := fun e : Event => e.kind = .tc .waitLd) hf (by rw [hp.block]) rfl

/-- The reads of the epilogue (the partner's row sum). -/
theorem shapeAt_eld (d : D) (hs : d.site = .eld) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shapeS
  change Fires _ (loadTmpl _ L g t .shared false _ _ _ _) e o at hf
  exact fires_rd_at (rg 472) rfl rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf

/-- The epilogue's row-sum store at its exact word (`%r13`) and the LSE's global write. -/
theorem shapeAt_ewr (d : D) (hs : d.site = .est ∨ d.site = .lse) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hs with hs | hs <;> cases hs
  · w0_shapeS
    change Fires _ (storeTmpl L g t .shared _ _ _ _) e o at hf
    exact fires_wr_at (rg 471) rfl rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf
  · w0_shapeS
    change Fires _ (storeTmpl L g t .global _ _ _ _) e o at hf
    exact fires_gwr_at (rg 3574) rfl (hsub.trans (by change el < 1 at hi; show el = 0; omega)) hf

/-- The staging stores of chunk `c` through the staging pointers. -/
theorem shapeAt_ost2 (hp : Pre P L m) (c : Fin 4) (d : D) (hs : ∃ k, d.site = .ost2 c k) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨k, hs⟩ := hs
  cases hs
  fin_cases c <;> fin_cases k <;> w0_shapeS <;>
  · exact ⟨hi, fires_gen_wr_at rfl rfl rfl rfl rfl rfl (regs_of_factsFrom hF (by decide +kernel))
      (stW_lt hp g (by decide)) rfl hsub (by decide) (by decide) hf⟩

theorem shapeAt_oel (d : D) (hs : ∃ c, d.site = .oel c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c
  · w0_elect 1912
  · w0_elect 2081
  · w0_elect 2250
  · w0_elect 2420

/-- **An output store's event**: the row of `fires_tensorStore_map`, and for a warp word below `2`
no gather rows and the origin `(128 w + col, 0, %ctaid.x, %ctaid.y)`. -/
private theorem otma_ev (hp : Pre P L m) {t : TState} {rx ry src col : Nat} {X sx y : BitVec 64}
    {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensorStore (.reg 3832) [.reg rx, .reg ry, .reg 459, .reg 460] src 0 none .tile none)) e
      o)
    (hs : t.regs src = some (.bits 32 sx)) (hm : t.regs 3832 = some (.bits 64 y))
    (hx : t.regs rx = some (w32 X)) (hy : t.regs ry = some (w32 (Arith32.i32 0))) (hcol : col ≤ 320)
    (h2 : t.regs 459 = some (b32 (ctaidX L g))) (h3 : t.regs 460 = some (b32 (ctaidY L g)))
    (hX : w.toNat < 2 → X = BitVec.ofNat 64 (128 * w.toNat + col)) :
    (∃ a s, e.kind = .tensorStore a s ∧ s.sharedBase = smLoc L g sx 0 ∧ a = y.toNat ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ s.descriptor = d ∧ (w.toNat < 2 → s.rows = none ∧
        BoxOrigin s.origin [128 * w.toNat + col, 0, ctaidX L g, ctaidY L g])) ∨
      ∃ f, e.kind = .ub f := by
  rcases fires_tensorStore_map hs hm hf with ⟨a, s, hk, hss, ha, d, hd, hdd⟩ | h
  · refine .inl ⟨a, s, hk, hss, ha, d, hd, hdd, fun hw => ?_⟩
    have hlt := ctaid_lt hp g
    have hsq := hp.sqLt
    have hb4 := hp.bLt
    have hx' : t.regs rx = some (b32 (128 * w.toNat + col)) := by rw [hx, hX hw]; rfl
    have hy' : t.regs ry = some (b32 0) := by rw [hy]; rfl
    exact tensorStore_origin hf hx' hy' h2 h3 (by omega) (by omega) (by omega) (by omega) hk
  · exact .inr h

open Arith32 in
/-- The coordinate registers of the output stores for a warp word below `2`. -/
private theorem otma_colRegs {w : BitVec 64} (hw : w.toNat < 2) :
    shl w 7 = BitVec.ofNat 64 (128 * w.toNat + 0) ∧
      addi (shl (shl w 1) 6) 64 = BitVec.ofNat 64 (128 * w.toNat + 64) ∧
      addi (shl (shl w 1) 6) 256 = BitVec.ofNat 64 (128 * w.toNat + 256) ∧
      addi (shl (shl w 1) 6) 320 = BitVec.ofNat 64 (128 * w.toNat + 320) := by
  obtain h | h : w.toNat = 0 ∨ w.toNat = 1 := by omega
  · obtain rfl : w = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide
  · obtain rfl : w = 1 := BitVec.eq_of_toNat_eq (by simpa using h)
    decide

theorem shapeAt_otma (hp : Pre P L m) (d : D) (hs : ∃ c, d.site = .otma c) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨c, hs⟩ := hs
  cases hs
  fin_cases c <;> w0_shape
  · exact otma_ev hp hf (rg 1913) (rg 3832) (rg 1914) (rg 1915) (by decide) (rg 459) (rg 460)
      fun hw => by obtain ⟨h, -, -, -⟩ := otma_colRegs hw; exact h
  · exact otma_ev hp hf (rg 2082) (rg 3832) (rg 2083) (rg 2084) (by decide) (rg 459) (rg 460)
      fun hw => by obtain ⟨-, h, -, -⟩ := otma_colRegs hw; exact h
  · exact otma_ev hp hf (rg 2251) (rg 3832) (rg 2252) (rg 2253) (by decide) (rg 459) (rg 460)
      fun hw => by obtain ⟨-, -, h, -⟩ := otma_colRegs hw; exact h
  · exact otma_ev hp hf (rg 2421) (rg 3832) (rg 2422) (rg 2423) (by decide) (rg 459) (rg 460)
      fun hw => by obtain ⟨-, -, -, h⟩ := otma_colRegs hw; exact h

theorem shapeAt_commit (d : D) (hs : d.site = .commit) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  exact shape_bulkCommit (L := L) (g := g) (P := fun e : Event => e.kind = .bulkCommit) hf rfl

theorem shapeAt_dealloc (d : D) (hs : d.site = .dealloc) :
    (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  have ha := readBits_reg (L := L) (g := g) (rg 2427)
  have hn := readBits_reg (L := L) (g := g) (rg 2428)
  simp only [eventTmpl, tcTmpl, ha, hn, bind, Except.bind, pure, Except.pure] at hf
  have h0 : (truncBits 32 (Arith32.i32 0)).toNat = 0 := by decide
  have h5 : (truncBits 32 (Arith32.i32 512)).toNat = 512 := by decide
  simp only [h0, h5] at hf
  split_ifs at hf <;> simp_all [ofExec, Fires, Tmem.validColumns, throw, throwThe,
    MonadExceptOf.throw]

theorem shapeAt_exit (d : D) (hs : d.site = .exit) : (code P L g w).ShapeAt (EvK P L g w) d := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases hs
  w0_shape
  simp only [eventTmpl, Fires] at hf
  exact congrArg Event.kind hf.1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
