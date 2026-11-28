-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Export.StoreAddress
import Kernels.InklingRelDecode.Proof.Lib.StoreInject
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Lemmas.Kernel.Frame

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX

/-- The pcs of the epilogue's global stores. -/
def IsStoreSite (pc : Nat) : Prop := pc = 2682 ∨ ∃ j : Fin 64, pc = 2751 + j.val + j.val / 2

/-- **Two epilogue stores that overlap are the stores of one thread at one site**, so of one
footprint. -/
theorem store_pair {Q L m X g k g' k' pc pc' a a' bs bs' l} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.wr a bs⟩) (he' : X.get (g',k') = some ⟨pc',.wr a' bs'⟩)
    (site : IsStoreSite pc) (site' : IsStoreSite pc') (ca : a.Covers l) (cb : a'.Covers l) :
    g = g' ∧ a.SameFootprint a' := by
  have hg := Frame.lt_of_get hX he
  have hg' := Frame.lt_of_get hX he'
  obtain ⟨lane,vt,sz,loc⟩ := Export.store_address hp hX hf he site
  obtain ⟨lane',vt',sz',loc'⟩ := Export.store_address hp hX hf he' site'
  have bx := (Lib.coordinate_bounds hp hg).1
  have bx' := (Lib.coordinate_bounds hp hg').1
  have by1 : (L.ctaidOf (g/L.block)).get .y < 2 := (Lib.coordinate_bounds hp hg).2.1
  have by1' : (L.ctaidOf (g'/L.block)).get .y < 2 := (Lib.coordinate_bounds hp hg').2.1
  have bz := (Lib.coordinate_bounds hp hg).2.2
  have bz' := (Lib.coordinate_bounds hp hg').2.2
  have tn := Lib.token_lt hp bz vt
  have tn' := Lib.token_lt hp bz' vt'
  have pos := hp.nTokPos
  have r1 := Lib.rowM_lt (g%L.block)
  have r2 := Lib.rowM_lt (g'%L.block)
  obtain ⟨hl1,hl2,hl3,hl4⟩ := ca
  obtain ⟨hm1,hm2,hm3,hm4⟩ := cb
  have hrowS := fun u => (Lib.rowM_lt u)
  set x := (L.ctaidOf (g/L.block)).get .x with hx_def
  set y := (L.ctaidOf (g/L.block)).get .y with hy_def
  set z := (L.ctaidOf (g/L.block)).get .z with hz_def
  set t := g%L.block with ht_def
  set x' := (L.ctaidOf (g'/L.block)).get .x with hx'_def
  set y' := (L.ctaidOf (g'/L.block)).get .y with hy'_def
  set z' := (L.ctaidOf (g'/L.block)).get .z with hz'_def
  set t' := g'%L.block with ht'_def
  rcases loc with ⟨j,hpc,hloc⟩ | ⟨hpc,hbit,hloc⟩ <;>
    rcases loc' with ⟨j',hpc',hloc'⟩ | ⟨hpc',hbit',hloc'⟩
  · rw [hloc] at hl3 hl4
    rw [hloc'] at hm3 hm4
    simp only [oLoc, heads, headDim, sz] at hl3 hl4 hm3 hm4
    have idx : (((x * Q.nTok + (Q.qStart z + Lib.tokM t)) * 12 + (y * 6 + Lib.rowM t % 6)) * 128 +
        (64 * (t/16%2) + j.val)) = (((x' * Q.nTok + (Q.qStart z' + Lib.tokM t')) * 12 +
        (y' * 6 + Lib.rowM t' % 6)) * 128 + (64 * (t'/16%2) + j'.val)) := by omega
    have eq : oLoc Q x (Q.qStart z + Lib.tokM t) (y * 6 + Lib.rowM t % 6) (64 * (t/16%2) + j.val) =
        oLoc Q x' (Q.qStart z' + Lib.tokM t') (y' * 6 + Lib.rowM t' % 6)
          (64 * (t'/16%2) + j'.val) := by
      simp only [oLoc, heads, headDim]
      rw [idx]
    have jl := j.isLt
    have jl' := j'.isLt
    obtain ⟨hs, hK, hh, hc⟩ := Lib.oLoc_inj pos tn tn' (by omega) (by omega)
      (by omega) (by omega) eq
    obtain ⟨hz, htok⟩ := Lib.request_of_token hp bz bz' vt vt' hK
    simp only [Lib.tokM] at htok
    have row : Lib.rowM t = Lib.rowM t' := by omega
    have hy : y = y' := by omega
    have gg := Lib.thread_of_row hp hg hg' lane lane' hs hy hz row (by omega)
    exact ⟨gg, (by rw [hloc, hloc']; exact eq), by rw [sz, sz']⟩
  · exfalso
    rw [hloc] at hl3 hl4
    rw [hloc'] at hm3 hm4
    have r1 := Lib.oLoc_range (Q := Q) x (Q.qStart z + Lib.tokM t) (y * 6 + Lib.rowM t % 6)
      (64 * (t/16%2) + j.val) bx tn (by simp only [heads]; omega)
      (by simp only [headDim]; have := j.isLt; omega)
    have r2 := Lib.lseLoc_range (Q := Q) x' (Q.qStart z' + Lib.tokM t')
      (y' * 6 + Lib.rowM t' % 6) bx' tn' (by simp only [heads]; omega)
    have ap := hp.oApartLse
    unfold Apart at ap
    simp only [oLoc, lseLoc, heads, headDim, sz, sz'] at hl3 hl4 hm3 hm4 r1 r2
    omega
  · exfalso
    rw [hloc] at hl3 hl4
    rw [hloc'] at hm3 hm4
    have r1 := Lib.lseLoc_range (Q := Q) x (Q.qStart z + Lib.tokM t) (y * 6 + Lib.rowM t % 6)
      bx tn (by simp only [heads]; omega)
    have r2 := Lib.oLoc_range (Q := Q) x' (Q.qStart z' + Lib.tokM t') (y' * 6 + Lib.rowM t' % 6)
      (64 * (t'/16%2) + j'.val) bx' tn' (by simp only [heads]; omega)
      (by simp only [headDim]; have := j'.isLt; omega)
    have ap := hp.oApartLse
    unfold Apart at ap
    simp only [oLoc, lseLoc, heads, headDim, sz, sz'] at hl3 hl4 hm3 hm4 r1 r2
    omega
  · rw [hloc] at hl3 hl4
    rw [hloc'] at hm3 hm4
    simp only [lseLoc, heads, sz] at hl3 hl4 hm3 hm4
    have idx : ((x * Q.nTok + (Q.qStart z + Lib.tokM t)) * 12 + (y * 6 + Lib.rowM t % 6)) =
        ((x' * Q.nTok + (Q.qStart z' + Lib.tokM t')) * 12 + (y' * 6 + Lib.rowM t' % 6)) := by
      omega
    have eq : lseLoc Q x (Q.qStart z + Lib.tokM t) (y * 6 + Lib.rowM t % 6) =
        lseLoc Q x' (Q.qStart z' + Lib.tokM t') (y' * 6 + Lib.rowM t' % 6) := by
      simp only [lseLoc, heads]
      rw [idx]
    obtain ⟨hs, hK, hh⟩ := Lib.lseLoc_inj pos tn tn' (by omega) (by omega) eq
    obtain ⟨hz, htok⟩ := Lib.request_of_token hp bz bz' vt vt' hK
    simp only [Lib.tokM] at htok
    have row : Lib.rowM t = Lib.rowM t' := by omega
    have hy : y = y' := by omega
    have gg := Lib.thread_of_row hp hg hg' lane lane' hs hy hz row (by omega)
    exact ⟨gg, (by rw [hloc, hloc']; exact eq), by rw [sz, sz']⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
