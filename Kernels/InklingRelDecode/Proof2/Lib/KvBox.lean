-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.LoaderPage
public import Kernels.InklingRelDecode.Proof.Thread.ShapeProCopy
public import Kernels.InklingRelDecode.Data.TensorMaps
public import Lemmas.Tensor.TensorAddress
public import Lemmas.Tensor.TensorReadSources

@[expose] public section

/-!
# The copies' boxes: the pure part

Moved from the first tree (names and namespaces unchanged): the CTA coordinates `splitOf`,
`kvhOf`, `reqOf`, `blkOf` (`Result/MmaPremises.lean`), `i32_mod`, `kvCopySpec_mod`,
`loader_copy_spec` (`Result/MmaLoader.lean`, now deleted), `kv_noOob` (`Result/MmaCopy.lean`),
`boxSlot`, `kv_readLoc` (`Result/MmaCopy.lean`), `kvCopy_readLoc_slot`, `kvCopy_readLoc_input`
(`Interface/SxGCopy.lean`), `ptc_kvspec` and its helpers (`Interface/ShapeKv.lean`; its premise
is now the three inherited parameter words instead of the first tree's startup record),
`kvbox_noOob` and `loader_box_ok`
(`Interface/ShapeBox.lean`). A copy of a loader or prologue state whose block exists and whose
block-table word is its slab's page is a box of the map without an out-of-bounds element.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.Flow PTX.Proof TensorDescriptor
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec i32 ldCopy ldDst ldBox kvReady)

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The split (`ctaid.x`), KV head (`ctaid.y`) and request (`ctaid.z`) of thread `g`'s CTA. -/
def splitOf (L : Launch) (g : Nat) : Nat := ProA.cta L g .x
def kvhOf (L : Launch) (g : Nat) : Nat := ProA.cta L g .y
def reqOf (L : Launch) (g : Nat) : Nat := ProA.cta L g .z

/-- The block of the request that iteration `i` of the thread's CTA works on: the split's
`i`-th block `split + i · num_splits`. -/
def blkOf (Q : Params) (L : Launch) (g i : Nat) : Nat := splitOf L g + i * Q.splits

/-- The coordinates of a copy are read as signed 32-bit words, so reducing them modulo `2 ^ 32`
changes nothing. -/
theorem i32_mod (x : Nat) : i32 (x % 2 ^ 32) = i32 x := by
  unfold i32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

theorem kvCopySpec_mod (Q : Params) (cta col row dst : Nat) (bar : Loc) :
    kvCopySpec Q cta (col % 2 ^ 32) (row % 2 ^ 32) dst bar = kvCopySpec Q cta col row dst bar := by
  unfold kvCopySpec
  rw [i32_mod, i32_mod]

/-- **A loader state's copy is the copy of `Spec`'s box.** For the loader state `d` (iteration
`d.i`) at one of the eight copy sites, with box `(isV, slab, hh)`, and the block-table word of the
box's slab the page of the slab `2 (split + i · num_splits) + slab`: the copy is `kvCopySpec` at
the origin `(kvh · head_cols + 128 isV + 64 hh, page · page_rows + kvh · head_rows)`, the
destination `sb + 32768 (i % 3) + 98304 isV + 8192 slab + 16384 hh` and the barrier
`kv_ready (i % 3)`. -/
theorem loader_copy_spec {P : Loader.Pro} {d : Loader.D} (hm : EvW.Words Q P)
    (hpro : Loader.ProEq L g P d) {isV slab hh : Nat} (hV : isV ≤ 1)
    (hpage : (if slab = 0 then d.p0 else d.p1) =
      Q.page (reqOf L g) (2 * blkOf Q L g d.i + slab)) :
    ldCopy Q L g d (decide (isV = 1), slab, hh) =
      kvCopySpec Q (g / L.block) (kvhOf L g * Q.headCols + 128 * isV + 64 * hh)
        (Q.page (reqOf L g) (2 * blkOf Q L g d.i + slab) * Q.pageRows + kvhOf L g * Q.headRows)
        (L.sharedBase + 32768 * (d.i % 3) + 98304 * isV + 8192 * slab + 16384 * hh)
        (kvReady L (g / L.block) (d.i % 3)) := by
  have e1 := EvW.ldCol_spec (d := d) hm hpro (decide (isV = 1)) hh
  have e2 := EvW.ldRow_spec (d := d) hm hpro slab
  unfold ldCopy
  simp only
  rw [e1, e2, kvCopySpec_mod, hpage]
  have hc : (if decide (isV = 1) = true then 128 else 0) = 128 * isV := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with rfl | rfl <;> simp
  have hd : (if decide (isV = 1) = true then 98304 else 0) = 98304 * isV := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hV with rfl | rfl <;> simp
  unfold ldDst
  simp only [hc, hd]
  rfl

/-- **A box inside the map has no out-of-bounds element.** -/
theorem kv_noOob (Q : Params) {col row : Nat} (hc : col + 64 ≤ Q.slotStride)
    (hr : row + 64 ≤ Q.rows) (hc2 : col < 2 ^ 31) (hr2 : row < 2 ^ 31) :
    ¬ TensorHasOob (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) ![i32 col, i32 row] none := by
  rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩, hn⟩
  apply hn
  intro axis
  simp [mapKv, TensorTile.count, TensorTile.step] at hx
  simp [mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step] at hy
  have hi : i32 col = col := EvW.i32_of_lt hc2
  have hj : i32 row = row := EvW.i32_of_lt hr2
  fin_cases axis
  · show 0 ≤ i32 col + ((x * 1 : Nat) : Int) ∧
      i32 col + ((x * 1 : Nat) : Int) < (Q.slotStride : Int)
    omega
  · show 0 ≤ i32 row + ((y * 1 : Nat) : Int) ∧ i32 row + ((y * 1 : Nat) : Int) < (Q.rows : Int)
    omega

/-- The slot of element `(x, y)`, byte `z` of a KV box. -/
def boxSlot (b sS rows : Nat) (cls : AllocationClass) {x y z : Nat} (hx : x < 64) (hy : y < 64)
    (hz : z < 2) : TensorTransfer.Slot (mapKv b sS rows cls) :=
  ⟨⟨x, by simpa [mapKv, TensorTile.count, TensorTile.step] using hx⟩,
    ⟨y, by simpa [mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step] using hy⟩,
    ⟨z, by simpa [mapKv, Format.bytes] using hz⟩⟩

/-- **A KV copy reads, at element `(x, y)` of its box inside the map, the cache element at the
box's origin plus `(x, y)`.** -/
theorem kv_readLoc (Q : Params) (cta col row dst : Nat) (bar : Loc) {x y z : Nat}
    (hno : ¬ TensorHasOob (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass)
        ![i32 col, i32 row] none)
    (hx : x < 64) (hy : y < 64) (hz : z < 2) :
    ∃ r c : Nat, (r : Int) = i32 row + y ∧ (c : Int) = i32 col + x ∧
      TensorCopy.readLoc (kvCopySpec Q cta col row dst bar) x y z =
        some ⟨.global, 0, Q.kvBase + 2 * (Q.slotStride * r + c) + z⟩ := by
  have hslot : TensorTransfer.slotAt (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) x y z =
      some (boxSlot Q.kvBase Q.slotStride Q.rows Q.kvClass hx hy hz) := by
    simp [TensorTransfer.slotAt, boxSlot, mapKv, TensorTile.count,
      TensorTile.step, TensorTile.rows, TensorTile.rowsOf, Format.bytes, hx, hy, hz]
  have hin := not_exists.mp hno (boxSlot Q.kvBase Q.slotStride Q.rows Q.kvClass hx hy hz)
  rw [not_not] at hin
  have h0 := hin 0
  have h1 := hin (Fin.succ 0)
  simp only [TensorTransfer.coord, TensorTransfer.index, TensorTile.coord, TensorTile.indexOf,
    geometry, mapKv, boxSlot, Fin.cases_succ, Fin.cases_zero] at h0 h1
  simp [TensorTile.step, TensorTile.unflatten] at h0 h1
  refine ⟨(i32 row + y).toNat, (i32 col + x).toNat, by omega, by omega, ?_⟩
  have hga : (kvCopySpec Q cta col row dst bar).globalAddress
      (boxSlot Q.kvBase Q.slotStride Q.rows Q.kvClass hx hy hz) =
      some (Q.kvBase + 2 * (Q.slotStride * (i32 row + y).toNat + (i32 col + x).toNat) + z) := by
    change TensorAddress.lookup (geometry (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass))
      (TensorTransfer.coord (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) ![i32 col, i32 row]
        none (boxSlot Q.kvBase Q.slotStride Q.rows Q.kvClass hx hy hz)) z = _
    rw [TensorAddress.lookup_some_iff]
    refine ⟨hin, by simpa [mapKv, geometry, Format.bytes] using hz, ?_⟩
    simp only [TensorAddress.byteAddress, Fin.sum_univ_succ, Fin.sum_univ_zero, geometry,
      mapKv, TensorTransfer.coord, TensorTransfer.index,
      TensorTile.coord, TensorTile.indexOf, boxSlot, Fin.cases_succ, Fin.cases_zero, Format.bytes]
    simp [TensorTile.step, TensorTile.unflatten]
    ring
  rw [TensorCopy.readLoc_source]
  refine Option.bind_eq_some_iff.mpr ⟨boxSlot Q.kvBase Q.slotStride Q.rows Q.kvClass hx hy hz,
    hslot, ?_⟩
  unfold TensorCopy.source
  erw [hga]

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem mul_mod_mod' (a b m : Nat) : a * (b % m) % m = a * b % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem sbRoom_of_pre (hpre : Pre Q L mem0) : ProA.SbRoom L := by
  have := hpre.sharedRange
  unfold sharedBytes at this
  unfold ProA.SbRoom
  omega

/-- **A prologue copy's spec in `Spec`'s quantities.** For the copy `i < 12` of the thread `g`
(block `i / 4`, V if `i % 2 = 1`, slab `i % 4 / 2`, half `hh = ProA.half d.dt (i / 4)`), with the
inherited words of the launch and the loaded block-table word of the slab the page of the block's
slab:
`EvW.kvCopySpec` at the origin `(kvh · head_cols + 128 isV + 64 hh, page · page_rows + kvh ·
head_rows)` and the destination `sharedBase + 32768 (i / 4) + 98304 isV + 8192 slab +
16384 hh`. -/
theorem ptc_kvspec (hpre : Pre Q L mem0) {d : ProA.D}
    (hw : d.dt.pro.w68 = Q.pageRows % 2 ^ 32 ∧ d.dt.pro.w69 = Q.headRows % 2 ^ 32 ∧
      d.dt.pro.w70 = Q.headCols % 2 ^ 32) {i : Nat} (hi : i < 12) (bar : Loc)
    (hpage : ProA.btW d.dt (2 * (i / 4) + i % 4 / 2) =
      Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + i / 4 * Q.splits) + i % 4 / 2)) :
    EvW.kvCopySpec Q (g / L.block) (ProA.copyX L g d.dt i) (ProA.copyY L g d.dt i)
        (ProA.copyDst L g d.dt i) bar =
      EvW.kvCopySpec Q (g / L.block)
        (ProA.cta L g .y * Q.headCols + 128 * (i % 2) + 64 * ProA.half d.dt (i / 4))
        (Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + i / 4 * Q.splits) + i % 4 / 2) *
          Q.pageRows + ProA.cta L g .y * Q.headRows)
        (L.sharedBase + 32768 * (i / 4) + 98304 * (i % 2) + 8192 * (i % 4 / 2) +
          16384 * ProA.half d.dt (i / 4)) bar := by
  obtain ⟨h68, h69, h70⟩ := hw
  have e1 : ProA.copyX L g d.dt i =
      (ProA.cta L g .y * Q.headCols + 128 * (i % 2) + 64 * ProA.half d.dt (i / 4)) %
        2 ^ 32 := by
    rw [ProA.copyX_form L g d.dt hi]
    unfold ProA.colOf
    have hm : Q.headCols % 2 ^ 32 * (ProA.cta L g .y % 2 ^ 32) % 2 ^ 32 =
        ProA.cta L g .y * Q.headCols % 2 ^ 32 := by
      rw [← Nat.mul_mod, Nat.mul_comm]
    rw [h70, hm]
    omega
  have e2 : ProA.copyY L g d.dt i =
      (Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + i / 4 * Q.splits) + i % 4 / 2) *
        Q.pageRows + ProA.cta L g .y * Q.headRows) % 2 ^ 32 := by
    rw [ProA.copyY_form L g d.dt hi]
    unfold ProA.rowOf
    have hm : Q.headRows % 2 ^ 32 * (ProA.cta L g .y % 2 ^ 32) % 2 ^ 32 =
        ProA.cta L g .y * Q.headRows % 2 ^ 32 := by
      rw [← Nat.mul_mod, Nat.mul_comm]
    have hm1 := mul_mod_mod' (Q.page (ProA.cta L g .z)
      (2 * (ProA.cta L g .x + i / 4 * Q.splits) + i % 4 / 2)) Q.pageRows (2 ^ 32)
    rw [h68, h69, hpage, hm]
    omega
  have e3 := ProA.copyDst_form L g d.dt (sbRoom_of_pre hpre) hi
  rw [e1, e2, e3]
  have e4 : L.sharedBase + 16384 * ProA.half d.dt (i / 4) + 32768 * (i / 4) +
      98304 * (i % 2) + 8192 * (i % 4 / 2) = L.sharedBase + 32768 * (i / 4) + 98304 * (i % 2) +
      8192 * (i % 4 / 2) + 16384 * ProA.half d.dt (i / 4) := by omega
  rw [e4]
  exact Result.Mma.kvCopySpec_mod Q _ _ _ _ _

/-- **A box of a block that exists is inside the map.** -/
theorem kvbox_noOob (hpre : Pre Q L mem0) {r s kvh isV hh : Nat} (hr : r < Q.b)
    (hs : s < 2 * Q.blocks r) (hkvh : kvh < 2) (hV : isV ≤ 1) (hH : hh ≤ 1) (cta dst : Nat)
    (bar : Loc) :
    ¬ TensorHasOob
      (EvW.kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).descriptor
      (EvW.kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).origin
      (EvW.kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).rows := by
  have hkc := hpre.kvCols kvh (by unfold kvHeads; omega)
  have hsl := hpre.slotStrideRange
  have hrr := hpre.rowsRange
  have hslab := hpre.slabInside r hr s hs kvh (by unfold kvHeads; omega)
  unfold headDim at hkc
  exact Result.Mma.kv_noOob Q (col := kvh * Q.headCols + 128 * isV + 64 * hh)
    (row := Q.page r s * Q.pageRows + kvh * Q.headRows) (by omega) (by omega) (by omega)
    (by omega)

open Result.Mma (reqOf kvhOf blkOf) in
/-- **A loader copy's box is inside the map.** -/
theorem loader_box_ok (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) {d : Loader.D}
    {P : Loader.Pro} (hm : EvW.Words Q P) (hpro : Loader.ProEq L g P d)
    (hi : d.i < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) {isV slab hh : Nat}
    (hV : isV ≤ 1) (hs : slab ≤ 1) (hH : hh ≤ 1)
    (hpage : (if slab = 0 then d.p0 else d.p1) =
      Q.page (ProA.cta L g .z) (2 * (ProA.cta L g .x + d.i * Q.splits) + slab)) :
    ¬ TensorHasOob (EvW.ldCopy Q L g d (decide (isV = 1), slab, hh)).descriptor
      (EvW.ldCopy Q L g d (decide (isV = 1), slab, hh)).origin
      (EvW.ldCopy Q L g d (decide (isV = 1), slab, hh)).rows := by
  obtain ⟨hx, hy, hz⟩ := ProA.cta_lt hpre hg
  have hblk := Result.Mma.blk_lt hpre.splitsPos hi
  rw [Result.Mma.loader_copy_spec hm hpro hV hpage]
  exact kvbox_noOob hpre (r := ProA.cta L g .z) (s := 2 * (ProA.cta L g .x + d.i * Q.splits) + slab)
    (kvh := ProA.cta L g .y) hz (by omega) (by unfold kvHeads at hy; omega) hV hH _ _ _

/-- A byte a KV copy reads is of a slot of its `(64, 64)` box of two-byte elements. -/
theorem kvCopy_readLoc_slot {cta col row dst : Nat} {bar : Loc} {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc (EvW.kvCopySpec Q cta col row dst bar) x y z = some l) :
    x < 64 ∧ y < 64 ∧ z < 2 := by
  unfold TensorCopy.readLoc TensorTransfer.sourceLoc at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨slot, hslot, -⟩ := h
  unfold TensorTransfer.slotAt at hslot
  split_ifs at hslot with h1 h2 h3
  simp only [EvW.kvCopySpec, mapKv, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, TensorDescriptor.Format.bytes] at h1 h2 h3
  simp at h1 h2 h3
  exact ⟨by omega, by omega, by omega⟩

/-- **A source byte of a K or V copy of a slab of a block that exists is an input byte.** -/
theorem kvCopy_readLoc_input (hpre : Pre Q L mem0) {r sl kvh isV hh cta dst : Nat} {bar : Loc}
    (hr : r < Q.b) (hs : sl < 2 * Q.blocks r) (hkvh : kvh < kvHeads) (hV : isV ≤ 1)
    (hH : hh ≤ 1) {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc (EvW.kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar) x y z = some l) :
    l.space = .global ∧ l.cta = 0 ∧ Q.reads l.addr := by
  obtain ⟨hx, hy, hz⟩ := kvCopy_readLoc_slot h
  have hkc := hpre.kvCols kvh hkvh
  have hsl := hpre.slotStrideRange
  have hrr := hpre.rowsRange
  have hslab := hpre.slabInside r hr sl hs kvh hkvh
  unfold headDim at hkc
  have hno := Result.Mma.kv_noOob Q (col := kvh * Q.headCols + 128 * isV + 64 * hh)
    (row := Q.page r sl * Q.pageRows + kvh * Q.headRows) (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨rr, cc, hrr', hcc', hl⟩ := Result.Mma.kv_readLoc Q cta _ _ dst bar (x := x) (y := y)
    (z := z) hno hx hy hz
  rw [h] at hl
  cases hl
  rw [EvW.i32_of_lt (by omega)] at hrr' hcc'
  have hr2 : rr = Q.page r sl * Q.pageRows + kvh * Q.headRows + y := by omega
  have hc2 : cc = kvh * Q.headCols + 128 * isV + 64 * hh + x := by omega
  subst hr2 hc2
  refine ⟨rfl, rfl, Or.inr (Or.inr (Or.inl ⟨r, hr, sl, hs, kvh, hkvh, y, hy,
    128 * isV + 64 * hh + x, by unfold headDim; omega, z, hz, ?_⟩))⟩
  ring

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
