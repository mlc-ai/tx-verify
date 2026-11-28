-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvFoot
public import Lemmas.Tensor.TensorAddress
public import Lemmas.Tensor.TensorReadSources

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

open TensorDescriptor
noncomputable section
variable {Q : Params} {L : Launch} {mem0 : Mem0}

theorem i32_of_lt {x : Nat} (h : x < 2 ^ 31) : i32 x = (x : Int) := by
  unfold i32
  rw [BitVec.toInt_ofNat', Int.bmod_def]
  have h1 : ((x : Int) % (2 ^ 32 : Nat)) = x := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  push_cast at h1 ⊢
  rw [h1]
  split_ifs with h2
  · rfl
  · exfalso; omega

theorem i32_mod (x : Nat) : i32 (x % 2 ^ 32) = i32 x := by
  unfold i32
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

theorem kvCopySpec_mod (Q : Params) (cta col row dst : Nat) (bar : Loc) :
    kvCopySpec Q cta (col % 2 ^ 32) (row % 2 ^ 32) dst bar = kvCopySpec Q cta col row dst bar := by
  unfold kvCopySpec
  rw [i32_mod, i32_mod]

/-- **A box inside the map has no out-of-bounds element.** -/
theorem kv_noOob (Q : Params) {col row : Nat} (hc : col + 64 ≤ Q.slotStride)
    (hr : row + 64 ≤ Q.rows) (hc2 : col < 2 ^ 31) (hr2 : row < 2 ^ 31) :
    ¬ TensorHasOob (mapKv Q.kvBase Q.slotStride Q.rows Q.kvClass) ![i32 col, i32 row] none := by
  rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩, hn⟩
  apply hn
  intro axis
  simp [mapKv, TensorTile.count, TensorTile.step] at hx
  simp [mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step] at hy
  have hi : i32 col = col := i32_of_lt hc2
  have hj : i32 row = row := i32_of_lt hr2
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
/-- **A box of a block that exists is inside the map.** -/
theorem kvbox_noOob (hpre : Pre Q L mem0) {r s kvh isV hh : Nat} (hr : r < Q.b)
    (hs : s < 2 * Q.blocks r) (hkvh : kvh < 2) (hV : isV ≤ 1) (hH : hh ≤ 1) (cta dst : Nat)
    (bar : Loc) :
    ¬ TensorHasOob
      (kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).descriptor
      (kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).origin
      (kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
        (Q.page r s * Q.pageRows + kvh * Q.headRows) dst bar).rows := by
  have hkc := hpre.kvCols kvh (by unfold kvHeads; omega)
  have hsl := hpre.slotStrideRange
  have hrr := hpre.rowsRange
  have hslab := hpre.slabInside r hr s hs kvh (by unfold kvHeads; omega)
  unfold headDim at hkc
  exact kv_noOob Q (col := kvh * Q.headCols + 128 * isV + 64 * hh)
    (row := Q.page r s * Q.pageRows + kvh * Q.headRows) (by omega) (by omega) (by omega)
    (by omega)

/-- A byte a KV copy reads is of a slot of its `(64, 64)` box of two-byte elements. -/
theorem kvCopy_readLoc_slot {cta col row dst : Nat} {bar : Loc} {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc (kvCopySpec Q cta col row dst bar) x y z = some l) :
    x < 64 ∧ y < 64 ∧ z < 2 := by
  unfold TensorCopy.readLoc TensorTransfer.sourceLoc at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨slot, hslot, -⟩ := h
  unfold TensorTransfer.slotAt at hslot
  split_ifs at hslot with h1 h2 h3
  simp only [kvCopySpec, mapKv, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, TensorDescriptor.Format.bytes] at h1 h2 h3
  simp at h1 h2 h3
  exact ⟨by omega, by omega, by omega⟩

/-- **A source byte of a K or V copy of a slab of a block that exists is the byte of the cache
at the box's origin plus the element.** -/
theorem kvCopy_readLoc_eq (hpre : Pre Q L mem0) {r sl kvh isV hh cta dst : Nat} {bar : Loc}
    (hr : r < Q.b) (hs : sl < 2 * Q.blocks r) (hkvh : kvh < kvHeads) (hV : isV ≤ 1)
    (hH : hh ≤ 1) {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc (kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar) x y z = some l) :
    x < 64 ∧ y < 64 ∧ z < 2 ∧ l = ⟨.global, 0, Q.kvBase + 2 * (Q.slotStride *
      (Q.page r sl * Q.pageRows + kvh * Q.headRows + y) +
      (kvh * Q.headCols + 128 * isV + 64 * hh + x)) + z⟩ := by
  obtain ⟨hx, hy, hz⟩ := kvCopy_readLoc_slot h
  have hkc := hpre.kvCols kvh hkvh
  have hsl := hpre.slotStrideRange
  have hrr := hpre.rowsRange
  have hslab := hpre.slabInside r hr sl hs kvh hkvh
  unfold headDim at hkc
  have hno := kv_noOob Q (col := kvh * Q.headCols + 128 * isV + 64 * hh)
    (row := Q.page r sl * Q.pageRows + kvh * Q.headRows) (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨rr, cc, hrr', hcc', hl⟩ := kv_readLoc Q cta _ _ dst bar (x := x) (y := y)
    (z := z) hno hx hy hz
  rw [h] at hl
  cases hl
  rw [i32_of_lt (by omega)] at hrr' hcc'
  have hr2 : rr = Q.page r sl * Q.pageRows + kvh * Q.headRows + y := by omega
  have hc2 : cc = kvh * Q.headCols + 128 * isV + 64 * hh + x := by omega
  subst hr2 hc2
  exact ⟨hx, hy, hz, rfl⟩

/-- **A source byte of a K or V copy of a slab of a block that exists is an input byte.** -/
theorem kvCopy_readLoc_input (hpre : Pre Q L mem0) {r sl kvh isV hh cta dst : Nat} {bar : Loc}
    (hr : r < Q.b) (hs : sl < 2 * Q.blocks r) (hkvh : kvh < kvHeads) (hV : isV ≤ 1)
    (hH : hh ≤ 1) {x y z : Nat} {l : Loc}
    (h : TensorCopy.readLoc (kvCopySpec Q cta (kvh * Q.headCols + 128 * isV + 64 * hh)
      (Q.page r sl * Q.pageRows + kvh * Q.headRows) dst bar) x y z = some l) :
    l.space = .global ∧ l.cta = 0 ∧ Q.reads l.addr := by
  obtain ⟨hx, hy, hz, rfl⟩ := kvCopy_readLoc_eq hpre hr hs hkvh hV hH h
  refine ⟨rfl, rfl, Or.inr (Or.inr (Or.inl ⟨r, hr, sl, hs, kvh, hkvh, y, hy,
    128 * isV + 64 * hh + x, by unfold headDim; omega, z, hz, ?_⟩))⟩
  ring

end

end PTX.Kernels.InklingRelDecode.Proof.Lib
