-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Rings
public import Lemmas.Tensor.BoxWrite
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaBox

@[expose] public section

/-! # Where the ring copies write

The copies of a ring slot (`copySpec`) are boxes of 64 FP16 columns by `copyBytes / 128` rows
(128 for a Q half and a V block, 64 for a K half) with 128-byte swizzle, copy `j` at
`boxBase b j` (`copyBytes` apart from the region's start). So copy `j` writes element `(x, y)`,
byte `z` at `boxBase b j + offset .b128 (boxBase b j) (128 y + 2 x + z)` of its CTA
(`copy_writeLoc`); each byte of the slot's region is written by one slot of one box
(`region_box`), and a copy's bytes lie in its box (`copy_box`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof TensorDescriptor

noncomputable section

namespace Rings

variable {P : Params} {L : Launch}

theorem encodeTiled_geom {base rows heads batch boxRows : Nat} {fill : Fill}
    {cls : AllocationClass} :
    TensorTile.count (FlashAttn4Fwd.encodeTiled base rows heads batch boxRows fill cls).box 0 =
        64 ∧
      TensorTile.rows (FlashAttn4Fwd.encodeTiled base rows heads batch boxRows fill cls).box =
        boxRows := by
  simp [FlashAttn4Fwd.encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
    TensorTile.step]

/-- The geometry of a ring copy's map: 64 columns, `copyBytes / 128` rows, FP16, 128-byte
swizzle. -/
theorem copyMap_geom {b : FBar} (hb : b.isFull) :
    TensorTile.count (copyMap P b).box 0 = 64 ∧
      TensorTile.rows (copyMap P b).box = b.copyBytes / 128 ∧ (copyMap P b).format = .f16 ∧
      (copyMap P b).swizzle = .b128 := by
  have hQ := encodeTiled_geom (base := P.qBase) (rows := P.sq) (heads := P.h) (batch := P.b)
    (fill := P.qFill) (cls := P.qClass) (boxRows := 128)
  have hK := encodeTiled_geom (base := P.kBase) (rows := P.sk) (heads := P.h) (batch := P.b)
    (fill := P.kFill) (cls := P.kClass) (boxRows := 64)
  have hV := encodeTiled_geom (base := P.vBase) (rows := P.sk) (heads := P.h) (batch := P.b)
    (fill := P.vFill) (cls := P.vClass) (boxRows := 128)
  cases b <;> simp only [FBar.isFull, Bool.false_eq_true] at hb
  · exact ⟨hQ.1, hQ.2.trans (by norm_num [FBar.copyBytes]), rfl, rfl⟩
  · simp only [copyMap, FBar.copyBytes]
    split_ifs
    · exact ⟨hK.1, hK.2.trans (by norm_num), rfl, rfl⟩
    · exact ⟨hV.1, hV.2.trans (by norm_num), rfl, rfl⟩

/-- **Where a ring copy writes.** -/
theorem copy_writeLoc {g : Nat} {b : FBar} (hb : b.isFull) (cnt : Nat) {x y z : Nat}
    (hx : x < 64) (hy : y < b.copyBytes / 128) (hz : z < 2) :
    TensorCopy.writeLoc (copySpec P L g b cnt) x y z = some ⟨.shared, ctaOf L g,
      boxBase L b (cnt % b.copies) + TensorSwizzle.offset .b128 (boxBase L b (cnt % b.copies))
        (128 * y + 2 * x + z)⟩ := by
  obtain ⟨h0, hR, hf, hsw⟩ := copyMap_geom (P := P) hb
  exact TensorCopy.box_writeLoc (s := copySpec P L g b cnt) h0 hR hf hsw hx hy hz

/-- **A ring copy's bytes lie in its box**, of its CTA. -/
theorem copy_box {g : Nat} {b : FBar} (hb : b.isFull) {cnt x y z : Nat} {l : Loc}
    (h : TensorCopy.writeLoc (copySpec P L g b cnt) x y z = some l) :
    x < 64 ∧ y < b.copyBytes / 128 ∧ z < 2 ∧ l = ⟨.shared, ctaOf L g,
      boxBase L b (cnt % b.copies) + TensorSwizzle.offset .b128 (boxBase L b (cnt % b.copies))
        (128 * y + 2 * x + z)⟩ := by
  obtain ⟨h0, hR, hf, -⟩ := copyMap_geom (P := P) hb
  obtain ⟨hx, hy, hz⟩ := TensorCopy.writeLoc_bounds h
  have hx' : x < 64 := by
    have : TensorTile.count (copySpec P L g b cnt).descriptor.box 0 = 64 := h0
    omega
  have hy' : y < b.copyBytes / 128 := by
    have : TensorTile.rows (copySpec P L g b cnt).descriptor.box = b.copyBytes / 128 := hR
    omega
  have hz' : z < 2 := by
    have : (copySpec P L g b cnt).descriptor.format.bytes = 2 := by
      change (copyMap P b).format.bytes = 2; rw [hf]; rfl
    omega
  refine ⟨hx', hy', hz', ?_⟩
  rw [copy_writeLoc hb cnt hx' hy' hz'] at h
  exact (Option.some.inj h).symm

/-- **Every byte of a ring region is written by one slot of one box.** -/
theorem region_box {b : FBar} (hb : b.isFull) {cta : Nat} {l : Loc} (hl : InRegion L cta b l) :
    ∃ j x y z, j < b.copies ∧ x < 64 ∧ y < b.copyBytes / 128 ∧ z < 2 ∧
      l = ⟨.shared, cta, boxBase L b j + TensorSwizzle.offset .b128 (boxBase L b j)
        (128 * y + 2 * x + z)⟩ := by
  obtain ⟨sp, ct, ad⟩ := l
  obtain ⟨hsp, hc, h1, h2⟩ := hl
  simp only at hsp hc h1 h2
  subst hsp hc
  rw [regionSize_eq hb] at h2
  obtain ⟨hm, hpos⟩ := copyBytes_mul hb
  have hcb : 0 < b.copyBytes := by omega
  obtain ⟨d, hd⟩ : ∃ d, ad = L.sharedBase + b.regionOff + d := ⟨ad - (L.sharedBase + b.regionOff),
    by omega⟩
  subst hd
  have hj : d / b.copyBytes < b.copies := by
    rw [Nat.div_lt_iff_lt_mul hcb]
    omega
  have hoff : d % b.copyBytes < 128 * (b.copyBytes / 128) := by
    have := Nat.mod_lt d hcb
    omega
  obtain ⟨x, y, z, hx, hy, hz, hof⟩ := TensorCopy.box_writeLoc_surj
    (base := boxBase L b (d / b.copyBytes)) hoff
  refine ⟨d / b.copyBytes, x, y, z, hj, hx, hy, hz, ?_⟩
  rw [hof]
  simp only [boxBase, Loc.mk.injEq, true_and]
  have := Nat.div_add_mod d b.copyBytes
  rw [Nat.mul_comm] at this
  omega

end Rings

end
end PTX.Kernels.FlashAttn4Fwd.Proof
