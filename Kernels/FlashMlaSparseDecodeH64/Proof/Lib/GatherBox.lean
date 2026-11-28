-- SPDX-License-Identifier: Apache-2.0
-- domain: complete
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Async.Tensor.TensorMemory
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The box of a gather4 load of a cache map

A gather4 load through a cache map (`encodeKv`, 132 words of 528-byte rows, a 144-word by one-row
box, four rows) copies, for slot `(x, y, z)` (column `x < 144`, box row `y < 4`, byte `z < 4`), the
word of tensor row `rows y`, column `origin 0 + x`, to the shared byte `576 y + 4 x + z` after its
base. The element is in the tensor when the column is below 132 and the row is below the map's
rows (`globalAddress`: byte `4 x + z` of row `r` is at `base + 528 r + 4 x + z`), and a row of
`-1` is outside it (`invalidAddress`, the zero fill). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GatherBox
open PTX TensorDescriptor

noncomputable section

/-- A gather tile covers four rows of the selected cache. -/
def box (base blocks stride : Nat) (cls : AllocationClass) (dst : Loc) (origin : Fin 2 → Int)
    (rows : Option (Fin 4 → Int)) : TensorBox :=
  ⟨1, (encodeKv base blocks stride cls).fourRows, origin, dst, rows⟩

theorem shape (base blocks stride : Nat) (cls : AllocationClass) :
    let d := (encodeKv base blocks stride cls).fourRows
    TensorTile.count d.box 0 = 144 ∧ TensorTile.rows d.box = 4 ∧ d.format.bytes = 4 := by
  norm_num [encodeKv, Descriptor.fourRows, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, Fin.cases, Format.bytes]

/-- The slot of column `x`, box row `row` and byte `b`. -/
def slot (base blocks stride : Nat) (cls : AllocationClass) (row : Fin 4) (x : Fin 144)
    (b : Fin 4) : TensorTransfer.Slot (encodeKv base blocks stride cls).fourRows :=
  have hs := shape base blocks stride cls
  ⟨⟨x.val, by rw [hs.1]; exact x.isLt⟩,
    ⟨row.val, by rw [hs.2.1]; exact row.isLt⟩,
    ⟨b.val, by rw [hs.2.2]; exact b.isLt⟩⟩

theorem slotAt (base blocks stride : Nat) (cls : AllocationClass) (row : Fin 4) (x : Fin 144)
    (b : Fin 4) :
    TensorTransfer.slotAt (encodeKv base blocks stride cls).fourRows x.val row.val b.val =
      some (slot base blocks stride cls row x b) := by
  obtain ⟨hx, hr, hb⟩ := shape base blocks stride cls
  unfold TensorTransfer.slotAt
  simp only [hx, hr, hb, x.isLt, row.isLt, b.isLt, dite_eq_left]
  rfl

private theorem coords {base blocks stride : Nat} {cls : AllocationClass} (dst : Loc)
    (o : Fin 2 → Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    let t := box base blocks stride cls dst o (some rows)
    TensorTransfer.coord t.descriptor t.origin t.rows (slot base blocks stride cls row x b) =
      ![o 0 + (x.val : Int), rows row] := by
  funext i
  have hmod : row.val % 4 = row.val := Nat.mod_eq_of_lt row.isLt
  fin_cases i <;> simp [box, TensorTransfer.coord, slot, hmod]

/-- **A selected element's global byte**: the origin's column is `0`, the row `rows row` is the
row `r` of the cache, the column is below 132. -/
theorem globalAddress {base blocks stride : Nat} {cls : AllocationClass} (dst : Loc)
    (o : Fin 2 → Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4)
    (ho : o 0 = 0) {r : Nat} (hr : rows row = r) (hrow : r < blocks * (stride / 528))
    (hx : x.val < 132) :
    (box base blocks stride cls dst o (some rows)).globalAddress
        (slot base blocks stride cls row x b) = some (base + r * 528 + 4 * x.val + b.val) := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress
  rw [coords, ho, hr]
  let geom := geometry (encodeKv base blocks stride cls).fourRows
  let c : Fin 2 → Int := ![0 + (x.val : Int), r]
  have hin : TensorAddress.InBounds geom c := by
    intro i
    fin_cases i <;> simp [geom, c, geometry, encodeKv, Descriptor.fourRows, hx]
    exact_mod_cast hrow
  have hb : b.val < geom.elementBytes := b.isLt
  change TensorAddress.lookup geom c b.val = _
  rw [TensorAddress.lookup, ite_eq_left ⟨hin, hb⟩]
  congr 1
  simp [TensorAddress.byteAddress, geometry, geom, c, encodeKv, Descriptor.fourRows,
    Fin.sum_univ_succ, Fin.cases, Format.bytes]
  omega

/-- **A row `-1` has no global byte**: the slot is the map's fill. -/
theorem invalidAddress {base blocks stride : Nat} {cls : AllocationClass} (dst : Loc)
    (o : Fin 2 → Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4)
    (hr : rows row = -1) :
    (box base blocks stride cls dst o (some rows)).globalAddress
        (slot base blocks stride cls row x b) = none := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress
  rw [coords]
  unfold TensorAddress.lookup
  apply ite_eq_right
  intro hh
  have hrow := hh.1 (1 : Fin 2)
  simp [hr] at hrow

/-- **The shared byte of a slot**: a 576-byte row pitch, no swizzle. -/
theorem sharedLoc {base blocks stride : Nat} {cls : AllocationClass} (dst : Loc)
    (o : Fin 2 → Int) (rows : Option (Fin 4 → Int)) (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    (box base blocks stride cls dst o rows).sharedLoc (slot base blocks stride cls row x b) =
      dst.at (576 * row.val + 4 * x.val + b.val) := by
  have hp : TensorTile.rowBytes (encodeKv base blocks stride cls).fourRows.box 4 .none = 576 := by
    simp only [TensorTile.rowBytes, (shape base blocks stride cls).1]
    rfl
  unfold TensorBox.sharedLoc TensorTile.sharedByte TensorTile.linearByte
  change { dst with addr := dst.addr + (TensorSwizzle.offset .none dst.addr
    (row.val * TensorTile.rowBytes (encodeKv base blocks stride cls).fourRows.box 4 .none
      + x.val * 4 + b.val)) } = _
  rw [TensorSwizzle.offset_none, hp]
  simp only [Loc.at]
  congr 1
  omega

/-- **The canonical box of a gather spec**: a box of the cache map `encodeKv` is `box` of its own
origin and rows. -/
theorem canonicalBox {s : TensorBox} {base blocks stride : Nat} {cls : AllocationClass}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ outer, Descriptor outer) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩) :
    ∃ o : Fin 2 → Int, s = box base blocks stride cls s.sharedBase o s.rows := by
  rcases s with ⟨outer, descriptor, origin, dst, rows'⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hd
  dsimp only at ho hd
  subst outer
  have he := eq_of_heq hd
  subst descriptor
  exact ⟨origin, rfl⟩

/-! ### The same for a gather spec -/

section Spec
variable {base blocks stride : Nat} {cls : AllocationClass} {s : TensorCopy.Spec}

/-- **The shared byte of a slot of a gather spec**. -/
theorem spec_writeLoc
    (hD : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
    {x y z : Nat} (hx : x < 144) (hy : y < 4) (hz : z < 4) :
    TensorCopy.writeLoc s x y z = some (s.sharedBase.at (576 * y + 4 * x + z)) := by
  rcases s with ⟨⟨outer, desc, origin, dst, rows'⟩, mbar, ca, grp⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hD
  dsimp only at ho hd ⊢
  subst ho
  have := eq_of_heq hd
  subst this
  unfold TensorCopy.writeLoc
  have h1 := slotAt base blocks stride cls ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩
  have h2 := sharedLoc (base := base) (blocks := blocks) (stride := stride) (cls := cls) dst
    origin rows' ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩
  simp only at h1 h2
  rw [h1]
  exact congrArg some h2

/-- **A slot with a selected row has the cache byte as its source.** -/
theorem spec_source_global
    (hD : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
    {ys : Fin 4 → Int} (hr : s.rows = some ys) (h0 : s.origin 0 = 0) {x y z r : Nat}
    (hx : x < 132) (hy : y < 4) (hz : z < 4) (hrow : ys ⟨y, hy⟩ = r)
    (hrng : r < blocks * (stride / 528)) :
    ∃ slot, TensorTransfer.slotAt s.descriptor x y z = some slot ∧
      TensorCopy.source s slot = .global (base + r * 528 + 4 * x + z) := by
  rcases s with ⟨⟨outer, desc, origin, dst, rows'⟩, mbar, ca, grp⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hD
  dsimp only at ho hd hr h0 ⊢
  subst ho
  have := eq_of_heq hd
  subst this
  subst hr
  refine ⟨slot base blocks stride cls ⟨y, hy⟩ ⟨x, by omega⟩ ⟨z, hz⟩,
    slotAt base blocks stride cls ⟨y, hy⟩ ⟨x, by omega⟩ ⟨z, hz⟩, ?_⟩
  have h := globalAddress (base := base) (blocks := blocks) (stride := stride) (cls := cls) dst
    origin ys ⟨y, hy⟩ ⟨x, by omega⟩ ⟨z, hz⟩ h0 hrow hrng hx
  change (match (box base blocks stride cls dst origin (some ys)).globalAddress
    (slot base blocks stride cls ⟨y, hy⟩ ⟨x, by omega⟩ ⟨z, hz⟩) with
    | some address => TensorTransfer.Source.global address
    | none => _) = _
  rw [h]

/-- **A slot with the row word `-1` has the zero fill as its source.** -/
theorem spec_source_fill
    (hD : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
    {ys : Fin 4 → Int} (hr : s.rows = some ys) {x y z : Nat}
    (hx : x < 144) (hy : y < 4) (hz : z < 4) (hrow : ys ⟨y, hy⟩ = -1) :
    ∃ slot, TensorTransfer.slotAt s.descriptor x y z = some slot ∧
      TensorCopy.source s slot = .fill .zero .u32 z := by
  rcases s with ⟨⟨outer, desc, origin, dst, rows'⟩, mbar, ca, grp⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hD
  dsimp only at ho hd hr ⊢
  subst ho
  have := eq_of_heq hd
  subst this
  subst hr
  refine ⟨slot base blocks stride cls ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩,
    slotAt base blocks stride cls ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩, ?_⟩
  have h := invalidAddress (base := base) (blocks := blocks) (stride := stride) (cls := cls) dst
    origin ys ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩ hrow
  change (match (box base blocks stride cls dst origin (some ys)).globalAddress
    (slot base blocks stride cls ⟨y, hy⟩ ⟨x, hx⟩ ⟨z, hz⟩) with
    | some address => TensorTransfer.Source.global address
    | none => TensorTransfer.Source.fill _ _ _) = _
  rw [h]
  rfl

/-- **The fill of a gather spec is the zero of `.u32`.** -/
theorem spec_fill
    (hD : (⟨s.outer, s.descriptor⟩ : Σ n, Descriptor n) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩) :
    s.descriptor.fill = .zero ∧ s.descriptor.format = .u32 := by
  rcases s with ⟨⟨outer, desc, origin, dst, rows'⟩, mbar, ca, grp⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hD
  dsimp only at ho hd ⊢
  subst ho
  have := eq_of_heq hd
  subst this
  exact ⟨rfl, rfl⟩

end Spec

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.GatherBox
