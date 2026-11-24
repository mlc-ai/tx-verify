-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmRawGather
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather

open PTX.Proof

noncomputable section

/-- A gather tile covers four rows of the selected cache. The row coordinates replace
the second coordinate of the origin, which is retained separately by the model. -/
def box (base blocks stride : Nat) (cls : TensorDescriptor.AllocationClass)
    (dst : Loc) (originY : Int) (rows : Fin 4 → Int) : TensorBox :=
  ⟨1, (encodeKv base blocks stride cls).fourRows, ![0, originY], dst, some rows⟩

private theorem shape (base blocks stride : Nat) (cls : TensorDescriptor.AllocationClass) :
    let d := (encodeKv base blocks stride cls).fourRows
    TensorTile.count d.box 0 = 144 ∧ TensorTile.rows d.box = 4 ∧ d.format.bytes = 4 := by
  norm_num [encodeKv, TensorDescriptor.Descriptor.fourRows, TensorTile.count, TensorTile.step,
    TensorTile.rows, TensorTile.rowsOf, Fin.cases, TensorDescriptor.Format.bytes]

/-- A gather writes the selected 32-bit word byte at its row and column in the raw tile. -/
def slot (base blocks stride : Nat) (cls : TensorDescriptor.AllocationClass)
    (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    TensorTransfer.Slot (encodeKv base blocks stride cls).fourRows :=
  ⟨⟨x.val, by rw [(shape base blocks stride cls).1]; exact x.isLt⟩,
    ⟨row.val, by rw [(shape base blocks stride cls).2.1]; exact row.isLt⟩,
    ⟨b.val, by rw [(shape base blocks stride cls).2.2]; exact b.isLt⟩⟩

theorem slotAt (base blocks stride : Nat) (cls : TensorDescriptor.AllocationClass)
    (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    TensorTransfer.slotAt (encodeKv base blocks stride cls).fourRows x.val row.val b.val =
      some (slot base blocks stride cls row x b) := by
  obtain ⟨hx, hr, hb⟩ := shape base blocks stride cls
  unfold TensorTransfer.slotAt
  simp only [hx, hr, hb, x.isLt, row.isLt, b.isLt, dite_eq_left]
  rfl

private theorem coords {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    (dst : Loc) (oy : Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    let t := box base blocks stride cls dst oy rows
    TensorTransfer.coord t.descriptor t.origin t.rows (slot base blocks stride cls row x b) =
      ![(x.val : Int), rows row] := by
  funext i
  have hmod : row.val % 4 = row.val := Nat.mod_eq_of_lt row.isLt
  fin_cases i <;> simp [box, TensorTransfer.coord, slot, hmod]

/-- A valid token row and word use the contiguous global address of that cache byte. -/
theorem globalAddress {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    (dst : Loc) (oy : Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4)
    {r : Nat} (hr : rows row = r) (hrow : r < blocks * (stride / 528)) (hx : x.val < 132) :
    (box base blocks stride cls dst oy rows).globalAddress
      (slot base blocks stride cls row x b) = some (base + r * 528 + 4 * x.val + b.val) := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress
  rw [coords]
  let geom := TensorDescriptor.geometry (encodeKv base blocks stride cls).fourRows
  let c : Fin 2 → Int := ![↑x.val, ↑r]
  simp only [hr]
  have hin : TensorAddress.InBounds geom c := by
    intro i
    fin_cases i <;> simp [geom, c, TensorDescriptor.geometry, encodeKv,
      TensorDescriptor.Descriptor.fourRows, hx]
    exact_mod_cast hrow
  have hb : b.val < geom.elementBytes := b.isLt
  change TensorAddress.lookup geom c b.val = _
  rw [TensorAddress.lookup, ite_eq_left ⟨hin, hb⟩]
  congr 1
  simp [TensorAddress.byteAddress, TensorDescriptor.geometry, geom, c, encodeKv,
    TensorDescriptor.Descriptor.fourRows, Fin.sum_univ_succ, Fin.cases,
    TensorDescriptor.Format.bytes]
  omega

/-- An invalid sparse row uses the map's zero fill for every selected byte. -/
theorem invalidAddress {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    (dst : Loc) (oy : Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4)
    (hr : rows row = -1) :
    (box base blocks stride cls dst oy rows).globalAddress
      (slot base blocks stride cls row x b) = none := by
  unfold TensorBox.globalAddress TensorTransfer.globalAddress
  rw [coords]
  unfold TensorAddress.lookup
  apply ite_eq_right
  intro hh
  have hrow := hh.1 (1 : Fin 2)
  simp [hr] at hrow

/-- Each gather destination has a 576-byte row pitch and no swizzle. -/
theorem sharedLoc {base blocks stride : Nat} {cls : TensorDescriptor.AllocationClass}
    (dst : Loc) (oy : Int) (rows : Fin 4 → Int) (row : Fin 4) (x : Fin 144) (b : Fin 4) :
    (box base blocks stride cls dst oy rows).sharedLoc (slot base blocks stride cls row x b) =
      dst.at (576 * row.val + 4 * x.val + b.val) := by
  have hp : TensorTile.rowBytes (encodeKv base blocks stride cls).fourRows.box 4 .none =
      576 := by
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

/-- Recover a canonical gather tile from its actual descriptor, first coordinate and row list. -/
theorem canonicalBox {s : TensorBox} {base blocks stride : Nat}
    {cls : TensorDescriptor.AllocationClass} {rows : Fin 4 → Int}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ outer, TensorDescriptor.Descriptor outer) =
      ⟨1, (encodeKv base blocks stride cls).fourRows⟩)
    (hx : s.origin ⟨0, Nat.zero_lt_succ _⟩ = 0) (hr : s.rows = some rows) :
    ∃ y, s = box base blocks stride cls s.sharedBase y rows := by
  rcases s with ⟨outer, descriptor, origin, dst, rows'⟩
  obtain ⟨ho, hd⟩ := Sigma.mk.inj hd
  dsimp only at ho hd hx hr
  subst outer
  have he := eq_of_heq hd
  subst descriptor
  subst rows'
  refine ⟨origin 1, ?_⟩
  have heq : origin = ![0, origin 1] := by
    funext i
    fin_cases i
    · exact hx
    · rfl
  rw [box, ← heq]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result.RawGather
