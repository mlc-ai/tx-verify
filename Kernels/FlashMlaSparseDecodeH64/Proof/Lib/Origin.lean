-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Core.Async.Tensor.TensorTransfer

@[expose] public section

/-! # The box origin of a tile access of the query and output maps

A tile load or store through the query map or the output map (`encodeTiled`: extents
`512, 64, s_q, b`, a `64 x 64 x 1 x 1` box) with the origin `(x, 0, q, e)` selects only elements
inside the tensor when `x + 64 ≤ 512`, `q < s_q` and `e < b` (`tile_inBounds`). `BoxOrigin` says an
access has that origin: coordinate `i` of the origin is entry `i` of the list. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- The origin `o` of a tensor access has the coordinates `xs` (missing ones are `0`). -/
def BoxOrigin {n : Nat} (o : Fin (n + 1) → Int) (xs : List Nat) : Prop :=
  ∀ i : Fin (n + 1), o i = ((xs.getD i.val 0 : Nat) : Int)

/-- The first coordinate of an origin of four coordinates. -/
theorem boxOrigin_zero {n : Nat} {o : Fin (n + 1) → Int} {x y z w : Nat}
    (h : BoxOrigin o [x, y, z, w]) : o 0 = x := by
  simpa using h 0

/-- **The coordinate of a slot of a tile access of the query or output map**: the slot at column
`s0`, row `s1` of a box with the origin `(x, 0, q, e)` is at the coordinate `(x + s0, s1, q, e)`. -/
theorem tile_coord {d : Descriptor 3} {base sq b : Nat} {fill : Fill}
    {cls : AllocationClass} {sH sS sB : Nat} (hd : d = encodeTiled base sH sS sB sq b fill cls)
    {org : Fin (3 + 1) → Int} {x q e : Nat} (ho : BoxOrigin org [x, 0, q, e])
    (slot : TensorTransfer.Slot d) :
    slot.1.val < 64 ∧ slot.2.1.val < 64 ∧ slot.2.2.val < 2 ∧
      TensorTransfer.coord d org none slot =
        (![((x + slot.1.val : Nat) : Int), (slot.2.1.val : Int), (q : Int), (e : Int)] :
          Fin (3 + 1) → Int) := by
  subst hd
  have hc : TensorTile.count (encodeTiled base sH sS sB sq b fill cls).box 0 = 64 := by
    simp [encodeTiled, TensorTile.count, TensorTile.step]
  have hr : TensorTile.rows (encodeTiled base sH sS sB sq b fill cls).box = 64 := by
    simp [encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
  have hy : (encodeTiled base sH sS sB sq b fill cls).format.bytes = 2 := by
    simp [encodeTiled, Format.bytes]
  have o0 : org 0 = x := by simpa [List.getD] using ho 0
  have o1 : org 1 = 0 := by simpa [List.getD] using ho 1
  have o2 : org 2 = q := by simpa [List.getD] using ho 2
  have o3 : org 3 = e := by simpa [List.getD] using ho 3
  obtain ⟨⟨s0, hs0'⟩, ⟨s1, hs1'⟩, ⟨s2, hs2⟩⟩ := slot
  have hs0 : s0 < 64 := hc ▸ hs0'
  have hs1 : s1 < 64 := hr ▸ hs1'
  have hq1 : s1 % 64 = s1 := Nat.mod_eq_of_lt hs1
  have hq2 : s1 / 64 = 0 := Nat.div_eq_of_lt hs1
  have hidx : TensorTile.indexOf (encodeTiled base sH sS sB sq b fill cls).box s0 s1 =
      ![s0, s1, 0, 0] := by
    funext i
    fin_cases i <;> simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count,
      TensorTile.step, encodeTiled, Fin.cases, hq1, hq2] <;> rfl
  refine ⟨hs0, hs1, by omega, ?_⟩
  funext i
  simp only [TensorTransfer.coord, TensorTile.coord, TensorTransfer.index, hidx]
  fin_cases i <;> simp [TensorTile.step, encodeTiled, o0, o1, o2, o3]

/-- **A tile access of the query or output map with an in-range origin is in bounds.** -/
theorem tile_inBounds {o : Nat} {d : Descriptor o} {base sq b : Nat} {fill : Fill}
    {cls : AllocationClass} {sH sS sB : Nat}
    (hd : (⟨o, d⟩ : Σ n, Descriptor n) = ⟨3, encodeTiled base sH sS sB sq b fill cls⟩)
    {org : Fin (o + 1) → Int} {x q e : Nat} (hx : x + 64 ≤ 512) (hq : q < sq) (he : e < b)
    (ho : BoxOrigin org [x, 0, q, e]) :
    ¬ TensorHasOob d org none := by
  obtain ⟨rfl, hd⟩ := Sigma.mk.inj_iff.mp hd
  cases hd
  have key := tile_coord (base := base) (sq := sq) (b := b) (fill := fill) (cls := cls)
    (sH := sH) (sS := sS) (sB := sB) rfl ho
  rintro ⟨slot, hbad⟩
  apply hbad
  intro axis
  obtain ⟨hs0, hs1, -, hco⟩ := key slot
  rw [hco]
  fin_cases axis <;> simp [geometry, encodeTiled] <;> omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
