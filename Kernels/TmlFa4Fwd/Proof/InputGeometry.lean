-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

open TensorDescriptor
noncomputable section

/-- The rank-three input coordinates are column, absolute packed row and head. -/
def inputCoordinate (col row head : Nat) : Fin 3 → Int := ![(col : Int), (row : Int), (head : Int)]

private def packedInput (base cols rows heads : Nat) : TensorAddress.Geometry 3 :=
  ⟨base, 2, ![cols, rows, heads], ![2, 2 * cols * heads, 2 * cols]⟩

private theorem packedInput_lookup (base cols rows heads col row head byte : Nat) :
    TensorAddress.lookup (packedInput base cols rows heads) (inputCoordinate col row head) byte =
      if (col < cols ∧ row < rows ∧ head < heads) ∧ byte < 2 then
        some (base + 2 * ((row * heads + head) * cols + col) + byte)
      else none := by
  have hb : TensorAddress.InBounds (packedInput base cols rows heads)
      (inputCoordinate col row head) ↔ col < cols ∧ row < rows ∧ head < heads := by
    constructor
    · intro h
      exact ⟨by simpa [packedInput, inputCoordinate] using (h 0).2,
        by simpa [packedInput, inputCoordinate] using (h 1).2,
        by simpa [packedInput, inputCoordinate] using (h 2).2⟩
    · intro h axis
      fin_cases axis <;> simp [packedInput, inputCoordinate, h.1, h.2.1, h.2.2]
  have haddr :
      TensorAddress.byteAddress (packedInput base cols rows heads) (inputCoordinate col row head)
        byte = base + 2 * ((row * heads + head) * cols + col) + byte := by
    unfold TensorAddress.byteAddress
    rw [Fin.sum_univ_three]
    change base + ((col : Int).toNat * 2 + (row : Int).toNat * (2 * cols * heads) +
      (head : Int).toNat * (2 * cols)) + byte = _
    simp only [Int.toNat_natCast]
    ring
  unfold TensorAddress.lookup
  by_cases h : (col < cols ∧ row < rows ∧ head < heads) ∧ byte < 2
  · rw [ite_eq_left ⟨hb.mpr h.1, h.2⟩, ite_eq_left h, haddr]
  · rw [ite_eq_right (fun ht => h ⟨hb.mp ht.1, ht.2⟩), ite_eq_right h]

/-- Exact lookup for any nonnegative coordinates of the packed Q descriptor. -/
theorem qLookup_eq (p : Params) (col row head byte : Nat) :
    TensorAddress.lookup (geometry p.qMap) (inputCoordinate col row head) byte =
      if (col < 128 ∧ row < p.totalQ ∧ head < p.heads) ∧ byte < 2 then
        some ((p.qLoc row head col).at byte).addr else none :=
  packedInput_lookup p.qBase 128 p.totalQ p.heads col row head byte

/-- Exact lookup for the packed bias, including its 128 rows after the last packed query. -/
theorem biasLookup_eq (p : Params) (col row head byte : Nat) :
    TensorAddress.lookup (geometry p.biasMap) (inputCoordinate col row head) byte =
      if (col < 1280 ∧ row < p.totalQ + 128 ∧ head < p.heads) ∧ byte < 2 then
        some ((p.biasLoc row head col).at byte).addr else none :=
  packedInput_lookup p.biasBase 1280 (p.totalQ + 128) p.heads col row head byte

theorem qLookup (p : Params) {col row head byte : Nat}
    (hc : col < 128) (hr : row < p.totalQ) (hh : head < p.heads) (hk : byte < 2) :
    TensorAddress.lookup (geometry p.qMap) (inputCoordinate col row head) byte =
      some ((p.qLoc row head col).at byte).addr := by
  rw [qLookup_eq, ite_eq_left ⟨⟨hc, hr, hh⟩, hk⟩]

private def inputBox : TensorTile.Box 3 :=
  ⟨![64, 128, 1], ![1, 1, 1]⟩

private theorem inputIndexOf (x y : Nat) (hy : y < 128) :
    TensorTile.indexOf inputBox x y = ![x, y, 0] := by
  have hd : y / 128 = 0 := Nat.div_eq_of_lt hy
  funext axis
  fin_cases axis <;>
    simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step,
      inputBox, Nat.mod_eq_of_lt hy, hd] <;> rfl

private theorem tileCoordinateAdd (box : TensorTile.Box 3) (hbox : box = inputBox)
    (x y col row head : Nat) (hy : y < 128) :
    TensorTile.coord box (inputCoordinate col row head) (TensorTile.indexOf box x y) =
      inputCoordinate (col + x) (row + y) head := by
  rw [hbox, inputIndexOf x y hy]
  funext axis
  fin_cases axis <;> simp [TensorTile.coord, TensorTile.step, inputCoordinate, inputBox]

private theorem inputTileCoordinate {d : Descriptor 2} (hbox : d.box = inputBox)
    (slot : TensorTransfer.Slot d) (col row head : Nat) :
    TensorTransfer.coord d (inputCoordinate col row head) none slot =
      inputCoordinate (col + slot.1.val) (row + slot.2.1.val) head := by
  have hy : slot.2.1.val < 128 := by
    simpa [hbox, inputBox, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step] using slot.2.1.isLt
  exact tileCoordinateAdd d.box hbox _ _ col row head hy

/-- A Q coordinate outside any descriptor dimension has no source byte. -/
theorem qSlotAddress_eq (p : Params) {col row head : Nat} (slot : TensorTransfer.Slot p.qMap) :
    TensorTransfer.globalAddress p.qMap (inputCoordinate col row head) none slot =
      if col + slot.1.val < 128 ∧ row + slot.2.1.val < p.totalQ ∧ head < p.heads then
        some ((p.qLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val).addr
      else none := by
  unfold TensorTransfer.globalAddress
  rw [inputTileCoordinate rfl, qLookup_eq]
  have hk : slot.2.2.val < 2 := slot.2.2.isLt
  simp [hk]

/-- For bias, the descriptor's row dimension includes the physical padding. -/
theorem biasSlotAddress_eq (p : Params) {col row head : Nat}
    (slot : TensorTransfer.Slot p.biasMap) :
    TensorTransfer.globalAddress p.biasMap (inputCoordinate col row head) none slot =
      if col + slot.1.val < 1280 ∧ row + slot.2.1.val < p.totalQ + 128 ∧ head < p.heads then
        some ((p.biasLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val).addr
      else none := by
  unfold TensorTransfer.globalAddress
  rw [inputTileCoordinate rfl, biasLookup_eq]
  have hk : slot.2.2.val < 2 := slot.2.2.isLt
  simp [hk]

/-- The absolute row of a selected Q slot decides whether it is loaded or filled, once the
column and head are within the packed tensor. -/
theorem qSlotAddress (p : Params) {col row head : Nat} (slot : TensorTransfer.Slot p.qMap)
    (hc : col + slot.1.val < 128) (hh : head < p.heads) :
    TensorTransfer.globalAddress p.qMap (inputCoordinate col row head) none slot =
      if row + slot.2.1.val < p.totalQ then
        some ((p.qLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val).addr
      else none := by
  rw [qSlotAddress_eq]
  simp [hc, hh]

/-- The bias box uses the same slot coordinates and keeps the full physical row extent. -/
theorem biasSlotAddress (p : Params) {col row head : Nat} (slot : TensorTransfer.Slot p.biasMap)
    (hc : col + slot.1.val < 1280) (hh : head < p.heads) :
    TensorTransfer.globalAddress p.biasMap (inputCoordinate col row head) none slot =
      if row + slot.2.1.val < p.totalQ + 128 then
        some ((p.biasLoc (row + slot.2.1.val) head (col + slot.1.val)).at slot.2.2.val).addr
      else none := by
  rw [biasSlotAddress_eq]
  simp [hc, hh]

end
end PTX.Kernels.TmlFa4Fwd
