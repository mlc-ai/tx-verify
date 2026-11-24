-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputLayout
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part046
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Kernels.TmlFa4Fwd.Flow.Code.Part120
public import Kernels.TmlFa4Fwd.Flow.Code.Part121
public import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Lemmas.Flow.Run
public import Lemmas.Flow.MemTmpl
public import Lemmas.Isa.Rule
public import Mathlib.Tactic.FinCases
public import Lemmas.Tensor.TensorSwizzle
public import Lemmas.Flow.ContinuingEvent
public import Lemmas.Snoc.ControlEffect
public import Kernels.TmlFa4Fwd.Proof2.Startup.Transparency

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue

open TensorDescriptor

noncomputable section

private def outputTile : TensorTile.Box 4 :=
  ⟨![32, 128, 1, 1], ![1, 1, 1, 1]⟩

theorem outputBoxWidthShared (p : Params) : TensorTile.count p.oMap.box 0 = 32 := by
  simp [TensorTile.count, TensorTile.step, Params.oMap]

theorem outputBoxRowsShared (p : Params) : TensorTile.rows p.oMap.box = 128 := by
  simp [TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step, Params.oMap]

private theorem outputTileIndex (x y : Nat) (hy : y < 128) :
    TensorTile.indexOf outputTile x y = ![x, y, 0, 0] := by
  have hd : y / 128 = 0 := Nat.div_eq_of_lt hy
  funext axis
  fin_cases axis <;>
    simp [TensorTile.indexOf, TensorTile.unflatten, TensorTile.count, TensorTile.step,
      outputTile, Nat.mod_eq_of_lt hy, hd] <;> rfl

private theorem outputTileCoordinate (p : Params) (batch row head col : Nat)
    (slot : TensorTransfer.Slot p.oMap) :
    TensorTransfer.coord p.oMap (oCoordinate p batch head row col) none slot =
      oCoordinate p batch head (row + slot.2.1.val) (col + slot.1.val) := by
  have hy : slot.2.1.val < 128 := outputBoxRowsShared p ▸ slot.2.1.isLt
  change TensorTile.coord outputTile (oCoordinate p batch head row col)
    (TensorTile.indexOf outputTile slot.1.val slot.2.1.val) = _
  rw [outputTileIndex _ _ hy]
  funext axis
  fin_cases axis <;> simp [TensorTile.coord, TensorTile.step, outputTile, oCoordinate,
    Int.add_assoc]

/-- A byte slot of a writeback subbox targets the packed output exactly when its query row
belongs to the selected request. The shifted TMA coordinate clips the tail of that request. -/
theorem writebackSlotDestination {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile : Nat} (stage : Fin 2) (subbox : Fin 4)
    (slot : TensorTransfer.Slot p.oMap) (hb : batch < p.batch) (hh : head < p.heads) :
    let row := stageRow tile stage + slot.2.1.val
    let col := 32 * subbox.val + slot.1.val
    TensorStore.destination (writebackStoreSpec p l g batch head tile stage subbox) slot =
      if row < p.qLength batch then
        some ((p.oLoc (p.qOffset batch + row) head col).at slot.2.2.val)
      else none := by
  dsimp only
  have hx : slot.1.val < 32 := outputBoxWidthShared p ▸ slot.1.isLt
  have hk : slot.2.2.val < 4 := slot.2.2.isLt
  have hs := subbox.isLt
  let row := stageRow tile stage + slot.2.1.val
  let col := 32 * subbox.val + slot.1.val
  have hcol : col < 128 := by dsimp [col]; omega
  change (TensorTransfer.globalAddress p.oMap (oCoordinate p batch head (stageRow tile stage)
    (32 * subbox.val)) none slot).map (fun addr => globalLoc addr) =
      if row < p.qLength batch then some ((p.oLoc (p.qOffset batch + row) head col).at
        slot.2.2.val) else none
  unfold TensorTransfer.globalAddress
  rw [outputTileCoordinate]
  change (TensorAddress.lookup (geometry p.oMap)
    (oCoordinate p batch head row col) slot.2.2.val).map globalLoc = _
  by_cases hr : row < p.qLength batch
  · rw [outputLookup_of_pre hp hb hh hr hcol hk, ite_eq_left hr]
    rfl
  · rw [outputTailLookup_of_pre hp hb (Nat.le_of_not_lt hr), ite_eq_right hr]
    rfl

/-- Concrete coordinates outside a 32 × 128 subbox, or beyond one four-byte FP32 element,
do not denote a write effect. The other coordinates use the packed output address. -/
theorem writebackWriteLoc {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile : Nat} (stage : Fin 2) (subbox : Fin 4) (x y k : Nat)
    (hb : batch < p.batch) (hh : head < p.heads) :
    let row := stageRow tile stage + y
    let col := 32 * subbox.val + x
    TensorStore.writeLoc (writebackStoreSpec p l g batch head tile stage subbox) x y k =
      if x < 32 ∧ y < 128 ∧ k < 4 ∧ row < p.qLength batch then
        some ((p.oLoc (p.qOffset batch + row) head col).at k)
      else none := by
  dsimp only
  let target (slot : TensorTransfer.Slot p.oMap) : Option Loc :=
    TensorStore.destination (writebackStoreSpec p l g batch head tile stage subbox) slot
  change (TensorTransfer.slotAt p.oMap x y k).bind target = _
  by_cases h : x < 32 ∧ y < 128 ∧ k < 4
  · obtain ⟨hx, hy, hk⟩ := h
    have hcx : x < TensorTile.count p.oMap.box 0 := (outputBoxWidthShared p).symm ▸ hx
    have hry : y < TensorTile.rows p.oMap.box := (outputBoxRowsShared p).symm ▸ hy
    let slot : TensorTransfer.Slot p.oMap := ⟨⟨x, hcx⟩, ⟨y, hry⟩, ⟨k, hk⟩⟩
    have hSlot : TensorTransfer.slotAt p.oMap x y k = some slot := by
      unfold TensorTransfer.slotAt
      have hck : k < p.oMap.format.bytes := hk
      rw [dite_eq_left hcx, dite_eq_left hry, dite_eq_left hck]
    rw [hSlot, Option.bind_some]
    simp only [hx, hy, hk, true_and]
    exact writebackSlotDestination hp stage subbox (g := g) (tile := tile) slot hb hh
  · have hSlot : TensorTransfer.slotAt p.oMap x y k = none := by
      unfold TensorTransfer.slotAt
      split
      · split
        · split
          · rename_i hcx hry hck
            exact (h ⟨outputBoxWidthShared p ▸ hcx, outputBoxRowsShared p ▸ hry, hck⟩).elim
          · rfl
        · rfl
      · rfl
    rw [hSlot, Option.bind_none]
    rw [ite_eq_right (fun hw => h ⟨hw.1, hw.2.1, hw.2.2.1⟩)]

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
