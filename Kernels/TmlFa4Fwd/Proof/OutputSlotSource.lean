-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.OutputWriteLoc
public import Lemmas.Tensor.TensorSwizzle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue

open TensorDescriptor

noncomputable section

/-- Swizzling preserves each 128-byte row of the 16 KiB output subbox. -/
theorem writebackSlotSource (p : Params) (l : Launch) (g batch head tile : Nat)
    (stage : Fin 2) (subbox : Fin 4) (slot : TensorTransfer.Slot p.oMap) :
    ∃ offset < 16384,
      (writebackStoreSpec p l g batch head tile stage subbox).toTensorBox.sharedLoc slot =
        (sharedSlot l g stage subbox).at offset := by
  let base := (sharedSlot l g stage subbox).addr
  let linear := TensorTile.linearByte p.oMap.box 4 .b128
    slot.1.val slot.2.1.val slot.2.2.val
  have hPitch : TensorTile.rowBytes p.oMap.box 4 .b128 = 128 := by
    simp [TensorTile.rowBytes, outputBoxWidthShared, TensorTile.swizzleWidth]
  have hx : slot.1.val < 32 := outputBoxWidthShared p ▸ slot.1.isLt
  have hy : slot.2.1.val < 128 := outputBoxRowsShared p ▸ slot.2.1.isLt
  have hk : slot.2.2.val < 4 := slot.2.2.isLt
  have hl : linear < 16384 := by
    dsimp [linear, TensorTile.linearByte]
    rw [hPitch]
    omega
  have hs := TensorSwizzle.offset_row .b128 base linear
  exact ⟨TensorSwizzle.offset .b128 base linear, by omega, rfl⟩

/-- Every possible TMA source byte belongs to the issuer's allocated shared memory. -/
theorem writebackSlotSourceAllocated {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile : Nat} (hcta : g / l.block < l.grid)
    (stage : Fin 2) (subbox : Fin 4) (slot : TensorTransfer.Slot p.oMap) :
    m ((writebackStoreSpec p l g batch head tile stage subbox).toTensorBox.sharedLoc slot) ≠
      none := by
  obtain ⟨offset, ho, hLoc⟩ := writebackSlotSource p l g batch head tile stage subbox slot
  have hs := stage.isLt
  have hb := subbox.isLt
  rw [hLoc]
  have hRange : 3072 + 65536 * stage.val + 16384 * subbox.val + offset < 232448 := by omega
  simpa only [sharedSlot, Loc.at, Nat.add_assoc] using hp.shared.2.2 _ hcta _ hRange

/-- Distinct stage and subbox pairs on a writeback thread have disjoint source footprints. -/
theorem writebackSourcesDisjoint (p : Params) (l : Launch) (g batch head tile : Nat)
    {stage stage' : Fin 2} {subbox subbox' : Fin 4}
    (slot slot' : TensorTransfer.Slot p.oMap)
    (hSame : (writebackStoreSpec p l g batch head tile stage subbox).toTensorBox.sharedLoc slot =
      (writebackStoreSpec p l g batch head tile stage' subbox').toTensorBox.sharedLoc slot') :
    stage = stage' ∧ subbox = subbox' := by
  obtain ⟨a, ha, hA⟩ := writebackSlotSource p l g batch head tile stage subbox slot
  obtain ⟨b, hb, hB⟩ := writebackSlotSource p l g batch head tile stage' subbox' slot'
  rw [hA, hB] at hSame
  have hAddr := congrArg Loc.addr hSame
  simp only [sharedSlot, Loc.at] at hAddr
  have hc := subbox.isLt
  have hd := subbox'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
