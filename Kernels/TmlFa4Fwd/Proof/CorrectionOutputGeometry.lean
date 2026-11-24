-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputSlotSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open Epilogue

/-- The base byte of one four-element correction vector store in an output subbox. -/
def outputChunkLoc (l : Launch) (g : Nat) (stage : Fin 2) (subbox : Fin 4)
    (row chunk : Nat) : Loc :=
  (sharedSlot l g stage subbox).at
    (128 * row + 16 * (chunk ^^^ (row % 8)))

/-- Correction's physical vector layout and the absolute TMA swizzle agree byte for byte. -/
theorem outputChunk_swizzle {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (subbox : Fin 4) {row chunk byte : Nat}
    (hChunk : chunk < 8) (hByte : byte < 16) :
    TensorSwizzle.offset .b128 0
        ((sharedSlot l g stage subbox).addr + (128 * row + 16 * chunk + byte)) =
      ((outputChunkLoc l g stage subbox row chunk).at byte).addr := by
  let base := (sharedSlot l g stage subbox).addr
  have hAlign := hp.shared.1
  have hBase : base % 1024 = 0 := by
    change (l.sharedBase + (3072 + 65536 * stage.val + 16384 * subbox.val)) % 1024 = 0
    omega
  have hRow : (128 * row + 16 * chunk + byte) / 128 = row := by omega
  have hChunk' : (128 * row + 16 * chunk + byte) / 16 = 8 * row + chunk := by omega
  have hByte' : (128 * row + 16 * chunk + byte) % 16 = byte := by omega
  change TensorSwizzle.offset .b128 0 (base + (128 * row + 16 * chunk + byte)) = _
  rw [TensorSwizzle.offset_add_base _ _ _ (by omega)]
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask, hRow, hChunk',
    hByte', TensorSwizzle.sectors, outputChunkLoc, Loc.at, BitVec.toNat_xor, BitVec.toNat_ofNat]
  have hPhase : (base / 128 + row) % 8 = row % 8 := by omega
  have hCol : (8 * row + chunk) % 8 = chunk := by omega
  rw [hPhase, hCol, Nat.mod_mod]
  omega

/-- The TMA reader may use any issuer in the CTA. Its byte belongs to the correction vector
for the logical row and the four-element chunk containing the selected column. -/
theorem writebackSlot_correctionChunk {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g writer batch head tile : Nat} (hCta : writer / l.block = g / l.block)
    (stage : Fin 2) (subbox : Fin 4) (slot : TensorTransfer.Slot p.oMap) :
    (writebackStoreSpec p l g batch head tile stage subbox).toTensorBox.sharedLoc slot =
      (outputChunkLoc l writer stage subbox slot.2.1.val (slot.1.val / 4)).at
        ((4 * slot.1.val + slot.2.2.val) % 16) := by
  have hWidth : TensorTile.count p.oMap.box 0 = 32 := by
    simp [TensorTile.count, TensorTile.step, Params.oMap]
  have hx : slot.1.val < 32 := hWidth ▸ slot.1.isLt
  have hk : slot.2.2.val < 4 := slot.2.2.isLt
  let base := (sharedSlot l g stage subbox).addr
  let columnByte := 4 * slot.1.val + slot.2.2.val
  let row := slot.2.1.val
  have hAlign := hp.shared.1
  have hBase : base % 128 = 0 := by
    change (l.sharedBase + (3072 + 65536 * stage.val + 16384 * subbox.val)) % 128 = 0
    omega
  have hAddress := outputChunk_swizzle hp g stage subbox (row := row)
    (chunk := slot.1.val / 4) (byte := columnByte % 16) (by omega) (Nat.mod_lt _ (by decide))
  have hLinear : 128 * row + 16 * (slot.1.val / 4) + columnByte % 16 =
      TensorTile.linearByte p.oMap.box 4 .b128 slot.1.val row slot.2.2.val := by
    have hPitch : TensorTile.rowBytes p.oMap.box 4 .b128 = 128 := by
      simp [TensorTile.rowBytes, hWidth, TensorTile.swizzleWidth]
    simp only [TensorTile.linearByte, hPitch, columnByte]
    omega
  rw [hLinear, TensorSwizzle.offset_add_base _ _ _ hBase] at hAddress
  change (sharedSlot l g stage subbox).at
    (TensorSwizzle.offset .b128 base
      (TensorTile.linearByte p.oMap.box 4 .b128 slot.1.val row slot.2.2.val)) = _
  have hIssuer : sharedSlot l writer stage subbox = sharedSlot l g stage subbox := by
    simp only [sharedSlot, hCta]
  simp only [outputChunkLoc, hIssuer] at hAddress ⊢
  let storage := sharedSlot l g stage subbox
  change Loc.mk storage.space storage.cta (storage.addr + _) =
    Loc.mk storage.space storage.cta ((storage.addr + _) + _)
  exact congrArg (Loc.mk storage.space storage.cta) hAddress

end PTX.Kernels.TmlFa4Fwd.Correction
