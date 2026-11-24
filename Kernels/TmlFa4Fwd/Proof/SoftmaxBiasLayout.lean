-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasVector

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

/-- Each bias stage has two independently filled 128-by-64 BF16 boxes. -/
def biasBoxStart (l : Launch) (stage : Fin 2) (half : Nat) : Nat :=
  l.sharedBase + 166912 + 32768*stage.val + 16384*half

/-- The byte address of the lane's swizzled 16-byte chunk, before splitting it into words. -/
def biasVectorAddress (l : Launch) (g : Nat) (stage : Fin 2) (i : Fin 16) : Nat :=
  let b := biasBoxStart l stage (i.val/8)
  b + TensorSwizzle.offset .b128 b (128*((g % l.block) % 128)+16*(i.val%8))

/-- The address register excludes a fixed offset encoded directly in the load. -/
def biasVectorBase (l : Launch) (g : Nat) (stage : Fin 2) (repeated : Bool) (i : Fin 16) : Nat :=
  biasVectorAddress l g stage i - (biasReadSite repeated i).offset

private theorem swizzleBiasChunk (base row col : Nat) (hc : col < 8) {byte : Nat} (hb : byte < 16) :
    TensorSwizzle.offset .b128 base (128*row+16*col+byte) =
      TensorSwizzle.offset .b128 base (128*row+16*col)+byte := by
  have hRow : (128*row+16*col+byte)/128 = row := by omega
  have hRow0 : (128*row+16*col)/128 = row := by omega
  have hChunk : (128*row+16*col+byte)/16 = 8*row+col := by omega
  have hChunk0 : (128*row+16*col)/16 = 8*row+col := by omega
  have hByte : (128*row+16*col+byte)%16 = byte := by omega
  have hByte0 : (128*row+16*col)%16 = 0 := by omega
  rw [TensorSwizzle.offset, TensorSwizzle.offset, hRow, hRow0, hChunk, hChunk0, hByte,
    hByte0, Nat.add_zero]

private theorem biasVectorOffset (repeated : Bool) (i : Fin 16) :
    (biasReadSite repeated i).offset ≤ 16384 := by
  cases repeated <;> fin_cases i <;> decide

/-- The decoded vector base and displacement name the full swizzled chunk address. -/
theorem biasVectorBase_add (l : Launch) (g : Nat) (stage : Fin 2) (repeated : Bool) (i : Fin 16) :
    biasVectorBase l g stage repeated i + (biasReadSite repeated i).offset =
      biasVectorAddress l g stage i := by
  have hOff := biasVectorOffset repeated i
  dsimp [biasVectorBase, biasVectorAddress, biasBoxStart]
  omega

/-- Every Bias read is based at or above the start of the Bias storage. -/
theorem biasVectorAddressLower (l : Launch) (g : Nat) (stage : Fin 2) (i : Fin 16) :
    l.sharedBase + 166912 ≤ biasVectorAddress l g stage i := by
  dsimp [biasVectorAddress, biasBoxStart]
  omega

/-- Each swizzled Bias vector is entirely within its allocated shared storage. -/
theorem biasVectorAddressEnd (l : Launch) (g : Nat) (stage : Fin 2) (i : Fin 16) :
    biasVectorAddress l g stage i + 16 ≤ l.sharedBase + 232448 := by
  let row := (g % l.block) % 128
  let addr := 128 * row + 16 * (i.val % 8)
  let base := biasBoxStart l stage (i.val / 8)
  have hRow : row < 128 := Nat.mod_lt _ (by decide)
  have hAddr : addr / 128 = row ∧ addr % 16 = 0 := by dsimp [addr]; omega
  have hChunk := (TensorSwizzle.chunk .b128 base (addr / 128)
    (BitVec.ofNat 3 (addr / 16))).isLt
  have hStage := stage.isLt
  have hVector := i.isLt
  change base + TensorSwizzle.offset .b128 base addr + 16 ≤ _
  unfold TensorSwizzle.offset
  rw [hAddr.1] at hChunk
  rw [hAddr.1, hAddr.2]
  dsimp [base, biasBoxStart]
  omega

/-- Every bias vector address fits a shared-address word and is properly aligned for v4.b32. -/
theorem biasVectorAddressBounds {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) (i : Fin 16) :
    biasVectorAddress l g stage i < 2^32 ∧ biasVectorAddress l g stage i % 16 = 0 := by
  have hShared := hp.shared.2.1
  have hAlign := hp.shared.1
  have hStage := stage.isLt
  have hVector := i.isLt
  let addr := 128*((g % l.block) % 128)+16*(i.val%8)
  let base := biasBoxStart l stage (i.val/8)
  have hRow : addr / 128 = (g % l.block) % 128 := by dsimp [addr]; omega
  have hByte : addr % 16 = 0 := by dsimp [addr]; omega
  have hChunk :=
    (TensorSwizzle.chunk .b128 base (addr/128) (BitVec.ofNat 3 (addr/16))).isLt
  change base+TensorSwizzle.offset .b128 base addr < 2^32 ∧
    (base+TensorSwizzle.offset .b128 base addr)%16 = 0
  unfold TensorSwizzle.offset
  rw [hByte, Nat.add_zero]
  dsimp [base, biasBoxStart] at *
  omega

/-- The element and byte of the producer's selected half-box read by a consumer word. -/
def biasVectorSlot (p : Params) (l : Launch) (g : Nat) (i : Fin 16) (word byte : Fin 4) :
    TensorTransfer.Slot p.biasMap :=
  ⟨⟨8*(i.val%8)+2*word.val+byte.val/2, by
    have hw := word.isLt
    have hb := byte.isLt
    simpa [Params.biasMap, TensorTile.count, TensorTile.step] using
      (show 8*(i.val%8)+2*word.val+byte.val/2 < 64 by omega)⟩,
    ⟨(g % l.block) % 128, by
      simpa [Params.biasMap, TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step]
        using (Nat.mod_lt (g % l.block) (show 0 < 128 by decide))⟩,
    ⟨byte.val%2, by change _ < 2; omega⟩⟩

/-- A byte in the consumer's shared read is exactly the producer box's corresponding TMA
slot, including the two separately swizzled halves and the stage offset. -/
theorem biasVectorMatchesBox (p : Params) (l : Launch) (g : Nat) (stage : Fin 2)
    (repeated : Bool) (i : Fin 16) (word byte : Fin 4)
    (origin : Fin 3 → Int) :
    (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val).loc.at byte.val =
      (⟨2, p.biasMap, origin, ⟨.shared, g/l.block, biasBoxStart l stage (i.val/8)⟩, none⟩ :
        TensorBox).sharedLoc (biasVectorSlot p l g i word byte) := by
  have hw := word.isLt
  have hb := byte.isLt
  have hLinear : (g % l.block) % 128 * 128 +
      (8*(i.val%8)+2*word.val+byte.val/2)*2+byte.val%2 =
      128*((g % l.block) % 128)+16*(i.val%8)+(4*word.val+byte.val) := by omega
  simp only [biasReadAcc, Loc.at, biasVectorBase_add, TensorBox.sharedLoc, TensorTile.sharedByte,
    TensorTile.linearByte, biasVectorSlot]
  have hPitch :
      TensorTile.rowBytes p.biasMap.box p.biasMap.format.bytes p.biasMap.swizzle = 128 := by
    simp [Params.biasMap, TensorTile.rowBytes, TensorTile.count, TensorTile.step,
      TensorTile.swizzleWidth, TensorDescriptor.Format.bytes]
  have hFormat : p.biasMap.format.bytes = 2 := rfl
  have hSwizzle : p.biasMap.swizzle = .b128 := rfl
  rw [hPitch, hFormat, hSwizzle]
  congr 1
  rw [hLinear, swizzleBiasChunk (biasBoxStart l stage (i.val/8)) ((g % l.block) % 128)
    (i.val%8) (by omega) (by omega), biasVectorAddress]
  simp only [Nat.add_assoc]

end PTX.Kernels.TmlFa4Fwd.Softmax
