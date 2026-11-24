-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.MatrixLoad

@[expose] public section
namespace FlashKda.Packed.ProjectionAddress
open PTX

def stateOffset (tid : BitVec 32) : BitVec 32 :=
  let warp := tid >>> 5
  let low := (tid <<< 3) &&& 56
  let high := (tid <<< 2) &&& 64
  let key := (tid <<< 7) &&& 1024
  ((warp <<< 8) + ((low ||| high) ||| key)) <<< 1

def coefficientOffset (tid : BitVec 32) := (tid <<< 4) &&& 496

def element (rows row col : Nat) := 16*rows*(col/8) + 16*row + 2*(col%8)

theorem state_base : ∀ tid : Fin 128, (stateOffset (BitVec.ofNat 32 tid.val)).toNat =
    512*(tid.val/32) + 16*(tid.val%8) + 128*(tid.val%32/16) + 2048*(tid.val/8%2) := by
  decide +kernel

theorem coefficient_base : ∀ tid : Fin 128, (coefficientOffset (BitVec.ofNat 32 tid.val)).toNat =
    16*(tid.val%32) := by decide +kernel

theorem a_address (base step : Nat) (tid : Fin 128) (x : Fin 16) :
    let lane := tid.val%32
    let row := lane%16
    let key := 16*step + 8*(lane/16) + x.val/2
    base + 512*step + (coefficientOffset (BitVec.ofNat 32 tid.val)).toNat + x.val =
      base + element 16 row key + x.val%2 := by
  dsimp only
  rw [coefficient_base]
  unfold element
  omega

theorem b_address (base step : Nat) (tid : Fin 128) (side : Fin 2) (x : Fin 16) :
    let lane := tid.val%32
    let v := 32*(tid.val/32) + 16*side.val + 8*(lane/16) + lane%8
    let key := 16*step + 8*(lane/8%2) + x.val/2
    base + (stateOffset (BitVec.ofNat 32 tid.val)).toNat + 4096*step + 256*side.val + x.val =
      base + element 128 v key + x.val%2 := by
  dsimp only
  rw [state_base]
  unfold element
  omega

theorem coefficients (m : Nat → Option Byte) (a : Matrix.Tile) (base step : Nat)
    (stored : ∀ row < 16, ∀ k < 128, ∀ b < 2, m (base + element 16 row k + b) =
      some ((Value.float .bf16 (a row k)).byteAt b))
    (tid : Fin 128) (x : Fin 16) (live : step < 8) :
    m (base + 512*step + (coefficientOffset (BitVec.ofNat 32 tid.val)).toNat + x.val) =
      MatrixLoad.aByte (fun row k => a row (16*step+k)) (tid.val%32) x.val := by
  rw [a_address, stored _ (by omega) _ (by omega) _ (by omega)]
  unfold MatrixLoad.aByte
  simp [Nat.add_assoc]

theorem state (m : Nat → Option Byte) (s : Matrix.Tile) (base step : Nat) (side : Fin 2)
    (stored : ∀ v < 128, ∀ k < 128, ∀ b < 2, m (base + element 128 v k + b) =
      some ((Value.float .bf16 (s k v)).byteAt b))
    (tid : Fin 128) (x : Fin 16) (live : step < 8) :
    m (base + (stateOffset (BitVec.ofNat 32 tid.val)).toNat + 4096*step + 256*side.val + x.val) =
      MatrixLoad.bByte (fun k j => s (16*step+k) (32*(tid.val/32)+16*side.val+j))
        (tid.val%32) x.val := by
  rw [b_address, stored _ (by omega) _ (by omega) _ (by omega)]
  unfold MatrixLoad.bByte
  simp [Nat.add_assoc]

end FlashKda.Packed.ProjectionAddress
