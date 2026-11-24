-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorTransfer
public import Mathlib.Tactic

/-! Whole-box checks of the tiled shared layout (THREAD-TENSOR-TILE-SHARED, THREAD-TENSOR-SWIZZLE)
against an independent closed form: the physical address XORs the 16-byte chunk index (address bits
4..6) with the 128-byte pattern-row index (bits 7..9) modulo the swizzle's sector count, as
`run_tma2d.cu` models the B200. -/
namespace PTX.Tests.TensorTileCoverage
open TensorTile
noncomputable section

/-- The probe runner's swizzle for a 1024-byte-aligned buffer at offset `base`. -/
private def swz (sectors base byte : Nat) : Nat :=
  128 * (byte / 128) + 16 * Nat.xor (byte / 16 % 8) ((base / 128 + byte / 128) % sectors) +
    byte % 16

private def box (w h : Nat) : Box 2 := ⟨![w, h], ![1, 1]⟩

-- 128-byte swizzle, 128-byte rows, every destination phase of a 1024-byte block.
example : ∀ base < 8, ∀ r < 8, ∀ i < 128,
    sharedByte (box 128 8) 1 .b128 (128 * base) i r 0 = 128 * base + swz 8 (128 * base) (128 * r +
      i) := by
  decide
-- 64-byte swizzle: two 64-byte rows per 128-byte pattern row.
example : ∀ r < 8, ∀ i < 64,
    sharedByte (box 64 8) 1 .b64 640 i r 0 = 640 + swz 4 640 (64 * r + i) := by decide
-- 32-byte swizzle at an odd phase.
example : ∀ r < 8, ∀ i < 32,
    sharedByte (box 32 8) 1 .b32 128 i r 0 = 128 + swz 2 128 (32 * r + i) := by decide
-- No swizzle: plain row-major with the box's row pitch.
example : ∀ r < 8, ∀ i < 48, sharedByte (box 48 8) 1 .none 256 i r 0 = 256 + 48 * r + i := by
  decide
-- Rows narrower than the swizzle are padded to its width.
example : ∀ r < 8, ∀ i < 32,
    sharedByte (box 32 8) 1 .b128 0 i r 0 = swz 8 0 (128 * r + i) := by decide
-- Two-byte elements: element `i`'s byte `b` is linear byte `2 i + b`.
example : ∀ r < 4, ∀ i < 64, ∀ b < 2,
    sharedByte (box 64 4) 2 .b128 0 i r b = swz 8 0 (128 * r + 2 * i + b) := by decide

/-! ## The swizzle permutes the chunks of each pattern row -/

example : ∀ base < 8, ∀ row < 8, ∀ a < 8, ∀ b < 8,
    (TensorSwizzle.chunk .b128 (128 * base) row (BitVec.ofNat 3 a)).toNat =
      (TensorSwizzle.chunk .b128 (128 * base) row (BitVec.ofNat 3 b)).toNat → a = b := by decide
-- Bytes stay inside their 128-byte pattern row and keep their order within a chunk.
example : ∀ k < 8, ∀ byte < 128,
    TensorSwizzle.offset .b128 384 (128 * k + byte) / 128 = k ∧
    TensorSwizzle.offset .b128 384 (128 * k + byte) % 16 = byte % 16 := by decide
-- The no-swizzle mode is the identity.
example : ∀ k < 8, ∀ byte < 128,
    TensorSwizzle.offset .none 384 (128 * k + byte) = 128 * k + byte := by decide

/-! ## Row pitch -/

example : rowBytes (box 16 2) 1 .b128 = 128 ∧ rowBytes (box 16 2) 1 .none = 16 ∧
    rowBytes (box 64 2) 2 .b64 = 128 ∧ rowBytes (box 32 2) 4 .b32 = 128 := by decide

end
end PTX.Tests.TensorTileCoverage
