-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.TensorMaps
public import Core.Async.Tensor.TensorCopy

@[expose] public section

/-! # The shared source bytes of an output tile store

An output store's box is the O map's (`mapO`: 64 two-byte columns by 64 rows, 128-byte swizzle).
From a 1024-byte aligned shared base, the slot of column `x`, row `h` and byte `byte` reads the
byte at `128 h + 16 ((x / 8) ^^^ h % 8) + 2 (x % 8) + byte` (`outBox_sharedLoc`), which is byte
`b` of the 4-byte element `el` of the 16-byte chunk `k` of row `h` (`k = x / 8`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- The 128-byte swizzle at a 1024-byte aligned base, within a 128-byte row `h`. -/
theorem swizzle128_row {base h x byte : Nat} (hbase : base % 1024 = 0) (hx : x < 64)
    (hb : byte < 2) :
    TensorSwizzle.offset .b128 base (h * 128 + x * 2 + byte) =
      128 * h + 16 * ((x / 8) ^^^ (h % 8)) + 2 * (x % 8) + byte := by
  have hrow : (h * 128 + x * 2 + byte) / 128 = h := by omega
  have hchunk : (h * 128 + x * 2 + byte) / 16 % 8 = x / 8 := by omega
  have hmask : (base / 128 + h) % 8 = h % 8 := by omega
  have hbyte : (h * 128 + x * 2 + byte) % 16 = 2 * (x % 8) + byte := by omega
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, BitVec.toNat_xor, hrow, BitVec.toNat_ofNat, hchunk, hmask,
    Nat.mod_mod, hbyte]
  omega

/-- **The source byte of an output store's slot**: a tensor box whose descriptor is an O map
at a 1024-byte aligned base reads byte `b` of element `el` of chunk `k ^^^ h % 8` of row `h`. -/
theorem outBox_sharedLoc {b : TensorBox} {base sH sS sB sq bt : Nat} {fill : Fill}
    {cls : AllocationClass}
    (hd : (⟨b.outer, b.descriptor⟩ : Σ n, Descriptor n) =
      ⟨3, mapO base sH sS sB sq bt fill cls⟩)
    (hal : b.sharedBase.addr % 1024 = 0) (slot : TensorTransfer.Slot b.descriptor) :
    ∃ h < 64, ∃ k < 8, ∃ el < 4, ∃ y < 4, b.sharedLoc slot =
      { b.sharedBase with
        addr := b.sharedBase.addr + (128 * h + 16 * (k ^^^ h % 8) + 4 * el + y) } := by
  obtain ⟨outer, desc, origin, sb, rows⟩ := b
  simp only [Sigma.mk.injEq] at hd
  obtain ⟨rfl, hd⟩ := hd
  cases hd
  have hc : TensorTile.count (mapO base sH sS sB sq bt fill cls).box 0 = 64 := by
    simp [mapO, encodeTiled, TensorTile.count, TensorTile.step]
  have hr : TensorTile.rows (mapO base sH sS sB sq bt fill cls).box = 64 := by
    simp [mapO, encodeTiled, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step]
  obtain ⟨⟨x, hx⟩, ⟨h, hh⟩, ⟨y, hy⟩⟩ := slot
  rw [hc] at hx
  rw [hr] at hh
  have hy2 : y < 2 := by simpa [mapO, encodeTiled, Format.bytes] using hy
  refine ⟨h, hh, x / 8, by omega, (2 * (x % 8) + y) / 4, by omega, (2 * (x % 8) + y) % 4,
    by omega, ?_⟩
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rowBytes]
  have hp : TensorTile.count (mapO base sH sS sB sq bt fill cls).box 0 *
      (mapO base sH sS sB sq bt fill cls).format.bytes ⊔
        TensorTile.swizzleWidth (mapO base sH sS sB sq bt fill cls).swizzle = 128 := by
    simp [mapO, encodeTiled, TensorTile.count, TensorTile.step, Format.bytes,
      TensorTile.swizzleWidth]
  have hsw : (mapO base sH sS sB sq bt fill cls).swizzle = .b128 := by
    simp [mapO, encodeTiled]
  have hby : (mapO base sH sS sB sq bt fill cls).format.bytes = 2 := by
    simp [mapO, encodeTiled, Format.bytes]
  rw [hp, hsw, hby, swizzle128_row hal hx hy2]
  congr 1
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
