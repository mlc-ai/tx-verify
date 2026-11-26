-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.QueryTile
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Lemmas.Tensor.TensorSwizzle

@[expose] public section

/-! # The geometry of the key tile a QK MMA reads and the dequantizer writes

B byte `32 col + 2 t + z` of QK MMA `k` (column `col < 128`, element `t < 16`, byte `z < 2`) is
the swizzled linear byte of token `col % 64`, feature `128 (k / 4) + 64 (col / 64) + 16 (k % 4) +
t` of the tile at `B` (`qk_b_loc`, the layout of the query copy's source). The swizzled byte of
token `y`, feature chunk `c` and byte `w` of a 16-byte chunk of feature block `s` is the byte `w` of
the chunk `dqChunk (8 (y % 16) + c) (y / 16) s` of the dequantizer's lane `8 (y % 16) + c`
(`dq_swz`, `qk_b_addr`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
open PTX MmaFoot

/-- **The location of a QK MMA's B byte.** -/
theorem qk_b_loc {s : TcMma.OperandSpec} (hD : s.descriptor = qkD) {B k col t z : Nat}
    (hs : s.b = keyDesc B k) (hc : col < 128) (ht : t < 16) (hz : z < 2) :
    s.byteLoc .b (32 * col + 2 * t + z) =
      some ⟨.shared, s.lowCta, TensorSwizzle.offset .b128 0
        (linear B (col % 64) (feature k col t) z)⟩ := by
  have hv := qkD_valid
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at hv ⊢
  have h1 : (32 * col + 2 * t + z) / 32 = col := by omega
  simp [hv, h1, TcShared.byteAddress, TcShared.linear, TcShared.Swizzle.sectors, keyDesc,
    linear, feature, qkDelta, TcShared.Swizzle.offset]
  refine ⟨hc, ?_⟩
  have h2 : (32 * col + 2 * t + z) % 2 ≤ 1 := by omega
  simp only [h2, hc, ↓reduceIte, Option.bind_some]
  congr 3
  omega

/-- **The swizzled byte of a dequantizer chunk** (a tile at `Bt`, a multiple of 1024). -/
theorem dq_swz {Bt y s c w : Nat} (hB : Bt % 1024 = 0) (hc : c < 8)
    (hw : w < 16) :
    TensorSwizzle.offset .b128 0 (Bt + 128 * y + 8192 * s + 16 * c + w) =
      Bt + MemRow.dqChunk (8 * (y % 16) + c) (y / 16) s + w := by
  have h1 : (Bt + 128 * y + 8192 * s + 16 * c + w) / 128 % 8 = y % 8 := by omega
  have h2 : (Bt + 128 * y + 8192 * s + 16 * c + w) / 16 % 8 = c := by omega
  have h3 : (Bt + 128 * y + 8192 * s + 16 * c + w) / 128 = Bt / 128 + y + 64 * s := by omega
  have h4 : (Bt + 128 * y + 8192 * s + 16 * c + w) % 16 = w := by omega
  have hch : (TensorSwizzle.chunk .b128 0 ((Bt + 128 * y + 8192 * s + 16 * c + w) / 128)
      (BitVec.ofNat 3 ((Bt + 128 * y + 8192 * s + 16 * c + w) / 16))).toNat = c ^^^ y % 8 := by
    simp only [TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors, BitVec.toNat_xor,
      BitVec.toNat_ofNat, Nat.zero_div, Nat.zero_add]
    rw [show (2 : Nat) ^ 3 = 8 from rfl, h2, h1, Nat.mod_mod]
  have hi8 : (8 * (y % 16) + c) / 8 % 8 = y % 8 := by omega
  have hi64 : (8 * (y % 16) + c) / 64 % 2 = y % 16 / 8 := by omega
  have hi1 : (8 * (y % 16) + c) % 8 = c := by omega
  have hxor : (y % 8 ^^^ c) = c ^^^ y % 8 := Nat.xor_comm _ _
  unfold TensorSwizzle.offset
  rw [hch, h3, h4]
  simp only [MemRow.dqChunk, MemRow.dqCol, hi8, hi64, hi1, hxor]
  omega

/-- **A QK MMA's B byte is a byte of a dequantizer chunk**: the byte `2 e + z` of the chunk
`(r, s)` of lane `8 (col % 16) + c`, with `r = (col % 64) / 16`, `s = F / 64`, `c = F % 64 / 8`,
`e = F % 8`, `F` the feature. -/
theorem qk_b_addr {Bt k col t z : Nat} (hB : Bt % 1024 = 0) (hz : z < 2) :
    TensorSwizzle.offset .b128 0 (linear Bt (col % 64) (feature k col t) z) =
      Bt + MemRow.dqChunk (8 * (col % 64 % 16) + feature k col t % 64 / 8) (col % 64 / 16)
        (feature k col t / 64) + (2 * (feature k col t % 8) + z) := by
  have h := dq_swz (Bt := Bt) (y := col % 64) (s := feature k col t / 64)
    (c := feature k col t % 64 / 8) (w := 2 * (feature k col t % 8) + z) hB
    (by omega) (by omega)
  rw [← h]
  congr 1
  simp only [linear, feature]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
