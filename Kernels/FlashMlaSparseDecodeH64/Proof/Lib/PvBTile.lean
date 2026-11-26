-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.DqTile

@[expose] public section

/-! # The geometry of the value tile a PV MMA reads

B byte `32 col + 2 kk + z` of PV MMA `k'` (column `col < 256`, element `kk < 16`, byte `z < 2`) is
the swizzled linear byte of token `16 (k' / 2) + kk`, feature `256 (k' % 2) + col` of the tile at
`B` (`pv_b_loc`: MN-major, 128-byte swizzle, leading offset 8192, stride 1024, start
`B + 2048 (k' / 2) + 32768 (k' % 2)`: the layout of the key tile read the other way). Its place in
the dequantizer's chunks is `pv_b_addr`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
open PTX MmaFoot

/-- **The location of a PV MMA's B byte.** -/
theorem pv_b_loc {s : TcMma.OperandSpec} (hD : s.descriptor = pvD) {B k col kk z : Nat}
    (hs : s.b = valueDesc B k) (hc : col < 256) (hkk : kk < 16) (hz : z < 2) :
    s.byteLoc .b (32 * col + 2 * kk + z) =
      some ⟨.shared, s.lowCta, TensorSwizzle.offset .b128 0
        (linear B (16 * (k / 2) + kk) (256 * (k % 2) + col) z)⟩ := by
  have hv := pvD_valid
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvD, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size, hs,
    TcMma.Kind.k, TcMma.Kind.width] at hv ⊢
  have h1 : (32 * col + 2 * kk + z) / 32 = col := by omega
  simp [hv, h1, TcShared.byteAddress, TcShared.linear, TcShared.Swizzle.sectors, valueDesc,
    linear, pvDelta, TcShared.Swizzle.offset]
  refine ⟨hc, ?_⟩
  have h2 : (32 * col + 2 * kk + z) % 2 ≤ 1 := by omega
  simp only [h2, hc, ↓reduceIte, Option.bind_some]
  congr 3
  omega

/-- **A PV MMA's B byte is a byte of a dequantizer chunk**: the byte `2 (F % 8) + z` of the chunk
`(ks, F / 64)` of lane `8 kk + F % 64 / 8`, `ks = k' / 2`, `F = 256 (k' % 2) + col` the feature. -/
theorem pv_b_addr {Bt k col kk z : Nat} (hB : Bt % 1024 = 0) (hkk : kk < 16) (hz : z < 2) :
    TensorSwizzle.offset .b128 0 (linear Bt (16 * (k / 2) + kk) (256 * (k % 2) + col) z) =
      Bt + MemRow.dqChunk (8 * kk + (256 * (k % 2) + col) % 64 / 8) (k / 2)
        ((256 * (k % 2) + col) / 64) + (2 * ((256 * (k % 2) + col) % 8) + z) := by
  have h := dq_swz (Bt := Bt) (y := 16 * (k / 2) + kk) (s := (256 * (k % 2) + col) / 64)
    (c := (256 * (k % 2) + col) % 64 / 8) (w := 2 * ((256 * (k % 2) + col) % 8) + z) hB
    (by omega) (by omega)
  rw [show 8 * ((16 * (k / 2) + kk) % 16) + (256 * (k % 2) + col) % 64 / 8 =
    8 * kk + (256 * (k % 2) + col) % 64 / 8 by omega,
    show (16 * (k / 2) + kk) / 16 = k / 2 by omega] at h
  rw [← h]
  congr 1
  simp only [linear]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QueryTile
