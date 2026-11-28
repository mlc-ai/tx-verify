-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.MmaIssue
public import Kernels.InklingRelDecode.Proof.Lib.B128
public import Kernels.InklingRelDecode.Proof.Lib.QTile
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord

@[expose] public section

/-! # Where a QK MMA reads the query tile against where the prologue stored it

The A operand of step `j` reads element `(row, kk)` at the swizzle of `start + 128 row +
32 (j % 4) + 2 kk + z` of the tile; the prologue lane `t` stores its word `w` of the store `i` at
`2048 (4 (i % 2) + i / 2) + swz t + 4 w`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- **The address of a byte of a QK MMA's A operand** (K-major, 128-byte swizzle). -/
theorem qk_a_addr {s : TcMma.OperandSpec} {st rw kk byte : Nat} (hD : s.descriptor = qkDesc)
    (haT : s.aTmem = none) (hs : s.a = ⟨st, 0, 1024, 0, false, false, .b128⟩) (hr : rw < 64)
    (hk : kk < 16) (hb : byte < 2) :
    s.byteLoc .a (2 * (rw * 16 + kk) + byte) = some ⟨.shared, s.lowCta,
      TensorSwizzle.offset .b128 0 (st + (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte)⟩ := by
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
    TcMma.Kind.k, TcMma.Kind.width, hs, haT]
  simp [hv]
  have e1 : (2 * (rw * 16 + kk) + byte) / 32 = rw := by omega
  have e2 : (2 * (rw * 16 + kk) + byte) / 2 % 16 = kk := by omega
  have e3 : byte % 2 = byte := by omega
  have e4 : rw % 64 = rw := by omega
  simp only [e1, e2, e3, e4]
  refine ⟨hr, ?_⟩
  unfold TcShared.byteAddress
  simp [hr, hb, TcShared.linear, TcShared.Swizzle.sectors, TcShared.Swizzle.offset]

theorem b128_eq (base v : Nat) : TensorSwizzle.offset .b128 base v =
    128 * (v / 128) + 16 * ((v / 16 % 8) ^^^ ((base / 128 + v / 128) % 8)) + v % 16 := by
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask,
    TensorSwizzle.sectors, BitVec.toNat_xor, BitVec.toNat_ofNat]
  simp

theorem qSwz_eq : ∀ t < 128, qSwz t = 128 * (t / 8) + 16 * ((t % 8) ^^^ (t / 8 % 8)) := by
  decide +kernel

theorem xor_lt : ∀ a < 8, ∀ b < 8, (a ^^^ b) < 8 := by decide

theorem xor_cancel : ∀ a < 8, ∀ b < 8, ∀ c < 8, (a ^^^ c) = (b ^^^ c) → a = b := by decide

/-- **The prologue store of a byte of the A operand**: the thread, store and word of the store
whose location is the byte's. -/
theorem qk_a_geom {sb j rw kk byte t i w b : Nat} (hsb : sb % 1024 = 0) (hj : j < 8)
    (hrw : rw < 64) (hkk : kk < 16) (hb : byte < 2) (ht : t < 128) (hi : i < 8) (hw : w < 4)
    (hb' : b < 4)
    (h : TensorSwizzle.offset .b128 0 (((sb + 196608) / 16 + (2 * (j % 4) + 512 * (j / 4))) * 16 +
      (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte) =
      sb + qSwz t + (196608 + 2048 * qGroup i) + 4 * w + b) :
    i = 2 * (rw / 16) + j / 4 ∧ t = 8 * (rw % 16) + (2 * (j % 4) + kk / 8) ∧
      w = kk % 8 / 2 ∧ b = 2 * (kk % 2) + byte := by
  obtain ⟨u, hu⟩ : ∃ u, sb + 196608 = 1024 * u := ⟨(sb + 196608) / 1024, by omega⟩
  have mma : ((sb + 196608) / 16 + (2 * (j % 4) + 512 * (j / 4))) * 16 +
      (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte =
      (128 * rw + 32 * (j % 4) + 2 * kk + byte) + 1024 * (u + 8 * (j / 4)) := by omega
  rw [mma, b128_shift, b128_eq, Nat.zero_add] at h
  have e1 : (128 * rw + 32 * (j % 4) + 2 * kk + byte) / 128 = rw := by omega
  have e2 : (128 * rw + 32 * (j % 4) + 2 * kk + byte) / 16 % 8 = 2 * (j % 4) + kk / 8 := by
    omega
  have e3 : (1024 * (u + 8 * (j / 4))) / 128 = 8 * (u + 8 * (j / 4)) := by omega
  have e4 : (8 * (u + 8 * (j / 4)) + rw) % 8 = rw % 8 := by omega
  rw [e1, e3, e4, e2] at h
  rw [qSwz_eq t ht] at h
  have x1 := xor_lt (2 * (j % 4) + kk / 8) (by omega) (rw % 8) (by omega)
  have x2 := xor_lt (t % 8) (by omega) (t / 8 % 8) (by omega)
  have g1 := qGroup_lt i hi
  have hg : qGroup i = i % 2 * 4 + i / 2 := rfl
  have step : (2 * (j % 4) + kk / 8) ^^^ (rw % 8) = (t % 8) ^^^ (t / 8 % 8) ∧
      8 * (rw / 8) + rw % 8 = rw ∧ t / 8 = rw % 16 := by
    refine ⟨by omega, by omega, by omega⟩
  obtain ⟨hx, -, ht8⟩ := step
  have : t / 8 % 8 = rw % 8 := by omega
  rw [this] at hx
  have := xor_cancel _ (by omega) _ (by omega) _ (by omega) hx.symm
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The element the lane's store holds**: half `n` of a lane at the tile position of the
element `(row, 16 j + kk)`. -/
theorem qElem_pos {Q : Params} {L : Launch} {g j row kk : Nat} (hj : j < 8) (hrow : row < 64)
    (hkk : kk < 16) (ht : g % L.block = 8 * (row % 16) + (2 * (j % 4) + kk / 8)) :
    qElem Q L g (8 * (2 * (row / 16) + j / 4) + 2 * (kk % 8 / 2) + kk % 2) =
      qMat Q L (g / L.block) row (16 * j + kk) := by
  unfold qElem
  generalize g % L.block = t at ht ⊢
  have hn : (8 * (2 * (row / 16) + j / 4) + 2 * (kk % 8 / 2) + kk % 2) / 16 = row / 16 := by
    rcases (by omega : j / 4 = 0 ∨ j / 4 = 1) with h | h <;> rw [h] <;> omega
  have ht8 : t / 8 = row % 16 := by omega
  congr 1
  · unfold qTileRow
    rw [hn, ht8]
    omega
  · unfold qDim
    omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
