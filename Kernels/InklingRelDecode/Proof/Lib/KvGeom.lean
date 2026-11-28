-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.KvFoot
public import Kernels.InklingRelDecode.Proof.Lib.B128
public import Kernels.InklingRelDecode.Proof.Lib.MmaIssue

@[expose] public section

/-! # Where the copy of a block lands against where an MMA reads

The copy of a K or V box writes element `(x, y)` at `dst + offset dst (128 y + 2 x + z)`; the QK
MMA reads element `(row, kk)` of step `j` at the swizzle of `start + 128 row + 32 (j % 4) +
2 kk + z` with the start of the K tile of its slot and half `j / 4`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

/-- **The location a K/V copy writes**. -/
theorem kv_loc (Q : Params) (cta col row dst : Nat) (bar : Loc) {x y z : Nat} (hx : x < 64)
    (hy : y < 64) (hz : z < 2) :
    TensorCopy.writeLoc (kvCopySpec Q cta col row dst bar) x y z =
      some ⟨.shared, cta, dst + TensorSwizzle.offset .b128 dst (128 * y + 2 * x + z)⟩ :=
  box_writeLoc2 (R := 64)
    (by simp [kvCopySpec, mapKv, TensorTile.count, TensorTile.step])
    (by simp [kvCopySpec, mapKv, TensorTile.rows, TensorTile.rowsOf, TensorTile.count,
      TensorTile.step])
    (by simp [kvCopySpec, mapKv, TensorDescriptor.Format.bytes]) rfl hx hy hz

/-- **A byte of a QK MMA's B operand written by a copy**: the copy's box and the byte's place in it
are those of the key row and column. -/
theorem qk_b_geom {Q : Params} {bar : Loc} {cta col row sb σ j rw kk byte isV h hh x y z : Nat}
    (hsb : sb % 1024 = 0) (hj : j < 8) (hrw : rw < 128) (hkk : kk < 16)
    (hb : byte < 2) (hV : isV ≤ 1) (hH : h ≤ 1) (hhh : hh ≤ 1) (hx : x < 64) (hy : y < 64)
    (hz : z < 2)
    (hw : TensorCopy.writeLoc (kvCopySpec Q cta col row
      (sb + 32768 * σ + 16384 * hh + 98304 * isV + 8192 * h) bar) x y z =
      some ⟨.shared, cta, TensorSwizzle.offset .b128 0 (sb + 32768 * σ + 32 * (j % 4) +
        16384 * (j / 4) + (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte)⟩) :
    isV = 0 ∧ hh = j / 4 ∧ h = rw / 64 ∧ y = rw % 64 ∧ x = 16 * (j % 4) + kk ∧ z = byte := by
  rw [kv_loc Q cta col row _ bar hx hy hz] at hw
  have addr := Loc.mk.inj (Option.some.inj hw)
  obtain ⟨-, -, addr⟩ := addr
  obtain ⟨t, ht⟩ : ∃ t, sb + 32768 * σ + 16384 * (j / 4) = 1024 * t := ⟨(sb + 32768 * σ +
    16384 * (j / 4)) / 1024, by omega⟩
  have mma : sb + 32768 * σ + 32 * (j % 4) + 16384 * (j / 4) +
      (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte =
      (128 * rw + (32 * (j % 4) + 2 * kk + byte)) + 1024 * t := by omega
  rw [mma, b128_shift, Nat.zero_add] at addr
  have r1 := b128_range (1024 * t) (128 * rw + (32 * (j % 4) + 2 * kk + byte))
  have r2 := b128_range (sb + 32768 * σ + 16384 * hh + 98304 * isV + 8192 * h)
    (128 * y + 2 * x + z)
  have hrow : 128 * ((128 * rw + (32 * (j % 4) + 2 * kk + byte)) / 128) = 128 * rw := by omega
  have hrow2 : 128 * ((128 * y + 2 * x + z) / 128) = 128 * y := by omega
  rw [hrow] at r1
  rw [hrow2] at r2
  have pin : isV = 0 ∧ hh = j / 4 ∧ h = rw / 64 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := pin
  have shift := b128_shift (1024 * t) (128 * (rw % 64) + (32 * (j % 4) + 2 * kk + byte))
    (8 * (rw / 64))
  rw [show 128 * (rw % 64) + (32 * (j % 4) + 2 * kk + byte) + 1024 * (8 * (rw / 64)) =
    128 * rw + (32 * (j % 4) + 2 * kk + byte) by omega,
    show 1024 * t + 1024 * (8 * (rw / 64)) = sb + 32768 * σ + 16384 * (j / 4) + 98304 * 0 +
    8192 * (rw / 64) by omega] at shift
  rw [shift] at addr
  have inj := b128_inj _ (show TensorSwizzle.offset .b128
      (sb + 32768 * σ + 16384 * (j / 4) + 98304 * 0 + 8192 * (rw / 64)) (128 * y + 2 * x + z) =
      TensorSwizzle.offset .b128
      (sb + 32768 * σ + 16384 * (j / 4) + 98304 * 0 + 8192 * (rw / 64))
      (128 * (rw % 64) + (32 * (j % 4) + 2 * kk + byte)) by omega)
  omega

/-- **The address of a byte of a QK MMA's B operand** (K-major, 128-byte swizzle). -/
theorem qk_b_addr {s : TcMma.OperandSpec} {st rw kk byte : Nat} (hD : s.descriptor = qkDesc)
    (hs : s.b = ⟨st, 0, 1024, 0, false, false, .b128⟩) (hr : rw < 128) (hk : kk < 16)
    (hb : byte < 2) :
    ∃ cta, s.byteLoc .b (2 * (rw * 16 + kk) + byte) = some ⟨.shared, cta,
      TensorSwizzle.offset .b128 0 (st + (128 * (rw % 8) + 1024 * (rw / 8) + 2 * kk) + byte)⟩ := by
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
    TcMma.Kind.k, TcMma.Kind.width, hs]
  simp [hv]
  have e1 : (2 * (rw * 16 + kk) + byte) / 32 = rw := by omega
  have e2 : (2 * (rw * 16 + kk) + byte) / 2 % 16 = kk := by omega
  have e3 : byte % 2 = byte := by omega
  have e4 : rw % 128 = rw := by omega
  simp only [e1, e2, e3, e4]
  refine ⟨hr, s.lowCta, ?_⟩
  unfold TcShared.byteAddress
  simp [hr, hb, TcShared.linear, TcShared.Swizzle.sectors, TcShared.Swizzle.offset]

/-- **The address of a byte of a PV MMA's B operand** (MN-major, 128-byte swizzle): the V column
`rw` is the byte `2 (rw % 64)` of the 128-byte row of the token `kk`, in the half `rw / 64`. -/
theorem pv_b_addr {s : TcMma.OperandSpec} {st rw kk byte : Nat} (hD : s.descriptor = pvDesc)
    (hs : s.b = ⟨st, 16384, 1024, 0, false, false, .b128⟩) (hr : rw < 128) (hk : kk < 16)
    (hb : byte < 2) :
    ∃ cta, s.byteLoc .b (2 * (rw * 16 + kk) + byte) = some ⟨.shared, cta,
      TensorSwizzle.offset .b128 0 (st + (2 * (rw % 64) + 16384 * (rw / 64) + 128 * kk) +
        byte)⟩ := by
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  unfold TcMma.OperandSpec.byteLoc
  simp only [hD, pvDesc, TcMma.Operand.extent, TcMma.Operand.major, CtaGroup.size,
    TcMma.Kind.k, TcMma.Kind.width, hs]
  simp [hv]
  have e1 : (2 * (rw * 16 + kk) + byte) / 32 = rw := by omega
  have e2 : (2 * (rw * 16 + kk) + byte) / 2 % 16 = kk := by omega
  have e3 : byte % 2 = byte := by omega
  have e4 : rw % 128 = rw := by omega
  simp only [e1, e2, e3, e4]
  refine ⟨hr, s.lowCta, ?_⟩
  unfold TcShared.byteAddress
  simp [hr, hb, TcShared.linear, TcShared.Swizzle.sectors, TcShared.Swizzle.offset]
  congr 1
  omega

/-- **A byte of a PV MMA's B operand written by a copy**: the V box of the token's slab half, at
the token's row and the column's place. -/
theorem pv_b_geom {Q : Params} {bar : Loc} {cta col row sb σ j rw kk byte isV h hh x y z : Nat}
    (hsb : sb % 1024 = 0) (hj : j < 8) (hrw : rw < 128) (hkk : kk < 16)
    (hb : byte < 2) (hV : isV ≤ 1) (hH : h ≤ 1) (hhh : hh ≤ 1) (hx : x < 64) (hy : y < 64)
    (hz : z < 2)
    (hw : TensorCopy.writeLoc (kvCopySpec Q cta col row
      (sb + 32768 * σ + 16384 * hh + 98304 * isV + 8192 * h) bar) x y z =
      some ⟨.shared, cta, TensorSwizzle.offset .b128 0 (sb + 98304 + 32768 * σ + 2048 * j +
        (2 * (rw % 64) + 16384 * (rw / 64) + 128 * kk) + byte)⟩) :
    isV = 1 ∧ hh = rw / 64 ∧ h = j / 4 ∧ y = 16 * (j % 4) + kk ∧ x = rw % 64 ∧ z = byte := by
  rw [kv_loc Q cta col row _ bar hx hy hz] at hw
  obtain ⟨-, -, addr⟩ := Loc.mk.inj (Option.some.inj hw)
  obtain ⟨t, ht⟩ : ∃ t, sb + 98304 + 32768 * σ + 16384 * (rw / 64) = 1024 * t :=
    ⟨(sb + 98304 + 32768 * σ + 16384 * (rw / 64)) / 1024, by omega⟩
  have mma : sb + 98304 + 32768 * σ + 2048 * j + (2 * (rw % 64) + 16384 * (rw / 64) + 128 * kk) +
      byte = (128 * (16 * j + kk) + (2 * (rw % 64) + byte)) + 1024 * t := by omega
  rw [mma, b128_shift, Nat.zero_add] at addr
  have r1 := b128_range (1024 * t) (128 * (16 * j + kk) + (2 * (rw % 64) + byte))
  have r2 := b128_range (sb + 32768 * σ + 16384 * hh + 98304 * isV + 8192 * h)
    (128 * y + 2 * x + z)
  have hrow : 128 * ((128 * (16 * j + kk) + (2 * (rw % 64) + byte)) / 128) =
      128 * (16 * j + kk) := by omega
  have hrow2 : 128 * ((128 * y + 2 * x + z) / 128) = 128 * y := by omega
  rw [hrow] at r1
  rw [hrow2] at r2
  have pin : isV = 1 ∧ hh = rw / 64 ∧ h = j / 4 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := pin
  have shift := b128_shift (1024 * t) (128 * (16 * (j % 4) + kk) + (2 * (rw % 64) + byte))
    (8 * (j / 4))
  rw [show 128 * (16 * (j % 4) + kk) + (2 * (rw % 64) + byte) + 1024 * (8 * (j / 4)) =
    128 * (16 * j + kk) + (2 * (rw % 64) + byte) by omega,
    show 1024 * t + 1024 * (8 * (j / 4)) = sb + 32768 * σ + 16384 * (rw / 64) + 98304 * 1 +
    8192 * (j / 4) by omega] at shift
  rw [shift] at addr
  have inj := b128_inj _ (show TensorSwizzle.offset .b128
      (sb + 32768 * σ + 16384 * (rw / 64) + 98304 * 1 + 8192 * (j / 4)) (128 * y + 2 * x + z) =
      TensorSwizzle.offset .b128
      (sb + 32768 * σ + 16384 * (rw / 64) + 98304 * 1 + 8192 * (j / 4))
      (128 * (16 * (j % 4) + kk) + (2 * (rw % 64) + byte)) by omega)
  omega
