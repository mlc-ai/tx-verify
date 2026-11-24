-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.TmemCells
public import Core.Tc.TcMmaOperands
public import Lemmas.Tcgen05.TcSharedAddress
import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The bytes of the MMA operands in shared memory

The A operand of a QK MMA (the Q stage), its B operand (a K slot, K-major) and the B operand of a PV
MMA (a V slot, MN-major): the byte of each operand index, and the 32768-byte region it lies in. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Flow TcMma

noncomputable section

variable {L : Launch}

/-- **The K-major byte of a 128-row operand** at `base + 2 c`. -/
theorem k_byteAddress {base c y k z : Nat} (hb : base % 128 = 0) (hz : z < 2) :
    TcShared.byteAddress 2 .k (kDesc (base + 2 * c)) y k z =
      some (base + TensorSwizzle.offset .b128 base (128 * y + 2 * (c + k) + z)) :=
  TcShared.k128_tma_byte 2 base c 16 y k z hb hz

/-- **The MN-major byte** with 64 columns per 16384-byte tile: column `64 r + y` is in tile `r`. -/
theorem mn_byteAddress {base r y k z : Nat} (hb : base % 128 = 0) (hy : y < 64) (hz : z < 2) :
    TcShared.byteAddress 2 .mn (mnDesc base) (64 * r + y) k z =
      some (base + 16384 * r + TensorSwizzle.offset .b128 (base + 16384 * r)
        (128 * k + 2 * y + z)) := by
  simp only [TcShared.byteAddress, mnDesc, TcShared.linear, TcShared.Swizzle.sectors,
    TcShared.Swizzle.offset]
  simp only [reduceCtorEq, ↓reduceIte, hz, true_and, true_implies, false_implies,
    Nat.reduceEqDiff]
  rw [← TensorSwizzle.offset_add_base _ (base + 16384 * r) _ (by omega)]
  congr 2
  omega

/-- The decomposition of an operand index: row, contraction, byte. -/
theorem index_split {index : Nat} (h : index < 4096) :
    ∃ y k z, y < 128 ∧ k < 16 ∧ z < 2 ∧ index = 32 * y + 2 * k + z :=
  ⟨index / 32, index / 2 % 16, index % 2, by omega, by omega, by omega, by omega⟩

theorem opBytes {s : OperandSpec} {c : Nat} (hs : Spec128 s c) (op : Operand) :
    op.bytes s.descriptor = 4096 := by
  rcases hs.dsc with h | h <;> rw [h] <;> cases op <;> rfl

/-- **The bytes of a QK MMA's A operand**: in the 16384-byte box of its descriptor. -/
theorem qk_a_byteLoc {s : OperandSpec} {c : Nat} (hD : s.descriptor = qkDsc)
    (hl : s.lowCta = c) (haT : s.aTmem = none) {base j : Nat}
    (hs : s.a = kDesc (base + 32 * j)) (hj : j < 4) (hb : base % 128 = 0) {index : Nat}
    (hi : index < 4096) :
    ∃ off, off < 16384 ∧ s.byteLoc .a index = some ⟨.shared, c, base + off⟩ := by
  obtain ⟨y, k, z, hy, hk, hz, rfl⟩ := index_split hi
  refine ⟨TensorSwizzle.offset .b128 base (128 * y + 2 * (16 * j + k) + z),
    TensorCopy.box_offset_lt (R := 128) (by omega) hy hz, ?_⟩
  have haddr := k_byteAddress (base := base) (c := 16 * j) (y := y) (k := k) (z := z) hb hz
  rw [show 2 * (16 * j) = 32 * j by ring] at haddr
  have hdiv : (32 * y + 2 * k + z) / (16 * 2) = y := by omega
  have hkdiv : (32 * y + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * y + 2 * k + z) % 2 = z := by omega
  have hv := qkDsc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, qkDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
    hkdiv, hbmod, hs, haT, hl] at hv ⊢
  simp [hv, hy, Nat.mod_eq_of_lt hy, haddr]

/-- **The bytes of a QK MMA's B operand**. -/
theorem qk_b_byteLoc {s : OperandSpec} {c : Nat} (hD : s.descriptor = qkDsc)
    (hl : s.lowCta = c) {base j : Nat}
    (hs : s.b = kDesc (base + 32 * j)) (hj : j < 4) (hb : base % 128 = 0) {index : Nat}
    (hi : index < 4096) :
    ∃ off, off < 16384 ∧ s.byteLoc .b index = some ⟨.shared, c, base + off⟩ := by
  obtain ⟨y, k, z, hy, hk, hz, rfl⟩ := index_split hi
  refine ⟨TensorSwizzle.offset .b128 base (128 * y + 2 * (16 * j + k) + z),
    TensorCopy.box_offset_lt (R := 128) (by omega) hy hz, ?_⟩
  have haddr := k_byteAddress (base := base) (c := 16 * j) (y := y) (k := k) (z := z) hb hz
  rw [show 2 * (16 * j) = 32 * j by ring] at haddr
  have hdiv : (32 * y + 2 * k + z) / (16 * 2) = y := by omega
  have hkdiv : (32 * y + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * y + 2 * k + z) % 2 = z := by omega
  have hv := qkDsc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, qkDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
    hkdiv, hbmod, hs, hl] at hv ⊢
  simp [hv, hy, Nat.mod_eq_of_lt hy, haddr]

/-- **The bytes of a PV MMA's B operand**: in the 32768 bytes of its V slot. -/
theorem pv_b_byteLoc {s : OperandSpec} {c : Nat} (hD : s.descriptor = pvDsc)
    (hl : s.lowCta = c) {base j : Nat}
    (hs : s.b = mnDesc (base + 2048 * j)) (hj : j < 8) (hb : base % 128 = 0) {index : Nat}
    (hi : index < 4096) :
    ∃ off, off < 32768 ∧ s.byteLoc .b index = some ⟨.shared, c, base + off⟩ := by
  obtain ⟨y', k, z, hy', hk, hz, rfl⟩ := index_split hi
  obtain ⟨r, y, hr, hy, rfl⟩ : ∃ r y, r < 2 ∧ y < 64 ∧ y' = 64 * r + y :=
    ⟨y' / 64, y' % 64, by omega, Nat.mod_lt _ (by decide), by omega⟩
  have hoff : TensorSwizzle.offset .b128 (base + 16384 * r) (128 * (16 * j + k) + 2 * y + z) <
      16384 := TensorCopy.box_offset_lt (R := 128) hy (by omega) hz
  refine ⟨16384 * r + TensorSwizzle.offset .b128 (base + 16384 * r)
    (128 * (16 * j + k) + 2 * y + z), by omega, ?_⟩
  have haddr := mn_byteAddress (base := base + 2048 * j) (r := r) (y := y) (k := k) (z := z)
    (by omega) hy hz
  have e1 := TensorSwizzle.offset_add_base .b128 (base + 2048 * j + 16384 * r)
    (128 * k + 2 * y + z) (by omega)
  have e2 := TensorSwizzle.offset_add_base .b128 (base + 16384 * r)
    (128 * (16 * j + k) + 2 * y + z) (by omega)
  have e3 : base + 2048 * j + 16384 * r + (128 * k + 2 * y + z) =
      base + 16384 * r + (128 * (16 * j + k) + 2 * y + z) := by ring
  rw [← e1, e3, e2] at haddr
  have hdiv : (32 * (64 * r + y) + 2 * k + z) / (16 * 2) = 64 * r + y := by omega
  have hkdiv : (32 * (64 * r + y) + 2 * k + z) / 2 % 16 = k := by omega
  have hbmod : (32 * (64 * r + y) + 2 * k + z) % 2 = z := by omega
  have hext : 64 * r + y < 128 := by omega
  have hv := pvDsc_valid
  unfold OperandSpec.byteLoc
  simp only [hD, pvDsc, Kind.k, Kind.width, Operand.extent, CtaGroup.size, hdiv, Operand.major,
    hkdiv, hbmod, hs, hl] at hv ⊢
  simp [hv, hext, Nat.mod_eq_of_lt hext, haddr]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
