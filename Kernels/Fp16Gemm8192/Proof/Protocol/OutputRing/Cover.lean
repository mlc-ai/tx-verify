-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Lemmas.Flow.Store

@[expose] public section

/-! # The staging stores cover the TMA store's source

The output tensor map reads, at column `x`, row `y` and byte `b` of the tile, the byte of the
staging buffer at the 64-byte-swizzled offset of `64 y + 2 x + b` (`output_readLoc`). The base of a
staging buffer is 512-byte aligned, so the swizzle's phase is zero and the offset is the row's 64
bytes, the chunk of 16 bytes permuted by the row, and the element's bytes (`swizzle_zero_phase`).
That byte is in the four-byte staging store of chunk `x / 8` and element `x / 2 % 4` of the thread
whose index in its warp group is the row `y` (`source_in_store`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Flow

noncomputable section

namespace OutputRing

/-- The tensor store's source byte of the output map: the swizzled offset of the byte in its box. -/
theorem output_readLoc {globalBase cta base x y byte : Nat}
    {cls : TensorDescriptor.AllocationClass} {origin : Fin 2 → Int}
    (hx : x < 32) (hy : y < 128) (hb : byte < 2) :
    TensorStore.readLoc ⟨⟨1, Fp16Gemm8192.mapD globalBase cls, origin, ⟨.shared, cta, base⟩, none⟩,
      none⟩ x y byte =
      some ⟨.shared, cta, base + TensorSwizzle.offset .b64 base (64 * y + 2 * x + byte)⟩ := by
  rcases (by omega : byte = 0 ∨ byte = 1) with rfl | rfl <;>
  simp [TensorStore.readLoc, TensorTransfer.slotAt, TensorBox.sharedLoc, Fp16Gemm8192.mapD,
    encodeTiled, TensorTile.count, TensorTile.step, TensorTile.sharedByte, TensorTile.linearByte,
    TensorTile.rows, TensorTile.rowsOf, Fin.succ_zero_eq_one, TensorTile.rowBytes,
    TensorTile.swizzleWidth, TensorDescriptor.Format.bytes, hx, hy, hb, Nat.mul_comm]
  exacts [⟨_, _, .inl ⟨rfl, rfl⟩⟩, ⟨_, _, .inr ⟨rfl, rfl⟩⟩]

/-- The raw layout's four-vector permutation at a row. -/
def vectorIndex (row vector : Nat) : Nat := Nat.xor vector (row / 2 % 4)

/-- Physical vector index including the base's phase. -/
def physicalChunk (base row vector : Nat) : Nat :=
  ((BitVec.ofNat 3 (4 * (row % 2) + vector)) ^^^
    (BitVec.ofNat 3 ((base / 128 + row / 2) % 4))).toNat

/-- A byte of a row's chunk, from the hardware swizzle's 128-byte pattern row. -/
theorem swizzle_offset {base row vector byte : Nat} (hv : vector < 4) (hb : byte < 16) :
    TensorSwizzle.offset .b64 base (64 * row + 16 * vector + byte) =
      128 * (row / 2) + 16 * physicalChunk base row vector + byte := by
  have hd128 : (64 * row + 16 * vector + byte) / 128 = row / 2 := by omega
  have hd16 : (64 * row + 16 * vector + byte) / 16 = 4 * row + vector := by omega
  have hm16 : (64 * row + 16 * vector + byte) % 16 = byte := by omega
  have he : BitVec.ofNat 3 (4 * row + vector) = BitVec.ofNat 3 (4 * (row % 2) + vector) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [TensorSwizzle.offset, hd128, hd16, hm16, he, physicalChunk, TensorSwizzle.chunk,
    TensorSwizzle.mask, TensorSwizzle.sectors]

/-- A zero pattern phase reproduces the permutation. -/
theorem chunk_zero_phase {base row vector : Nat} (hphase : base / 128 % 4 = 0) (hv : vector < 4) :
    physicalChunk base row vector = 4 * (row % 2) + vectorIndex row vector := by
  have hm : (base / 128 + row / 2) % 4 = row / 2 % 4 := by omega
  unfold physicalChunk vectorIndex
  rw [hm]
  have hp : row % 2 < 2 := by omega
  have hq : row / 2 % 4 < 4 := by omega
  generalize row % 2 = p at *
  generalize row / 2 % 4 = q at *
  interval_cases p <;> interval_cases q <;> interval_cases vector <;> rfl

/-- At a zero phase the swizzle is the row's 64 bytes and the permuted chunk. -/
theorem swizzle_zero_phase {base row vector byte : Nat} (hphase : base / 128 % 4 = 0)
    (hv : vector < 4) (hb : byte < 16) :
    TensorSwizzle.offset .b64 base (64 * row + 16 * vector + byte) =
      64 * row + 16 * vectorIndex row vector + byte := by
  rw [swizzle_offset hv hb, chunk_zero_phase hphase hv]
  omega

/-- **The source byte is in the staging store of its row's thread.** For a staging buffer of base
`T`'s group and parity `par`, with a base of zero phase, the byte at column `x`, row `y` and byte
`b` of the output map lies in the four bytes of chunk `x / 8` and element `x / 2 % 4` of the thread
of that group whose index in the group is `y`. -/
theorem source_in_store {sb T t' par x y b : Nat}
    (hphase : (sb + Consumer.stagingBase T par) / 128 % 4 = 0)
    (hx : x < 32) (hy : y < 128) (hb : b < 2) (ht' : t' = 128 * (T / 32 / 4) + y) :
    sb + Consumer.stagingOff t' par (x / 8) (x / 2 % 4) ≤
        (sb + Consumer.stagingBase T par) +
          TensorSwizzle.offset .b64 (sb + Consumer.stagingBase T par) (64 * y + 2 * x + b) ∧
      (sb + Consumer.stagingBase T par) +
          TensorSwizzle.offset .b64 (sb + Consumer.stagingBase T par) (64 * y + 2 * x + b) <
        sb + Consumer.stagingOff t' par (x / 8) (x / 2 % 4) + 4 := by
  have hv : x / 8 < 4 := by omega
  have h1 : 64 * y + 2 * x + b = 64 * y + 16 * (x / 8) + (4 * (x / 2 % 4) + 2 * (x % 2) + b) := by
    omega
  rw [h1, swizzle_zero_phase hphase hv (by omega)]
  have hxor : (t' / 2 % 4) ^^^ (x / 8) = vectorIndex y (x / 8) := by
    unfold vectorIndex
    rw [show t' / 2 % 4 = y / 2 % 4 by omega, Nat.xor_comm]
    rfl
  simp only [Consumer.stagingOff, Consumer.stage, Consumer.stagingBase, hxor]
  omega

end OutputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
