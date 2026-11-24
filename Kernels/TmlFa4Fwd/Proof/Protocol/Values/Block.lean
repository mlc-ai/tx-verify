-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.KvSlot
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands

@[expose] public section

/-! # The bytes of a K/V block

Byte `z` of element `(row, d)` of a block at a multiple of 1024 is at byte `(2 d + z) mod 16` of the
16 bytes that the copy of row `row / 8` and half `d / 64` of the lane of index `blockLane row d`
writes (`blockAddr_eq`): the lanes' columns are the swizzled chunks of eight lines. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The index of the loader lane that copies element `(row, d)` of a block. -/
def blockLane (row d : Nat) : Nat := 8 * (row % 8) + d % 64 / 8

theorem blockLane_lt (row d : Nat) : blockLane row d < 64 := by unfold blockLane; omega

private theorem chunk_xor : ∀ c < 8, ∀ r < 8,
    (BitVec.ofNat 3 c ^^^ BitVec.ofNat 3 r : BitVec 3).toNat = c ^^^ r := by decide

private theorem rowCol_lane (row c : Nat) (hc : c < 8) :
    Loader.rowCol (8 * (row % 8) + c) = 8 * (row % 8) + (c ^^^ row % 8) := by
  unfold Loader.rowCol
  have h1 : (8 * (row % 8) + c) / 8 = row % 8 := by omega
  have h2 : (8 * (row % 8) + c) % 8 = c := by omega
  rw [h1, h2]

/-- **The address of an element's byte** in a block at a multiple of 1024. -/
theorem blockAddr_eq {base row d z : Nat} (hb : base % 1024 = 0) (hz : z < 2) :
    blockAddr base row d z = base + 16384 * (d / 64) + 1024 * (row / 8) +
      16 * Loader.rowCol (blockLane row d) + (2 * (d % 64) + z) % 16 := by
  have h0 : d % 64 < 64 := Nat.mod_lt _ (by decide)
  have e1 : (128 * row + 2 * (d % 64) + z) / 128 = row := by omega
  have e2 : (128 * row + 2 * (d % 64) + z) / 16 = 8 * row + d % 64 / 8 := by omega
  have e3 : (128 * row + 2 * (d % 64) + z) % 16 = (2 * (d % 64) + z) % 16 := by omega
  have e4 : BitVec.ofNat 3 (8 * row + d % 64 / 8) = BitVec.ofNat 3 (d % 64 / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have e5 : ((base + 16384 * (d / 64)) / 128 + row) % TensorSwizzle.sectors .b128 = row % 8 := by
    simp only [TensorSwizzle.sectors]
    omega
  have e6 : TensorSwizzle.chunk .b128 (base + 16384 * (d / 64)) row
      (BitVec.ofNat 3 (d % 64 / 8)) = BitVec.ofNat 3 (d % 64 / 8) ^^^ BitVec.ofNat 3 (row % 8) := by
    simp only [TensorSwizzle.chunk, TensorSwizzle.mask, e5]
  unfold blockAddr TensorSwizzle.offset
  rw [e1, e2, e3, e4, e6, chunk_xor _ (by omega) _ (by omega)]
  unfold blockLane
  rw [rowCol_lane _ _ (by omega)]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
