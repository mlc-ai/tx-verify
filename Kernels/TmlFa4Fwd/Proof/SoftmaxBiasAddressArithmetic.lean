-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLayout
import Kernels.TmlFa4Fwd.Proof.MmaQkKeyLayout

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof

/-- The decoded shift, AND and XOR swizzle the absolute byte address of a 16-byte Bias chunk. -/
theorem biasSwizzleWord {base row col : Nat} (hBase : base % 128 = 0) (hc : col < 8) :
    let raw := base + 128 * row + 16 * col
    (raw >>> 3 &&& 112) ^^^ raw =
      base + TensorSwizzle.offset .b128 base (128 * row + 16 * col) := by
  dsimp only
  let raw := base + 128 * row + 16 * col
  rw [Nat.xor_comm]
  change kvSwizzle raw = _
  rw [Mma.kvSwizzle_eq_offset]
  have hAbsRow : raw / 128 = base / 128 + row := by dsimp [raw]; omega
  have hAbsCol : raw / 16 % 8 = col := by dsimp [raw]; omega
  have hAbsByte : raw % 16 = 0 := by dsimp [raw]; omega
  have hRow : (128 * row + 16 * col) / 128 = row := by omega
  have hCol : (128 * row + 16 * col) / 16 % 8 = col := by omega
  have hByte : (128 * row + 16 * col) % 16 = 0 := by omega
  simp only [TensorSwizzle.offset, TensorSwizzle.chunk, TensorSwizzle.mask, TensorSwizzle.sectors,
    hAbsRow, hAbsByte, hRow, hByte, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.reducePow,
    hAbsCol, hCol, Nat.zero_div, Nat.zero_add, Nat.mod_mod, Nat.add_zero]
  omega

end PTX.Kernels.TmlFa4Fwd.Softmax
