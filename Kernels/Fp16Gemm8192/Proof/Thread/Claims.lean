-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Loader

@[expose] public section

/-! # The tile a claimed CTA gives

The code's bit arithmetic for the tile of a CTA, on the bounded values it is applied to. The
roles that start or continue a task share these facts. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof

/-- The code's bit arithmetic on bounded values, checked on every value: the claimed tile
row of a first CTA in the grid, the CLC phase flip and the second row offset of a tile. -/
theorem claim_bits : ∀ x < 1024, (truncBits 32
    (truncBits 32
        (if (truncBits 32 (BitVec.ofInt 64 6)).toNat ≥ 32 then 0
        else truncBits 32 (BitVec.ofNat 64 x) >>> (truncBits 32 (BitVec.ofInt 64 6)).toNat) &&&
      truncBits 32 (BitVec.ofInt 64 8)) |||
    truncBits 32
      (truncBits 32
          (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then 0
          else truncBits 32 (BitVec.ofNat 64 x) >>> (truncBits 32 (BitVec.ofInt 64 1)).toNat) &&&
        truncBits 32 (BitVec.ofInt 64 7))) = BitVec.ofNat 64 (x / 512 % 2 * 8 + x / 2 % 8) := by
  table_decide

theorem flip_bits : ∀ cp < 2,
    truncBits 32 (BitVec.ofNat 64 cp) ^^^ truncBits 32 (BitVec.ofInt 64 1) =
      BitVec.ofNat 64 (1 - cp) := by
  table_decide

theorem row_bits : ∀ m < 16, (truncBits 32
    (if (truncBits 32 (BitVec.ofInt 64 9)).toNat ≥ 32 then 0
    else truncBits 32 (truncBits 32 (BitVec.ofNat 64 m) <<<
      (truncBits 32 (BitVec.ofInt 64 9)).toNat)) |||
    truncBits 32 (BitVec.ofInt 64 128)) = BitVec.ofNat 64 (512 * m + 128) := by
  table_decide

/-- The claimed tile, as the code computes it, is a tile. -/
theorem claim_lt (x : Nat) : claimM x < 16 ∧ claimN x < 32 := by
  unfold claimM claimN
  split_ifs <;> omega

end PTX.Kernels.Fp16Gemm8192.Proof.Loader

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof

/-- The code's arithmetic for the starting tile row of a CTA, checked on every CTA. -/
theorem start_bits : ∀ c < 1024, (truncBits 32
    (truncBits 32
        (if (truncBits 32 (BitVec.ofInt 64 6)).toNat ≥ 32 then 0
        else truncBits 32 (BitVec.ofNat 64 c) >>> (truncBits 32 (BitVec.ofInt 64 6)).toNat) &&&
      truncBits 32 (BitVec.ofInt 64 33554424)) |||
    truncBits 32
      (truncBits 32
          (if (truncBits 32 (BitVec.ofInt 64 1)).toNat ≥ 32 then 0
          else truncBits 32 (BitVec.ofNat 64 c) >>> (truncBits 32 (BitVec.ofInt 64 1)).toNat) &&&
        truncBits 32 (BitVec.ofInt 64 7))) = BitVec.ofNat 64 (c / 512 % 2 * 8 + c / 2 % 8) := by
  table_decide

theorem claimM_of {c : Nat} (hc : c < 1024) : Loader.claimM c = c / 512 % 2 * 8 + c / 2 % 8 := by
  simp only [Loader.claimM]
  split_ifs <;> omega

theorem claimN_of {c : Nat} (hc : c < 1024) : Loader.claimN c = c / 16 % 32 := by
  simp only [Loader.claimN]
  split_ifs <;> omega

end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
