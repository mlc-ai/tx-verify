-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefArith
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
public import Kernels.FlashMlaSparseDecodeH64.Data.Indices

@[expose] public section

/-! # The index warp's block counts are the data's

-- domain: valid-rows

For a length word `W a` (`a + 63 < 2 ^ 31`) the main cache's block count `nMain` is the data's
`numOrigBlocks a` (`nMain_val`); the loops' blocks (`roundsOf`, `rounds_val`) are the data's
`totalBlocks`. With the lengths at most the index arrays' widths, which are whole blocks, the
blocks of the main cache fill at most `topk` slots (`blocks_main_le`) and those of the extra cache
at most `extra_topk` (`blocks_extra_le`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 FlashMlaSparseDecodeH64

noncomputable section

/-- **The main cache's block count of a length word.** -/
theorem nMain_val {a : Nat} (h : a + 63 < 2 ^ 31) : nMain (W a) = numOrigBlocks a := by
  have hA := padL_W h
  have ha := Nat.div_mul_le_self (a + 64 - 1) 64
  have ha' := Nat.lt_div_mul_add (a := a + 64 - 1) (b := 64) (by norm_num)
  have hE : a + 63 - (a + 63) % 64 = (a + 64 - 1) / 64 * 64 := by omega
  have hm : ixMax (W a) = W (max ((a + 64 - 1) / 64 * 64) 64) := by
    show max32 (padL (W a)) (i32 64) = _
    rw [hA, hE, show i32 64 = W 64 by decide]
    exact max32_W (by omega) (by norm_num)
  unfold nMain ixNmain
  rw [hm, shru_int (by omega) (by norm_num) (by norm_num)]
  simp only [Int.reduceToNat, Nat.reducePow]
  rw [toNat_W (by omega)]
  simp only [numOrigBlocks, origPadded, ceilToMultiple, topkBlock]

/-- **The main cache's blocks fit the index array's row.** -/
theorem blocks_main_le {len t : Nat} (hl : len ≤ t) (hd : t % 64 = 0) (hp : 0 < t) :
    64 * numOrigBlocks len ≤ t := by
  simp only [numOrigBlocks, origPadded, ceilToMultiple, topkBlock]
  omega

/-- **The extra cache's blocks fit the extra index array's row.** -/
theorem blocks_extra_le {a b t : Nat} (hl : b ≤ t) (hd : t % 64 = 0) :
    64 * (totalBlocks a b - numOrigBlocks a) ≤ t := by
  simp only [totalBlocks, numOrigBlocks, origPadded, ceilToMultiple, topkBlock]
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
