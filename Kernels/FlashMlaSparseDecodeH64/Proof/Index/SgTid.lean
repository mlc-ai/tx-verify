-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexAddr

@[expose] public section

/-! # The validity byte's stores of a lane are those of its thread index

A lane stores the validity byte of its quad once per block, on lanes `0 mod 4` only. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0}

/-- The validity byte's stores of a lane per block: one on lanes `0 mod 4`. -/
theorem sgB_tid (hp : Pre P L m) (g : Nat) :
    Index.sgB L g = if (L.tidOf g).x % 4 = 0 then 1 else 0 := by
  have ht := tidOf_lt hp g
  unfold Index.sgB ixSkipB
  rw [show (3 : Int) = ((2 ^ 2 - 1 : Nat) : Int) from rfl, show tw L g = W (tidOf L g) from rfl,
    andi_W_low ht (by norm_num), scmpi_ne_b_W (by omega) (by norm_num) (by norm_num)]
  simp only [tidOf, Int.toNat_zero, ne_eq]
  by_cases h : (L.tidOf g).x % 4 = 0 <;> simp [h]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
