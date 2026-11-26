-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Result.Run

@[expose] public section

/-! # The block count of a CTA is the reference's

The code's 32-bit block count of a CTA (`blocksOf`, `roundsOf` of the two length words) is the
reference's `Result.blocks` of the CTA's row (`rowOf`): the row's two lengths are inside the padded
range (`len_words`), where the bitvector arithmetic is the data's (`rounds_val`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0}

/-- **The block count of CTA `c` is `Result.blocks` of its row.** -/
theorem blocksOf_eq (hp : Pre P L m) (c : Nat) :
    blocksOf P L c = Result.blocks P (rowOf L c) := by
  obtain ⟨hwa, hwb, hr, -, -⟩ := len_words hp c
  rw [blocksOf, hwa, hwb]
  exact rounds_val hr

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
