-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProATac

@[expose] public section

/-! # The prologue's local segments, pc 411 to 504

Each lemma is one run of local instructions between two checkpoints, from the registers live at
the first (valued by the table of the thread's data) to the registers live at the second. A run
that starts after an election carries the facts of the election's result (the predicate of the
elected lane and of the guard, `a` and `b`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

seg_run seg_411_419_skipG 411 419 skip 81 q 12 16
seg_run seg_419_420 419 420 q 16 17
seg_run seg_419_431_skipG 419 431 skip 82 q 16 22
seg_run seg_431_443_skipG 431 443 skip 82 q 22 28
seg_run seg_443_451_skipG 443 451 skip 82 q 28 32
seg_run seg_451_452 451 452 q 32 33
seg_run seg_451_463_skipG 451 463 skip 83 q 32 38
seg_run seg_463_475_skipG 463 475 skip 83 q 38 44
seg_run seg_475_483_skipG 475 483 skip 83 q 44 48
seg_run seg_483_484 483 484 q 48 49
seg_run seg_483_495_skipG 483 495 skip 84 q 48 54
seg_run seg_495_507_skipG 495 507 skip 84 q 54 60

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
