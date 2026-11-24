-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLoader
public import Kernels.FlashAttn4Fwd.Proof.Thread.Machine
public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The item count of the roles

Every role walks its cluster's items `0, 1, …` while they are below the item count `Work.T L g`
(`items` of the softmax and correction warps, the loop test `work … < totOf` of the MMA warp are
the same count): an item below the count passes the loop test (`Work.workOf_lt`,
`Work.mma_work_lt`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-! ### The item count -/

/-- Every item below the count passed the loop test. -/
theorem Work.workOf_lt (hpre : Pre P L mem0) {i : Nat} (h : i < Work.T L g) :
    workOf L g i < totOf L := by
  rw [Work.totOf_eq' hpre]
  exact (Work.lt_T_iff hpre).mp h

/-- The MMA warp's loop test is the count. -/
theorem Work.mma_work_lt (hpre : Pre P L mem0) {i : Nat} :
    Mma.work L g i < totOf L ↔ i < Work.T L g := by
  rw [Work.totOf_eq' hpre, Work.lt_T_iff hpre]
  rfl

theorem Correction.items_eq (L : Launch) (g : Nat) : Correction.items L g = Work.T L g := rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof
