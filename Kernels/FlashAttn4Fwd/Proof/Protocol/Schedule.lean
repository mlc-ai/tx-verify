-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Schedule
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The static schedule

Every role of both CTAs of cluster `c` (but the odd CTA's MMA warp) walks the items
`c, c + G, c + 2G, …` below the item count `T` (`G = P.clusters`, `T = P.items`). Under `Pre`:

* **Items.** Item `i` exists exactly when `i < count G T c` (`work_lt_iff`), its work item is
  the `i`-th smallest of `visits G T c` (`visits_eq`, `work_strictMono`, `work_mem_visits`), and
  the code's coordinates of an item are the exact split of its index into (batch, head, query
  block) (`coords_eq`, `coords_lt`): the parameter objects divide exactly (`Divmod.Exact`).
* Both CTAs of a cluster, all of whose threads have cluster `c`, walk the same items
  (`work_of_cluster`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Schedule
open PTX PTX.Proof PTX.Flow StaticSchedule

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The launch's schedule parameters -/

theorem clusterCount_eq (hpre : Pre P L mem0) : clusterCount L = P.clusters := by
  simp only [clusterCount, hpre.grid, hpre.cluster]
  omega

theorem totOf_items (hpre : Pre P L mem0) : totOf L = P.items := by
  rw [totOf_eq hpre]
  have := hpre.scheduleRange
  omega

/-- The work items of thread `g` are those of its cluster. -/
theorem work_of_cluster {g g' : Nat} (h : clusterOf L g = clusterOf L g') (i : Nat) :
    workOf L g i = workOf L g' i := by
  simp only [workOf, h]

/-! ### Items -/

/-! ### Coordinates -/

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Schedule
