-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Bound.Machine
public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Lemmas.Kernel.Bound

@[expose] public section

/-! # `BoundGoal`

Every step of a thread's machine lowers its rank by the step's count (`Bound.rank_step`; a
failed poll leaves the state unchanged and is not counted), and every thread starts at rank at
most `Bound.N P = 256 + 256 (sk / 128 + 1) (items + 1) + 64` (`Bound.rank_init`). Along every
consistent execution the machines follow the threads (`tracked`), so a thread has at most
`N P + 2` counted events (`Frame.bound_of_rank`), and every consistent execution has bounded
size.

The machine follows every thread of every consistent execution (`tracked`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- The MMA warp's rank decreases given at least one cluster (`Bound.mmaRank_step`); the
precondition gives it. -/
theorem mma_clusters_pos (hpre : Pre P L mem0) : 0 < Mma.clusters L := by
  have := hpre.clustersPos
  simp only [Mma.clusters, hpre.grid, hpre.cluster]
  omega

/-- **`BoundGoal`**: consistent executions have bounded size. FA4 issues no linear copy, so no
copy destination is too large. -/
theorem bound_goal (hpre : Pre P L mem0) : BoundGoal kernel asms L mem0 :=
  Frame.bound_of_rank (fun _ hg => sound hpre hg) (fun _ hX => tracked hpre hX) (Bound.rank L)
    (fun _ _ _ _ _ h => Bound.rank_step (mma_clusters_pos hpre) h) (Bound.N P)
    (fun g _ => Bound.rank_init hpre g) (fun _ hX _ _ ⟨_, he⟩ => (TmemFacts_no_bulk hX he).elim)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
