-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tmem.TmemPairHistory
public import Core.Clc.ClcExecution

@[expose] public section

namespace PTX.Tmem.Pair
noncomputable section

/-! ## ERR-TMEM-NOT-RELEASED — no live allocations at kernel completion
Statement: When every launched thread has exited or belongs to a canceled CLC task, and every issued
  allocation-management operation is complete, an execution is unsafe if the replay of some CTA's
  allocator history ends without fault in a state that still holds a live allocation. Only
  `tcgen05.dealloc` releases an allocation.

Defs: Tmem.Pair.Exited, Tmem.Pair.Released, Tmem.Pair.ReleaseUnsafe

Source:
- §9.7.18.1.2
- §9.7.18.7.1 (all allocated Tensor Memory must be explicitly deallocated before kernel exit)

Direction: reading

Applies: Allocator histories of non-exclusive resource operations of either cta_group

Premises: Every launched thread has exited (canceled CLC tasks have no thread execution), and every
  issued allocation-management operation is complete (Drained). Resource replay is checked
  independently.

Effect: ReleaseUnsafe is a safety predicate of the final allocator history (`Unsafe`).
-/
/-- Every launched thread has exited, or its CLC task was canceled and it never ran. -/
def Exited (L : Launch) (X : Execution) : Prop :=
  ∀ g < L.threads, ClcCanceled L X g ∨ ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩

/-- Every CTA's allocator history that replays without fault ends with no live allocation. -/
def Released (X : Execution) : Prop :=
  ∀ cta s, runRequests {} (X.tmemHistory cta) = .done s → s.live = []

/-- A finished execution in which some CTA still holds Tensor Memory: all threads have exited,
all allocation-management operations are complete, and some allocator still has a live
allocation. -/
def ReleaseUnsafe (L : Launch) (X : Execution) : Prop :=
  Exited L X ∧ Drained L X ∧ ¬ Released X

end
end PTX.Tmem.Pair
