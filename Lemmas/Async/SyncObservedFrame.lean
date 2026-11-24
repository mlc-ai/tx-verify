-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.WaitOrder
public import Core.Async.BulkExecution

@[expose] public section

/-! ## The `SyncObserved` frame of an effect-only extension

`SyncObserved` has two disjuncts. The `GroupWaitsFor` one reads only `get` and `tr`, which an
effect-only extension keeps, so it transfers outright; only the stage's presence is a row fact.
The `MbarObserved` one reads `RefPresent` (a row fact) and `WaitObserves`, whose object-log part
`MBarrier.UpdateBeforeWait (X.objects m)` is kept, so the same single row fact covers both. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {X : Execution} {N : Ref → Prop}
  {T : EvId → Option TensorCopy.Observation} {S : EvId → Option TensorStore.Observation}
  {C : EvId → Clc.Effects} {R : Ref → Nat → Option Ref}

set_option quotPrecheck false in
local notation "Y" => ({ X with rf := R, tensor := T, tensorStores := S, clc := C } : Execution)

/-- **The `SyncObserved` frame.** At two old nodes, a synchronization the extension observes is
one `X` observes. -/
theorem syncObserved_frame (hpres : ∀ u, ¬ N u → ((Y).RefPresent u ↔ X.RefPresent u))
    {x w : Ref} (hx : ¬ N x) (h : SyncObserved L Y x w) : SyncObserved L X x w := by
  rcases h with ⟨⟨hp, j, m, acquire, ws, hw', hob, hcnt⟩, j', m', pc, q, ws', us, g, hw2, hget,
    hrel, hsc⟩ | ⟨i, p, j, k, hx', hw', hp, hgw, hgs⟩
  · refine Or.inl ⟨⟨(hpres x hx).1 hp, j, m, acquire, ws, hw', hob, hcnt⟩,
      j', m', pc, q, ws', us, g, hw2, hget, hrel, hsc⟩
  · subst hx'
    exact Or.inr ⟨i, p, j, k, rfl, hw', (hpres _ hx).1 hp, hgw, hgs⟩

end
end PTX
