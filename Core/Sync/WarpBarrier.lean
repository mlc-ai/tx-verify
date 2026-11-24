-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.Elect

@[expose] public section

namespace PTX
noncomputable section

/-! ## THREAD-WARP-BAR — warp barrier template
Statement: `bar.warp.sync` produces a collective event that retains its member mask. The executing
  lane must be named in the mask, and otherwise the instruction is a barrier fault.

Defs: warpBarTmpl

Source:
- §9.7.15.2

Direction: reading

Applies: bar.warp.sync on sm_70 and later

Premises: The executing lane belongs to the 32-bit member mask.

Effect: Returns are constrained by DEP-WARP-BARRIER; this template alone grants no completion.
-/
def warpBarTmpl (L : Launch) (g : Nat) (t : TState) (mask : Opnd) : Tmpl :=
  match readBits L g t 32 mask with
  | .error f => .ub f
  | .ok bits => if electMember bits.toNat (laneOf L g)
    then .warpBar bits.toNat (next t) else .ub .badBarrier

/-! ## DEP-WARP-BARRIER — warp rendezvous and memory ordering

Statement: Every lane named in the mask of a `bar.warp.sync` executes it with the same mask, once
  per instance, and no participant returns before all have arrived. The memory accesses that a
  participant performs before the barrier are ordered before the accesses that the participants
  perform after it.

Defs: Execution.WarpBar, WarpBarEdge, WarpBarOk, WarpBarSync

Source:
- §9.7.15.2

Direction: reading

Applies: Dynamic bar.warp.sync instances on sm_70 and later, including partial masks

Premises: Matching labels identify a single rendezvous within one warp; every named lane
  participates once with the same mask.

Effect: `Consistent.warpBar` checks participation, the needs of the barrier (`KindNeeds`,
  DEP-ORDER) make every lane's arrival a witness of every return of the instance (execution
  layer), and baseCausality includes WarpBarSync (memory layer). Labels identify the participants of
  one rendezvous. Different source positions may participate.
-/
/-- Event `e` is a `bar.warp.sync` with member mask `mask` and instance label `inst`. -/
def Execution.WarpBar (X : Execution) (e : EvId) (mask inst : Nat) : Prop :=
  ∃ pc, X.get e = some ⟨pc, .warpBar mask inst⟩

/-- Events `e` and `f` are `bar.warp.sync` events of one instance of one warp. -/
def WarpBarEdge (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  SameWarp L e.1 f.1 ∧ ∃ mask inst, X.WarpBar e mask inst ∧ X.WarpBar f mask inst

/-- Every `bar.warp.sync` event is of a launched lane of its mask, and an instance has one mask and
at most one event of each lane. That every lane of the mask has executed the instance is the need
of the barrier (`KindNeeds`, DEP-ORDER). -/
def WarpBarOk (L : Launch) (X : Execution) : Prop :=
  (∀ e mask inst, X.WarpBar e mask inst →
    e.1 < L.threads ∧ electMember mask (laneOf L e.1)) ∧
  (∀ e f mask mask' inst, X.WarpBar e mask inst → X.WarpBar f mask' inst →
    SameWarp L e.1 f.1 → mask = mask' ∧ (e.1 = f.1 → e = f))

/-- Warp barrier synchronization from `e` to `f`: an event `i` at or after `e` and an event `j`
before `f` belong to one instance. -/
def WarpBarSync (L : Launch) (X : Execution) (e f : EvId) : Prop :=
  ∃ i j, WarpBarEdge L X (e.1, i) (f.1, j) ∧
    e.2 < i ∧ j < f.2 ∧ f.2 < (X.tr f.1).length

end
end PTX
