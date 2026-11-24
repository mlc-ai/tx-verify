-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assumption.CommitOrder

/-! Litmus tests for ASM-COMMIT-ORDER's performance constraint (`commitPerformedAt`, the `wf` of
`commitOrderAt`).

`X`: one thread issues two `tcgen05.commit`s (pcs 0 and 1); the second's arrive-on at rank 0 is
performed and the first's is not. With the commit at pc 0 selected the execution violates the
assumption's constraint, so it is not consistent under it (`selected_rejects`); with no site
selected the constraint is empty and the execution stays (`off_keeps`). When both arrive-ons are
performed the constraint holds (`both_ok`). -/

namespace PTX.Tests.CommitOrderLitmus
open PTX

def sp : TcCommit.Spec := ⟨.one, ⟨.shared, 0, 0⟩, 1, 0, 1⟩

def evs : List Event := [⟨0, .tc (.commit sp)⟩, ⟨1, .tc (.commit sp)⟩]

/-- Only the second commit's arrive-on is performed. -/
def X : Execution where
  tr g := if g = 0 then evs else []
  rf _ _ := none
  objects _ := []
  tcNotified i := if i = (0, 1) then {0} else ∅

/-- Both arrive-ons are performed. -/
def Y : Execution where
  tr g := if g = 0 then evs else []
  rf _ _ := none
  objects _ := []
  tcNotified i := if i.1 = 0 then {0} else ∅

/-- **Selected: the execution violates the constraint.** -/
theorem selected_rejects : ¬ (Assumption.commitOrderAt "litmus" [0] "").wf L mem0 X := by
  intro h
  have := h 0 0 1 0 sp 0 rfl rfl (by decide) ⟨sp, 1, rfl⟩ (by intro k h1 h2; omega)
    (by simp [X])
  simp [X] at this

/-- **Off: no constraint.** -/
theorem off_keeps : (Assumption.commitOrderAt "litmus" [] "").wf L mem0 X := by
  intro g j j' pc s r _ hs
  simp at hs

/-- **Both performed: the constraint holds.** -/
theorem both_ok : (Assumption.commitOrderAt "litmus" [0] "").wf L mem0 Y := by
  intro g j j' pc s r he _ _ _ _ hr
  have hg : g = 0 := by
    by_contra hg
    simp [Execution.get, Y, hg] at he
  simp [Y, hg] at hr ⊢
  exact hr

end PTX.Tests.CommitOrderLitmus
