-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Assign
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSourceLane

@[expose] public section

/-! # The output tensor stores, for the upper layers

The statements the safety, protocol and result layers consume about the output warp's tensor
stores, from `Proof2.Epilogue.store_issue`: every store writes the selected work item's box of
its CTA through the O map. -/

namespace PTX.Kernels.TmlFa4Fwd.OutputWarp
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Every issued output box is the selected work item's box of its CTA. -/
theorem issuedAssignment (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec) :
    AssignedOutputBox p l i.1 (i.1 / l.block) spec := by
  obtain ⟨-, b, hb, st, bx, hlo, hhi, rfl⟩ := Proof2.Epilogue.store_issue hp hX hIssue
  exact ⟨b, hb, st, bx, hlo, hhi, rfl⟩

/-- Every issued output box is a box of the output of a request and head. -/
theorem issuedBox (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec) :
    ∃ batch < p.batch, ∃ head < p.heads, ∃ (tile : Nat) (stage : Fin 2) (box : Fin 4),
      spec = writebackStoreSpec p l i.1 batch head tile stage box := by
  obtain ⟨-, b, hb, st, bx, hlo, hhi, rfl⟩ := Proof2.Epilogue.store_issue hp hX hIssue
  exact ⟨b, hb, _, (assignedCoordinates_valid hp hlo hhi).2, _, st, bx, rfl⟩

/-- Every output tensor store uses the launch's rank-four O map and a staging slot of its
CTA. -/
theorem storeBox (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    addr = p.oMapAddress ∧
      (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨3, p.oMap⟩ ∧
      ∃ stage box, s.sharedBase = sharedSlot l i.1 stage box := by
  obtain ⟨ha, b, hb, st, bx, hlo, hhi, rfl⟩ := Proof2.Epilogue.store_issue hp hX hi
  exact ⟨ha, rfl, st, bx, rfl⟩

/-- Every output tensor store uses the ABI's descriptor. -/
theorem storeDescriptor (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i addr s) :
    addr = p.oMapAddress ∧
      (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨3, p.oMap⟩ :=
  ⟨(storeBox hp hX hi).1, (storeBox hp hX hi).2.1⟩

/-- Every output tensor store uses the O map, a staging slot of its CTA and follows its stage's
ready acquire. -/
theorem readyBox (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorStore.Spec} (hIssue : X.TensorStoreIssue i addr spec) :
    addr = p.oMapAddress ∧
      (⟨spec.outer, spec.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) =
        ⟨3, p.oMap⟩ ∧
      ∃ stage box, spec.sharedBase = sharedSlot l i.1 stage box ∧
        Thread.Output.ReadyAcquire l X i stage := by
  obtain ⟨ha, hd, -⟩ := storeBox hp hX hIssue
  obtain ⟨st, bx, hb, j, hj, he⟩ := Proof2.Epilogue.store_ready hp hX hIssue
  refine ⟨ha, hd, st, bx, hb, j, hj, ?_⟩
  rw [he]
  fin_cases st <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.OutputWarp
