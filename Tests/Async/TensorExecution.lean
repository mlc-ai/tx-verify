-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Execution.ExecutionGrowth

namespace PTX.Tests.TensorExecution
noncomputable section

private def L : Launch := {
  grid := 2, block := 1, params := fun _ => none,
  clusterSize := ⟨2, by decide⟩ }
private def spec : TensorCopy.Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, ⟨.shared, 1, 64⟩, true, .two⟩
private def observation : TensorCopy.Observation := ⟨spec, {}⟩
private def X : Execution := {
  tr := fun g => if g = 0 then [⟨0, .tensorIssue 1024 spec⟩] else [],
  rf := fun _ _ => none,
  tensor := fun i => if i = (0, 0) then some observation else none }

private theorem observation_ok : TensorCopy.CopyOk spec observation.effects := by
  constructor
  · intro slot byte h; cases h
  · intro slot value h; cases h
  · intro h; cases h

example : TensorOk L X := by
  intro i obs ho
  change (if i = (0, 0) then some observation else none) = some obs at ho
  split_ifs at ho with hi
  · cases hi
    cases ho
    exact ⟨⟨1024, 0, rfl⟩, observation_ok, (by unfold TensorCopy.RoutingOk; decide), (by decide)⟩

-- A snapshot cannot contain a copy without the instruction that issued it.
private def ghost : Execution := { X with tr := fun _ => [] }
example : ¬ TensorOk L ghost := by
  intro h
  obtain ⟨⟨address, pc, he⟩, _, _⟩ := h (0, 0) observation rfl
  cases he

-- Nor can a matching issue justify an already-complete snapshot with no writes.
private def premature : TensorCopy.Observation := ⟨spec, { notified := true }⟩
private def bad : Execution := {
  X with tensor := fun i => if i = (0, 0) then some premature else none }
example : ¬ TensorOk L bad := by
  intro h
  have hc := (h (0, 0) premature rfl).2.1
  let slot : TensorTransfer.Slot spec.descriptor :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have := TensorCopy.missing_write_not_complete hc slot rfl
  cases this

-- Prefix extension cannot erase a recorded operation, even before its reads arrive.
example : ¬ X.le { X with tensor := fun _ => none } := by
  intro h
  obtain ⟨newer, hn, _⟩ := h.2.2.2.2.2.2.2.2.1 (0, 0) observation rfl
  cases hn

end
end PTX.Tests.TensorExecution
