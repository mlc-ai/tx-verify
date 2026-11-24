-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.TensorStore.TensorStore

namespace PTX.Tests.TensorStore
open PTX.TensorStore
noncomputable section

private def spec : Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![0, 0], ⟨.shared, 0,
    128⟩, none⟩, none⟩
private def slot0 : TensorTransfer.Slot spec.descriptor :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
private def byte : Byte := (.bits 16 0, 0)
private def readOnly : Effects spec := { read := fun _ => some byte, readsDone := true }

example : spec.sharedLoc slot0 = ⟨.shared, 0, 144⟩ := rfl
example : destination spec slot0 = some ⟨.global, 0, 4096⟩ := rfl

-- Source consumption may complete before any global write is recorded.
private theorem read_only_ok : CopyOk spec readOnly := by
  constructor
  · intro slot b hw; cases hw
  · intro _ slot loc _; exact ⟨byte, rfl⟩
  · intro h; cases h
  · intro slot b hw; cases hw
  · intro slot b h; cases h
example : CopyOk spec readOnly := read_only_ok
example : readOnly.fullDone = false := rfl

-- Premature full completion fails even if every source byte has been read.
example : ¬ CopyOk spec { readOnly with fullDone := true } := by
  intro h
  obtain ⟨b, hw⟩ := (h.complete rfl).2 slot0 ⟨.global, 0, 4096⟩ rfl
  cases hw

private def snapshots : Nat → Option Observation := fun i =>
  if i = 0 then some ⟨spec, readOnly⟩ else none
private def groups : BulkGroup.State Nat := BulkGroup.run [.issue 0, .commit]
example : BulkGroup.WaitReady groups (completion snapshots) .read 0 := by
  intro i hi
  have he : i = 0 := by simpa [BulkGroup.Observes, BulkGroup.required, groups,
    BulkGroup.run, BulkGroup.step] using hi
  subst i
  exact ⟨⟨spec, readOnly⟩, rfl, rfl⟩
example : ¬ BulkGroup.WaitReady groups (completion snapshots) .full 0 := by
  intro h
  have hi : BulkGroup.Observes groups 0 0 := by
    simp [BulkGroup.Observes, BulkGroup.required, groups, BulkGroup.run, BulkGroup.step]
  obtain ⟨o, ho, hd⟩ := group_full_completed h hi
  have he : o = ⟨spec, readOnly⟩ := (Option.some.inj ho).symm
  subst o
  cases hd

private theorem destination_exists (slot : TensorTransfer.Slot spec.descriptor) :
    ∃ loc, destination spec slot = some loc := by
  rcases slot with ⟨x, y, k⟩
  fin_cases x <;> fin_cases y <;> fin_cases k <;> exact ⟨_, rfl⟩
private def completed : Effects spec := {
  read := fun _ => some byte, write := fun _ => some byte,
  readsDone := true, fullDone := true }
example : CopyOk spec completed := by
  constructor
  · intro slot b hw
    cases hw
    exact ⟨destination_exists slot, byte, rfl, fun _ => rfl⟩
  · intro _ slot _ _; exact ⟨byte, rfl⟩
  · intro _; exact ⟨rfl, fun _ _ _ => ⟨byte, rfl⟩⟩
  · intro _ _ _ h; cases h
  · intro slot b h; cases h
example : Extends readOnly completed := by
  refine ⟨fun _ _ h => h, ?_, fun _ => rfl, ?_, fun _ => rfl, fun _ _ h => h⟩
  · intro slot b hw; cases hw
  · intro h; cases h

-- OOB global destinations are omitted rather than wrapped or filled with zero.
private def oob : Spec := { spec with origin := ![8, 0] }
example : destination oob slot0 = none := rfl
example : oob.sharedLoc slot0 = spec.sharedLoc slot0 := rfl
example (e : Effects oob) (h : CopyOk oob e) : e.write slot0 = none := no_oob_write h slot0 rfl

-- A skipped source byte cannot appear after read completion permits source reuse.
example {a b : Effects oob} (h : Extends a b) (hd : a.readsDone = true)
    (hr : a.read slot0 = none) : b.read slot0 = none := no_read_after_done h hd slot0 hr

-- Output origin restrictions differ from input zero-fill behavior.
example : ¬ Valid 0 { spec with origin := ![-1, 0] } := by
  intro h
  have hz := h.2.1 0
  norm_num at hz
-- Scatter4 row coordinates must be nonnegative too.
example : ¬ Valid 0 { spec with rows := some ![0, -1, 2, 3] } := by
  intro h
  have hz := h.2.2.1 _ rfl 1
  norm_num at hz
example : ¬ Valid 1 spec := by
  intro h
  have hc := h.2.2.2.2.1
  cases hc

end
end PTX.Tests.TensorStore
