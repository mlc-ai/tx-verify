-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorCopy

namespace PTX.TensorCopy
noncomputable section

private def spec : Spec :=
  ⟨⟨1, ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, .small⟩, ![-16, 0], ⟨.shared,
    1, 128⟩, none⟩, ⟨.shared, 0, 64⟩, true, .two⟩

private theorem all_oob (slot : TensorTransfer.Slot spec.descriptor) :
    source spec slot = .fill .zero .f16 slot.2.2.val := by
  apply source_out_of_bounds
  intro h
  have hn := (h 0).1
  have hx := slot.1.isLt
  change slot.1.val < 8 at hx
  simp [TensorTransfer.coord, TensorTile.coord, TensorTile.step, TensorTransfer.index,
    TensorTile.indexOf, spec] at hn
  change 16 ≤ slot.1.val at hn
  omega

private def launch : Launch := {
  grid := 2, block := 128, params := fun _ => none, clusterSize := ⟨2, by decide⟩ }
example : RoutingOk launch 1 spec := by
  unfold RoutingOk
  decide
example : ¬ RoutingOk launch 1 { spec with group := .one } := by
  unfold RoutingOk
  decide
example : ¬ RoutingOk launch 1 { spec with clusterAddress := false } := by
  unfold RoutingOk
  decide

private def filled : Effects spec where
  write := fun slot => some (.filled .zero .f16 slot.2.2.val)
  notified := true

private theorem filled_ok : CopyOk spec filled := by
  constructor
  · intro slot byte h; cases h
  · intro slot value h
    change some (.filled .zero .f16 slot.2.2.val) = some value at h
    cases h
    rw [all_oob]
  · intro _ slot
    exact ⟨_, rfl⟩

-- OOB bytes count, but swizzle padding does not; destination and mbarrier owners differ.
example : Completion spec filled ⟨.shared, 0, 64⟩ 16 := by
  exact ⟨rfl, rfl, rfl⟩
example : ¬ Completion spec filled ⟨.shared, 1, 64⟩ 16 := by
  rintro ⟨_, h, _⟩
  cases h
example : ¬ Completion spec filled spec.mbar 128 := by
  rintro ⟨_, _, h⟩
  cases h

-- An issue or an invented completion flag cannot substitute for the data writes.
private def premature : Effects spec where
  notified := true
example : ¬ CopyOk spec premature := by
  intro h
  let slot : TensorTransfer.Slot spec.descriptor :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have := missing_write_not_complete h slot rfl
  cases this

end
end PTX.TensorCopy
