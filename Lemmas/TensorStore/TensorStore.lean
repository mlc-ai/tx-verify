-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorStore
public import Lemmas.Tensor.TensorTransfer
public import Lemmas.Tensor.TensorCopy
public import Lemmas.Async.BulkGroup

@[expose] public section

namespace PTX.TensorStore
noncomputable section

theorem no_oob_write {s : Spec} {e : Effects s} (h : CopyOk s e)
    (slot : TensorTransfer.Slot s.descriptor) (hd : destination s slot = none) :
    e.write slot = none := by
  cases hw : e.write slot with
  | none => rfl
  | some b =>
    obtain ⟨loc, hl⟩ := (h.writes slot b hw).1
    rw [hd] at hl
    cases hl

theorem extends_refl {s : Spec} (e : Effects s) : Extends e e :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun h => h, fun h => h, fun _ => rfl, fun _ _ h => h⟩

theorem extends_trans {s : Spec} {a b c : Effects s}
    (hab : Extends a b) (hbc : Extends b c) : Extends a c :=
  ⟨fun slot byte h => hbc.1 slot byte (hab.1 slot byte h),
   fun slot byte h => hbc.2.1 slot byte (hab.2.1 slot byte h),
   fun h => hbc.2.2.1 (hab.2.2.1 h),
   fun h => hbc.2.2.2.1 (hab.2.2.2.1 h),
   fun h => (hbc.2.2.2.2.1 (hab.2.2.1 h)).trans (hab.2.2.2.2.1 h),
   fun slot byte h => hbc.2.2.2.2.2 slot byte (hab.2.2.2.2.2 slot byte h)⟩

/-- Read completion closes even those source slots skipped for OOB output. -/
theorem no_read_after_done {s : Spec} {a b : Effects s} (h : Extends a b)
    (hd : a.readsDone = true) (slot : TensorTransfer.Slot s.descriptor)
    (ha : a.read slot = none) : b.read slot = none := by rw [h.2.2.2.2.1 hd, ha]

/-- A full bulk-group wait cannot be justified just by read completion. -/
theorem group_full_completed {ι : Type} {snapshots : ι → Option Observation}
    {groups : BulkGroup.State ι} {n : Nat}
    (h : BulkGroup.WaitReady groups (completion snapshots) .full n)
    {i : ι} (hi : BulkGroup.Observes groups n i) :
    ∃ o, snapshots i = some o ∧ o.effects.fullDone = true := (h i hi).2

theorem group_reads_completed {ι : Type} {snapshots : ι → Option Observation}
    {groups : BulkGroup.State ι} {n : Nat} {mode : BulkGroup.WaitMode}
    (h : BulkGroup.WaitReady groups (completion snapshots) mode n)
    {i : ι} (hi : BulkGroup.Observes groups n i) :
    ∃ o, snapshots i = some o ∧ o.effects.readsDone = true := BulkGroup.waitReady_reads h hi

theorem Observation.extends_refl (a : Observation) : a.Extends a :=
  ⟨rfl, TensorStore.extends_refl _⟩

theorem Observation.extends_trans {a b c : Observation}
    (hab : a.Extends b) (hbc : b.Extends c) : a.Extends c := by
  obtain ⟨sa, ea⟩ := a
  obtain ⟨sb, eb⟩ := b
  obtain ⟨sc, ec⟩ := c
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨h3, h4⟩ := hbc
  cases h1
  cases h3
  exact ⟨rfl, TensorStore.extends_trans h2 h4⟩

theorem snapshotExtends_refl {ι : Type} (a : ι → Option Observation) : SnapshotExtends a a :=
  fun _ old h => ⟨old, h, old.extends_refl⟩

theorem snapshotExtends_trans {ι : Type} {a b c : ι → Option Observation}
    (hab : SnapshotExtends a b) (hbc : SnapshotExtends b c) : SnapshotExtends a c := by
  intro i old h
  obtain ⟨mid, hm, h1⟩ := hab i old h
  obtain ⟨last, hl, h2⟩ := hbc i mid hm
  exact ⟨last, hl, Observation.extends_trans h1 h2⟩

end
end PTX.TensorStore
