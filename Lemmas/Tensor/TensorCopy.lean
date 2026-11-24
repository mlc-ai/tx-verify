-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorTransfer

@[expose] public section

namespace PTX

/-- A tensor transfer's source byte is global memory. -/
theorem TensorTransfer.sourceLoc_global {outer : Nat} {d : TensorDescriptor.Descriptor outer}
    {origin : Fin (outer + 1) → Int} {rows : Option (Fin 4 → Int)} {x y k : Nat} {l : Loc}
    (h : TensorTransfer.sourceLoc d origin rows x y k = some l) : l.space = .global := by
  unfold TensorTransfer.sourceLoc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, -, _, -, rfl⟩ := h
  rfl

theorem TensorBox.globalAddress_out_of_bounds (b : TensorBox)
    (slot : TensorTransfer.Slot b.descriptor)
    (h : ¬ TensorAddress.InBounds (TensorDescriptor.geometry b.descriptor)
      (TensorTransfer.coord b.descriptor b.origin b.rows slot)) :
    b.globalAddress slot = none := by
  unfold globalAddress TensorTransfer.globalAddress TensorAddress.lookup
  split_ifs with hc
  · exact False.elim (h hc.1)
  · rfl

namespace TensorCopy
noncomputable section

/-- A tensor load's source location, by the source of its slot. -/
theorem readLoc_source (s : Spec) (x y k : Nat) :
    readLoc s x y k = (TensorTransfer.slotAt s.descriptor x y k).bind fun slot =>
      match source s slot with
      | .global address => some ⟨.global, 0, address⟩
      | .fill .. => none := by
  unfold readLoc TensorTransfer.sourceLoc
  cases TensorTransfer.slotAt s.descriptor x y k with
  | none => rfl
  | some slot =>
    simp only [Option.bind_eq_bind, Option.bind_some, source, TensorBox.globalAddress]
    cases TensorTransfer.globalAddress s.descriptor s.origin s.rows slot <;> rfl

theorem source_out_of_bounds (s : Spec) (slot : TensorTransfer.Slot s.descriptor)
    (h : ¬ TensorAddress.InBounds (TensorDescriptor.geometry s.descriptor)
      (TensorTransfer.coord s.descriptor s.origin s.rows slot)) :
    source s slot = .fill s.descriptor.fill s.descriptor.format slot.2.2.val := by
  simp only [source, TensorBox.globalAddress_out_of_bounds s.toTensorBox slot h]

theorem missing_write_not_complete {s : Spec} {e : Effects s} (h : CopyOk s e)
    (slot : TensorTransfer.Slot s.descriptor) (hw : e.write slot = none) :
    e.notified = false := by
  cases hn : e.notified with
  | false => rfl
  | true =>
    obtain ⟨value, hv⟩ := h.complete hn slot
    rw [hw] at hv
    cases hv

theorem extends_refl {s : Spec} (e : Effects s) : Extends e e :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun h => h⟩

theorem extends_trans {s : Spec} {a b c : Effects s}
    (hab : Extends a b) (hbc : Extends b c) : Extends a c :=
  ⟨fun slot value h => hbc.1 slot value (hab.1 slot value h),
   fun slot value h => hbc.2.1 slot value (hab.2.1 slot value h),
   fun h => hbc.2.2 (hab.2.2 h)⟩

theorem Observation.extends_refl (a : Observation) : a.Extends a :=
  ⟨rfl, TensorCopy.extends_refl _⟩

theorem Observation.extends_trans {a b c : Observation}
    (hab : a.Extends b) (hbc : b.Extends c) : a.Extends c := by
  obtain ⟨sa, ea⟩ := a
  obtain ⟨sb, eb⟩ := b
  obtain ⟨sc, ec⟩ := c
  obtain ⟨h1, h2⟩ := hab
  obtain ⟨h3, h4⟩ := hbc
  cases h1
  cases h3
  exact ⟨rfl, TensorCopy.extends_trans h2 h4⟩

theorem snapshotExtends_refl {ι : Type} (a : ι → Option Observation) : SnapshotExtends a a :=
  fun _ old h => ⟨old, h, old.extends_refl⟩

theorem snapshotExtends_trans {ι : Type} {a b c : ι → Option Observation}
    (hab : SnapshotExtends a b) (hbc : SnapshotExtends b c) : SnapshotExtends a c := by
  intro i old h
  obtain ⟨mid, hm, h1⟩ := hab i old h
  obtain ⟨last, hl, h2⟩ := hbc i mid hm
  exact ⟨last, hl, Observation.extends_trans h1 h2⟩

end
end TensorCopy
end PTX
