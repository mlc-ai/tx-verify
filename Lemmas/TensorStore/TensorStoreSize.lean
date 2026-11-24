-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorStoreMemory
public import Lemmas.TensorStore.TensorStore

@[expose] public section

section
namespace PTX.TensorStore
noncomputable section

theorem Observation.readByte_mono {a b : Observation} (h : a.Extends b)
    {x y k : Nat} {value : Byte} (hr : readByte a x y k = some value) :
    readByte b x y k = some value := by
  obtain ⟨sa, ea⟩ := a
  obtain ⟨sb, eb⟩ := b
  obtain ⟨hs, he⟩ := h
  cases hs
  unfold readByte at hr ⊢
  cases hslot : TensorTransfer.slotAt sa.descriptor x y k with
  | none => simp [hslot] at hr
  | some slot =>
    simp only [hslot, Option.bind_some] at hr ⊢
    exact he.1 slot value hr

theorem Observation.writeByte_mono {a b : Observation} (h : a.Extends b)
    {x y k : Nat} {value : Byte} (hr : writeByte a x y k = some value) :
    writeByte b x y k = some value := by
  obtain ⟨sa, ea⟩ := a
  obtain ⟨sb, eb⟩ := b
  obtain ⟨hs, he⟩ := h
  cases hs
  unfold writeByte at hr ⊢
  cases hslot : TensorTransfer.slotAt sa.descriptor x y k with
  | none => simp [hslot] at hr
  | some slot =>
    simp only [hslot, Option.bind_some] at hr ⊢
    exact he.2.1 slot value hr

theorem Observation.oldByte_mono {a b : Observation} (h : a.Extends b)
    {x y k : Nat} {value : Byte} (hr : oldByte a x y k = some value) :
    oldByte b x y k = some value := by
  obtain ⟨sa, ea⟩ := a
  obtain ⟨sb, eb⟩ := b
  obtain ⟨hs, he⟩ := h
  cases hs
  unfold oldByte at hr ⊢
  cases hslot : TensorTransfer.slotAt sa.descriptor x y k with
  | none => simp [hslot] at hr
  | some slot =>
    simp only [hslot, Option.bind_some] at hr ⊢
    exact he.2.2.2.2.2 slot value hr

end
end PTX.TensorStore
end

section
namespace PTX.TensorStore
noncomputable section

@[simp] theorem Effects.mem_readSlots {s : Spec} (e : Effects s)
    (slot : TensorTransfer.Slot s.descriptor) :
    slot ∈ e.readSlots ↔ (e.read slot).isSome := by simp [Effects.readSlots]

@[simp] theorem Effects.mem_writeSlots {s : Spec} (e : Effects s)
    (slot : TensorTransfer.Slot s.descriptor) :
    slot ∈ e.writeSlots ↔ (e.write slot).isSome := by simp [Effects.writeSlots]

theorem Extends.readSlots_subset {s : Spec} {a b : Effects s} (h : Extends a b) :
    a.readSlots ⊆ b.readSlots := by
  intro slot hs
  have ha := (Effects.mem_readSlots a slot).mp hs
  cases hr : a.read slot with
  | none => simp [hr] at ha
  | some value => simp [h.1 slot value hr]

theorem Extends.writeSlots_subset {s : Spec} {a b : Effects s} (h : Extends a b) :
    a.writeSlots ⊆ b.writeSlots := by
  intro slot hs
  have ha := (Effects.mem_writeSlots a slot).mp hs
  cases hw : a.write slot with
  | none => simp [hw] at ha
  | some value => simp [h.2.1 slot value hw]

theorem Effects.size_le {s : Spec} (e : Effects s) :
    e.size ≤ 2 * TensorTransfer.bytes s.descriptor + 2 := by
  have hr : e.readSlots.card ≤ Fintype.card (TensorTransfer.Slot s.descriptor) :=
    Finset.card_le_univ _
  have hw : e.writeSlots.card ≤ Fintype.card (TensorTransfer.Slot s.descriptor) :=
    Finset.card_le_univ _
  rw [TensorTransfer.slot_card] at hr hw
  unfold Effects.size
  split_ifs <;> omega

theorem Extends.size_mono {s : Spec} {a b : Effects s} (h : Extends a b) :
    a.size ≤ b.size := by
  have hr := Finset.card_le_card h.readSlots_subset
  have hw := Finset.card_le_card h.writeSlots_subset
  have hn := h.2.2.1
  have hf := h.2.2.2.1
  unfold Effects.size
  split_ifs <;> simp_all <;> omega

/-- A newly recorded source read makes actual progress, even before copy completion. -/
theorem Extends.size_lt_of_read {s : Spec} {a b : Effects s} (h : Extends a b)
    (slot : TensorTransfer.Slot s.descriptor) {value : Byte}
    (ha : a.read slot = none) (hb : b.read slot = some value) : a.size < b.size := by
  have hr : a.readSlots.card < b.readSlots.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨h.readSlots_subset, ?_⟩
    intro he
    have hm : slot ∈ b.readSlots := by simp [hb]
    rw [← he] at hm
    simp [ha] at hm
  have hw := Finset.card_le_card h.writeSlots_subset
  have hn := h.2.2.1
  have hf := h.2.2.2.1
  unfold Effects.size
  split_ifs <;> simp_all <;> omega

/-- A copied-byte write makes progress before full group completion. -/
theorem Extends.size_lt_of_write {s : Spec} {a b : Effects s} (h : Extends a b)
    (slot : TensorTransfer.Slot s.descriptor) {value : Byte}
    (ha : a.write slot = none) (hb : b.write slot = some value) : a.size < b.size := by
  have hw : a.writeSlots.card < b.writeSlots.card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨h.writeSlots_subset, ?_⟩
    intro he
    have hm : slot ∈ b.writeSlots := by simp [hb]
    rw [← he] at hm
    simp [ha] at hm
  have hr := Finset.card_le_card h.readSlots_subset
  have hn := h.2.2.1
  have hf := h.2.2.2.1
  unfold Effects.size
  split_ifs <;> simp_all <;> omega

theorem Extends.size_lt_of_readsDone {s : Spec} {a b : Effects s} (h : Extends a b)
    (ha : a.readsDone = false) (hb : b.readsDone = true) : a.size < b.size := by
  have hr := Finset.card_le_card h.readSlots_subset
  have hw := Finset.card_le_card h.writeSlots_subset
  have hf := h.2.2.2.1
  unfold Effects.size
  split_ifs <;> simp_all <;> omega

theorem Extends.size_lt_of_fullDone {s : Spec} {a b : Effects s} (h : Extends a b)
    (ha : a.fullDone = false) (hb : b.fullDone = true) : a.size < b.size := by
  have hr := Finset.card_le_card h.readSlots_subset
  have hw := Finset.card_le_card h.writeSlots_subset
  have hn := h.2.2.1
  unfold Effects.size
  split_ifs <;> simp_all <;> omega

@[simp] theorem Effects.size_empty (s : Spec) : ({} : Effects s).size = 0 := by
  simp [Effects.size, Effects.readSlots, Effects.writeSlots]

end
end PTX.TensorStore
end
