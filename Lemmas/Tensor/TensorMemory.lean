-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorMemory
public import Lemmas.Tensor.TensorCopy

@[expose] public section

namespace PTX.TensorCopy
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
    cases hw : ea.write slot with
    | none => simp [hw] at hr
    | some content =>
      have hw' := he.2.1 slot content hw
      change (eb.write slot).bind Content.byte = some value
      rw [hw']
      simpa only [hw, Option.bind_some] using hr

end
end PTX.TensorCopy
