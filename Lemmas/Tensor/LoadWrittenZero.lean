-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.LoadWritten

@[expose] public section

/-! # A notified zero-fill tensor load has written its byte

A notified tensor load whose descriptor fills with zero and whose element format has a scalar
zero (not `f64`) has written the byte of every slot: a slot with a global source holds a copied
byte, a slot out of bounds holds the zero (`writeByte_of_notified_zero`). The write is then a
memory write of the load's part (`memWrites_of_notified_zero`). -/

namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A notified zero-fill tensor load wrote the byte of every slot.** -/
theorem writeByte_of_notified_zero (hX : Consistent L K A mem0 X) {i : EvId}
    {o : TensorCopy.Observation} {x y z : Nat} {l : Loc} (ho : X.tensor i = some o)
    (hn : o.effects.notified = true) (hl : TensorCopy.writeLoc o.spec x y z = some l)
    (hz : o.spec.descriptor.fill = .zero) (hf : o.spec.descriptor.format ≠ .f64) :
    ∃ v, TensorCopy.writeByte o x y z = some v := by
  have hok := (hX.tensor i o ho).2.1
  obtain ⟨slot, hs, -⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨value, hv⟩ := hok.complete hn slot
  have hw := hok.writes slot value hv
  unfold TensorCopy.writeByte
  rw [hs, Option.bind_some, hv, Option.bind_some]
  cases hso : TensorCopy.source o.spec slot with
  | global a =>
    rw [hso] at hw
    obtain ⟨byte, -, rfl⟩ := hw
    exact ⟨byte, rfl⟩
  | fill mode format byte =>
    rw [hso] at hw
    simp only at hw
    subst hw
    have h2 : mode = o.spec.descriptor.fill ∧ format = o.spec.descriptor.format := by
      unfold TensorCopy.source at hso
      split at hso
      · cases hso
      · cases hso
        exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := h2
    rw [hz]
    unfold TensorCopy.Content.byte TensorCopy.zeroValue
    cases hfm : o.spec.descriptor.format <;> simp_all

/-- **A notified zero-fill tensor load's write of a byte is a memory write.** -/
theorem memWrites_of_notified_zero (hX : Consistent L K A mem0 X) {i : EvId}
    {o : TensorCopy.Observation} {x y z : Nat} {l : Loc} (ho : X.tensor i = some o)
    (hn : o.effects.notified = true) (hl : TensorCopy.writeLoc o.spec x y z = some l)
    (hz : o.spec.descriptor.fill = .zero) (hf : o.spec.descriptor.format ≠ .f64) :
    ∃ b, X.MemWrites (.async i (.write (.load x y z))) { loc := l, size := 1 } [b] := by
  obtain ⟨b, hb⟩ := writeByte_of_notified_zero hX ho hn hl hz hf
  obtain ⟨⟨addr, hIssue⟩, -, -⟩ := hX.tensor i o ho
  exact ⟨b, o, addr, b, ho, hIssue, hl, hb, rfl, rfl, rfl, rfl, rfl, rfl⟩

end
end PTX
