-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.SyncCluster

@[expose] public section

/-! # `TensorUnsafe`, from the thread facts

A tensor load is a loader's load of an input map's box into its CTA, completing on its slot's full
barrier in the cluster's leader CTA (`ThreadFacts.tensor_issue`). That barrier lies in the CTA's
shared allocation and was initialized and published to the loader, as in the CLC branches
(`tensor_mbar_allocated`, `tensor_mbar_published`, used by the mbarrier branches of `Unalloc` and
`MbarUninit`). Every byte the copy writes is a representable byte: the input maps fill
out-of-bounds elements with zero of a half-precision format, so the fill's byte is a defined one
(`no_tensorUnsafe`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A launched thread's CTA is below the grid. -/
theorem cta_lt_grid (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : g / L.block < L.grid :=
    by
  have hb : 0 < L.block := by rw [hpre.block]; norm_num
  exact (Nat.div_lt_iff_lt_mul hb).mpr hg

/-- The source of a tensor issue: a loader's load at a slot, with the slot's full barrier in the
cluster's leader CTA. -/
theorem tensor_source (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {i : EvId}
    {address : Nat} {s : TensorCopy.Spec} (hi : X.TensorIssue i address s) :
    ∃ (l : Loader.D) (b : Fin 8), Frame.stateAt (code L) X i.1 i.2 =
      some (some (.inr (.loader l))) ∧
      i.1 < L.threads ∧ s.mbar = InputRing.fullLoc L (i.1 / L.block / 2) (InputRing.slotOf b) := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨l, b, j, rfl, -, hm, -⟩ := ht.tensor_issue hg he hσ rfl
  exact ⟨l, b, hσ, hg, hm⟩

/-- Every byte a tensor load writes is a representable byte. -/
theorem write_byte (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {i : EvId} {observation : TensorCopy.Observation}
    (hobs : X.tensor i = some observation) {slot : TensorTransfer.Slot observation.spec.descriptor}
    {content : TensorCopy.Content} (hw : observation.effects.write slot = some content) :
    content.byte ≠ none := by
  obtain ⟨⟨address, hi⟩, hok, -, -⟩ := hX.tensor i observation hobs
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
  obtain ⟨l, b, j, rfl, -, -, ⟨base, cls, origin, hsp, -⟩, -⟩ := ht.tensor_issue hg he hσ rfl
  have hfill : observation.spec.descriptor.fill = .zero := by rw [hsp]; rfl
  have hfmt : observation.spec.descriptor.format = .f16 := by rw [hsp]; rfl
  have hwr := hok.writes slot content hw
  unfold TensorCopy.source at hwr
  rcases hga : observation.spec.globalAddress slot with _ | address
  · simp only [hga] at hwr
    rw [hwr]
    simp only [TensorCopy.Content.byte, hfill]
    intro h
    have hz : TensorCopy.zeroValue observation.spec.descriptor.format ≠ none := by
      rw [hfmt]
      simp [TensorCopy.zeroValue]
    exact hz (Option.map_eq_none_iff.mp h)
  · simp only [hga] at hwr
    obtain ⟨byte, -, rfl⟩ := hwr
    simp [TensorCopy.Content.byte]

/-- **No tensor load is unsafe.** -/
theorem no_tensorUnsafe (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ TensorUnsafe X := by
  rintro ⟨i, observation, slot, content, hobs, hw, hbyte⟩
  exact write_byte hX ht hobs hw hbyte

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
