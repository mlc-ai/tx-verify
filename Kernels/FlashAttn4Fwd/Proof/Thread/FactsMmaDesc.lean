-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaIssue
public import Kernels.FlashAttn4Fwd.Proof.Interface.MmaSmem
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread
public import Kernels.FlashAttn4Fwd.Proof.Interface.Floats

@[expose] public section

/-! # The MMAs' descriptors

From the MMA of each site (`mma_origin`): a QK MMA (A in shared memory) reads K step `j` of the
Q stage of its block and of the K block of an even ring slot (the uses `0` and `2 + 2 t` of the
item are even, and the item's first use `2 n i` is even), a PV MMA (A in Tensor Memory) K step
`j` of the V block of an odd slot (use `1 + 2 t`); the instruction descriptors are the QK and PV
ones, both `kind::f16` with FP16 inputs and an FP32 accumulator, and the lane masks are zero. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem Mma.slotOf_mod (L : Launch) (i u : Nat) : (Mma.slotOf L i u).val % 2 = u % 2 := by
  simp only [Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
  rw [Nat.mul_assoc]
  generalize Mma.trips L * i = m
  omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat}
include hpre hX ht

/-- **The field `MmaSmemFacts.qk`.** -/
theorem MmaSmemFacts_qk (hi : X.MmaIssue i d s acc mask) (ha : s.aTmem = none) :
    ∃ (st : Fin 2) (sl : Fin 6) (j : Fin 8), sl.val % 2 = 0 ∧
      s.a = kMajorDesc (qStepStart L st j) ∧ s.b = kMajorDesc (kStepStart L sl j) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, -, rfl, -⟩ := mma_origin hpre hX ht hi
  cases hp : Mma.isPv b
  · refine ⟨Mma.mmaStage b, Mma.kSlot L dd b, j, ?_, ?_, ?_⟩
    · unfold Mma.kSlot
      split
      · rw [Mma.slotOf_mod]
      · rw [Mma.slotOf_mod]; omega
    · simp [Mma.mmaSpec, hp]
    · simp [Mma.mmaSpec, hp]
  · rw [Mma.mmaSpec_aTmem, hp] at ha
    cases ha

/-- **The field `MmaSmemFacts.pv`.** -/
theorem MmaSmemFacts_pv (hi : X.MmaIssue i d s acc mask) (ha : s.aTmem.isSome = true) :
    ∃ (sl : Fin 6) (j : Fin 8), sl.val % 2 = 1 ∧ s.b = mnMajorDesc (vStepStart L sl j) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, -, rfl, -⟩ := mma_origin hpre hX ht hi
  cases hp : Mma.isPv b
  · rw [Mma.mmaSpec_aTmem, hp] at ha
    cases ha
  · refine ⟨Mma.vSlot L dd, j, ?_, ?_⟩
    · unfold Mma.vSlot
      rw [Mma.slotOf_mod]
      omega
    · simp [Mma.mmaSpec, hp]

/-- **The field `TcMmaThreadFacts.mma_desc`.** -/
theorem TcMmaThreadFacts_mma_desc (hi : X.MmaIssue i d s acc mask) : mask = List.replicate 8 0 ∧
      (s.aTmem = none → decode .two false .f16 Mma.qkIdesc = some s.descriptor) ∧
      (s.aTmem.isSome = true → decode .two false .f16 Mma.pvIdesc = some s.descriptor) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, -, rfl, -, rfl⟩ := mma_origin hpre hX ht hi
  refine ⟨rfl, fun ha => ?_, fun ha => ?_⟩ <;> rw [Mma.mmaSpec_aTmem] at ha <;>
    rw [Mma.mmaSpec_desc] <;> cases hp : Mma.isPv b <;> simp only [hp] at ha ⊢ <;>
    first
      | exact Mma.qkIdesc_decode
      | exact Mma.pvIdesc_decode
      | cases ha

/-- **The field `TcMmaThreadFacts.mma_collector`**: the kernel's MMAs keep no operand in a
collector buffer (their specification has the default collectors, `Mma.mmaSpec`). -/
theorem TcMmaThreadFacts_mma_collector (hi : X.MmaIssue i d s acc mask) :
    s.collector.a.reuses = false ∧ s.collector.b.reuses = false := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, -, rfl, -⟩ := mma_origin hpre hX ht hi
  unfold Mma.mmaSpec
  split <;> exact ⟨rfl, rfl⟩

/-- **The field `FloatFacts.mma_kind`.** -/
theorem FloatFacts_mma_kind (hi : X.MmaIssue i d s acc mask) :
    s.descriptor.kind = .f16 .f16 .f32 := by
  obtain ⟨g, k⟩ := i
  obtain ⟨dd, b, j, -, -, -, -, -, -, -, rfl, -⟩ := mma_origin hpre hX ht hi
  rcases Mma.mmaSpec_descOk L g dd b j with h | h <;> rw [h] <;> rfl

end
end PTX.Kernels.FlashAttn4Fwd.Proof
