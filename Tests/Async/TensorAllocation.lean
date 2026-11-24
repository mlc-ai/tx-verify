-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tensor.TensorTile
public import Core.Async.Tensor.TensorAllocation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic

namespace PTX.Tests.TensorAllocation
noncomputable section

private def d (c : TensorDescriptor.AllocationClass) : TensorDescriptor.Descriptor 1 :=
  ⟨.f16, 4096, ![8, 1], ![16], ⟨![8, 1], ![1, 1]⟩, .b128, .zero, c⟩
private def L : Launch := {
  grid := 1, block := 1, params := fun _ => none, tensorLargeAllocMinBytes := some 64 }
private def source (c : TensorDescriptor.AllocationClass) : TensorCopy.Spec :=
  ⟨⟨1, d c, ![0, 1], ⟨.shared, 0, 128⟩, none⟩, ⟨.shared, 0, 64⟩, true, .one⟩
private def target (c : TensorDescriptor.AllocationClass) : TensorStore.Spec :=
  ⟨⟨1, d c, ![0, 1], ⟨.shared, 0, 128⟩, none⟩, none⟩
private def prefetch (c : TensorDescriptor.AllocationClass) : TensorPrefetch.Spec :=
  ⟨1, d c, ![0, 1], none⟩
private def X (c : TensorDescriptor.AllocationClass) : Execution := {
  tr := fun _ => [⟨0, .tensorIssue 1024 (source c)⟩, ⟨1, .tensorStore 2048 (target c)⟩,
    ⟨2, .tensorPrefetch 3072 (prefetch c)⟩],
  rf := fun _ _ => none }

private theorem oob (c : TensorDescriptor.AllocationClass) : TensorHasOob (d c) ![0, 1] none := by
  refine ⟨⟨⟨0, by norm_num [TensorTile.count, TensorTile.step, d]⟩,
    ⟨0, by norm_num [TensorTile.rows, TensorTile.rowsOf, TensorTile.count, TensorTile.step, d]⟩, ⟨0,
      by change 0 < 2; decide⟩⟩, ?_⟩
  intro h
  have h1 := h 1
  norm_num [TensorDescriptor.geometry, TensorTransfer.coord, TensorTile.coord, TensorTransfer.index,
    TensorTile.indexOf_two, d] at h1

private theorem no_backing : ¬ TensorLargeBacking L (fun _ => none) 4096 := by
  rintro ⟨n, hn, hm⟩
  have he : n = 64 := by cases hn; rfl
  subst n
  exact hm 0 (by decide) rfl

-- Both copy directions and a prefetch enforce the same allocation-class condition.
example : TensorAllocationUnsafe L (fun _ => none) (X .large) :=
  ⟨(0, 0), .inl ⟨1024, source .large, ⟨0, rfl⟩, rfl, oob .large, no_backing⟩⟩
example : TensorAllocationUnsafe L (fun _ => none) (X .large) :=
  ⟨(0, 1), .inr (.inl ⟨2048, target .large, ⟨1, rfl⟩, rfl, oob .large, no_backing⟩)⟩
example : TensorAllocationUnsafe L (fun _ => none) (X .large) :=
  ⟨(0, 2), .inr (.inr ⟨3072, prefetch .large, ⟨2, rfl⟩, rfl, oob .large, no_backing⟩)⟩

-- Allocation suffices; initial values need not be known or initialized.
example : TensorLargeBacking L (fun _ => some none) 4096 :=
  ⟨64, rfl, fun _ _ => Option.some_ne_none _⟩

-- A single missing byte in the required contiguous range is enough to fail.
example : ¬ TensorLargeBacking L
    (fun l => if l.addr = 4096 + 63 then none else some none) 4096 := by
  rintro ⟨n, hn, hm⟩
  have he : n = 64 := by cases hn; rfl
  subst n
  exact hm 63 (by decide) (by simp)

-- No guessed device minimum is accepted when launch metadata is absent.
example (mem0 : Mem0) :
    ¬ TensorLargeBacking { L with tensorLargeAllocMinBytes := none } mem0 4096 := by
  rintro ⟨n, hn, _⟩
  cases hn

-- This is only the extra large-class obligation, not ordinary access allocation.
example (Y : Execution) (mem0 : Mem0)
    (hl : ∀ i a s, Y.TensorIssue i a s → s.descriptor.allocationClass = .small)
    (hs : ∀ i a s, Y.TensorStoreIssue i a s → s.descriptor.allocationClass = .small)
    (hp : ∀ i a s, Y.TensorPrefetchIssue i a s → s.descriptor.allocationClass = .small) :
    ¬ TensorAllocationUnsafe L mem0 Y := by
  rintro ⟨i, ⟨a, s, hi, hc, _⟩ | ⟨a, s, hi, hc, _⟩ | ⟨a, s, hi, hc, _⟩⟩
  · rw [hl i a s hi] at hc; cases hc
  · rw [hs i a s hi] at hc; cases hc
  · rw [hp i a s hi] at hc; cases hc

-- Large maps with entirely in-bounds selections have no extra range obligation.
example (Y : Execution) (mem0 : Mem0)
    (hl : ∀ i a s, Y.TensorIssue i a s → ¬ TensorHasOob s.descriptor s.origin s.rows)
    (hs : ∀ i a s, Y.TensorStoreIssue i a s → ¬ TensorHasOob s.descriptor s.origin s.rows)
    (hp : ∀ i a s, Y.TensorPrefetchIssue i a s → ¬ TensorHasOob s.descriptor s.origin s.rows) :
    ¬ TensorAllocationUnsafe L mem0 Y := by
  rintro ⟨i, ⟨a, s, hi, _, ho, _⟩ | ⟨a, s, hi, _, ho, _⟩ | ⟨a, s, hi, _, ho, _⟩⟩
  · exact hl i a s hi ho
  · exact hs i a s hi ho
  · exact hp i a s hi ho

end
end PTX.Tests.TensorAllocation
