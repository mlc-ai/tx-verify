-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Events

@[expose] public section

namespace PTX
noncomputable section

/-! ## ERR-TENSOR-LARGE-OOB — large allocation-class OOB backing requirement
Statement: When a tensor load, store or prefetch with a tensor map of the large allocation class
  selects an out-of-bounds element, the global range of the device's minimum size that starts at
  the tensor base must be accessible. The execution is unsafe if the range is not accessible or if
  the device's minimum size is not known.

Defs: TensorLargeBacking, TensorBackingMissing, TensorAllocationUnsafe,
  tensorAllocationUnsafe_iff

Source:
- §5.5.3.3: "If a TMA operation performs an out-of-boundary access and the tensor-map object’s
    allocation class (see tensormap.replace ) is large, but the memory range [global_addr,
    global_addr + CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE) is not accessible, the
    behavior is undefined."
- CU_DEVICE_ATTRIBUTE_TENSOR_MAP_LARGE_ALLOC_MIN_SIZE

Direction: reading

Applies: Supported tiled tensor loads, stores and prefetches, with the actual tensor-map allocation
  class

Premises: An operation selects an out-of-bounds element (`TensorHasOob`, THREAD-TENSOR-TRANSFER-MAP)
  and the map class is large.

Effect: Safety rejects missing backing or an unknown device attribute. Ordinary accessed-byte
  allocation checks still apply independently. Mem0 allocation represents storage accessible for
  the kernel lifetime. Unknown byte contents are sufficient here, since this requirement concerns
  accessibility only. The minimum size is launch/device data, separate from any tile size or kernel
  assumption of successful accesses. EXT-LAUNCH must match it and the class to the actual
  hardware attribute and host-created descriptor. Device-side map updates are unsupported. A load,
  a store and a prefetch issue (THREAD-TENSOR-PREFETCH) are each checked with the elements they
  select, under the same condition.
-/
/-- The global range of the device's minimum large-allocation size that starts at `base` is
allocated in the launch memory. -/
def TensorLargeBacking (L : Launch) (mem0 : Mem0) (base : Nat) : Prop :=
  ∃ size, L.tensorLargeAllocMinBytes = some size ∧
    ∀ k < size, mem0 ⟨.global, 0, base + k⟩ ≠ none

/-- An access that selects the elements of `origin` and `rows` through the map `d` has a large-class
map, selects an out-of-bounds element and has no accessible range behind the tensor base. A tensor
load and a store (`TensorBox`) and a prefetch record these three fields. -/
def TensorBackingMissing (L : Launch) (mem0 : Mem0) {outer : Nat}
    (d : TensorDescriptor.Descriptor outer) (origin : Fin (outer + 1) → Int)
    (rows : Option (Fin 4 → Int)) : Prop :=
  d.allocationClass = .large ∧ TensorHasOob d origin rows ∧ ¬ TensorLargeBacking L mem0 d.base

/-- Some tensor load, store or prefetch with a large-class map selects an out-of-bounds element and
the range behind the tensor base is not accessible. -/
def TensorAllocationUnsafe (L : Launch) (mem0 : Mem0) (X : Execution) : Prop :=
  ∃ i, (∃ address s, X.TensorIssue i address s ∧
      TensorBackingMissing L mem0 s.descriptor s.origin s.rows) ∨
    (∃ address s, X.TensorStoreIssue i address s ∧
      TensorBackingMissing L mem0 s.descriptor s.origin s.rows) ∨
    (∃ address s, X.TensorPrefetchIssue i address s ∧
      TensorBackingMissing L mem0 s.descriptor s.origin s.rows)

/-- Per-form lemma: the former form of `TensorAllocationUnsafe`, one disjunct for each of a tensor
load, a tensor store and a tensor prefetch. -/
theorem tensorAllocationUnsafe_iff (L : Launch) (mem0 : Mem0) (X : Execution) :
    TensorAllocationUnsafe L mem0 X ↔
    (∃ i address s, X.TensorIssue i address s ∧ s.descriptor.allocationClass = .large ∧
      TensorHasOob s.descriptor s.origin s.rows ∧ ¬ TensorLargeBacking L mem0 s.descriptor.base) ∨
    (∃ i address s, X.TensorStoreIssue i address s ∧ s.descriptor.allocationClass = .large ∧
      TensorHasOob s.descriptor s.origin s.rows ∧ ¬ TensorLargeBacking L mem0 s.descriptor.base) ∨
    (∃ i address s, X.TensorPrefetchIssue i address s ∧ s.descriptor.allocationClass = .large ∧
      TensorHasOob s.descriptor s.origin s.rows ∧
        ¬ TensorLargeBacking L mem0 s.descriptor.base) := by
  unfold TensorAllocationUnsafe TensorBackingMissing
  constructor
  · rintro ⟨i, h | h | h⟩
    · exact .inl (by obtain ⟨a, s, hi, h⟩ := h; exact ⟨i, a, s, hi, h⟩)
    · exact .inr (.inl (by obtain ⟨a, s, hi, h⟩ := h; exact ⟨i, a, s, hi, h⟩))
    · exact .inr (.inr (by obtain ⟨a, s, hi, h⟩ := h; exact ⟨i, a, s, hi, h⟩))
  · rintro (⟨i, a, s, hi, h⟩ | ⟨i, a, s, hi, h⟩ | ⟨i, a, s, hi, h⟩)
    · exact ⟨i, .inl ⟨a, s, hi, h⟩⟩
    · exact ⟨i, .inr (.inl ⟨a, s, hi, h⟩)⟩
    · exact ⟨i, .inr (.inr ⟨a, s, hi, h⟩)⟩

end
end PTX
