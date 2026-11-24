-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.TcWrites

@[expose] public section

/-! # The tensor allocation branch of `Unsafe`, from the interface

The kernel's tensor loads and TMA stores keep their boxes inside their maps
(`ThreadFacts.tensor_bounds`, `store_bounds`): no slot of a box is out of bounds, so no transfer
needs the backing of a large-allocation map (`no_tensor_allocation_unsafe`), whatever the maps'
allocation classes. The kernel issues no tensor prefetch (`ThreadFacts.no_tensor_prefetch`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No tensor transfer is out of bounds of a large-allocation map.** -/
theorem no_tensor_allocation_unsafe (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ TensorAllocationUnsafe L mem0 X := by
  rw [tensorAllocationUnsafe_iff]
  rintro (⟨i, a, s, ⟨pc, he⟩, -, hoob, -⟩ | ⟨i, a, s, ⟨pc, he⟩, -, hoob, -⟩ |
    ⟨i, a, s, ⟨pc, he⟩, -⟩)
  · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact ht.tensor_bounds (Frame.lt_of_get hX he) he hσ rfl hoob
  · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact ht.store_bounds (Frame.lt_of_get hX he) he hσ rfl hoob
  · obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he nofun
    exact ht.no_tensor_prefetch (Frame.lt_of_get hX he) he hσ rfl

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
