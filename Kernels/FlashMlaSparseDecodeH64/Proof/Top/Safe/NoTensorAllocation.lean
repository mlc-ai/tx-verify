-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef

@[expose] public section

/-! # ERR-TENSOR-LARGE-OOB: tensor accesses have their backing

The safety class of Core's `Unsafe` this file owns (`TensorAllocationUnsafe`). No tensor prefetch
is issued (`noTensorPrefetch`); a tensor load is a query load or a gather through a cache map
(`tensor_load_map`), a tensor store goes through the output map (`tensor_store_map`). A gather's
map is the main or the extra cache's, whose large class has its backing in `Pre`
(`kvBacking`, `extraKvBacking`).

The query loads and the output stores have their box origin (`tensor_load_origin`,
`tensor_store_origin`), which is inside the tensor (`tile_inBounds`), so they select no
out-of-bounds element. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TENSOR-LARGE-OOB**: tensor accesses have their backing. -/
theorem Safe.noTensorAllocation (hp : Pre P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ TensorAllocationUnsafe L mem0 X := by
  rintro ⟨⟨g, k⟩, ⟨a, s, hi, hBad⟩ | ⟨a, s, hi, hBad⟩ | ⟨a, s, hi, -⟩⟩
  · rcases tensor_load_map hp hX hFw hi with hq | ⟨d0, hd, hK⟩
    · obtain ⟨hrows, c, hc, hor⟩ := tensor_load_origin hp hX hFw hi hq
      have hlt := ctaid_lt hp g
      have hO := hBad.2.1
      rw [hrows] at hO
      exact tile_inBounds hq (x := 64 * c) (by omega) hlt.1 hlt.2 hor hO
    · obtain ⟨hc, -, hb⟩ := hBad
      have hcls : s.descriptor.allocationClass = d0.allocationClass := by rw [hd]; rfl
      have hbase : s.descriptor.base = d0.base := by rw [hd]; rfl
      have key : ∀ {n : Nat} {y : TensorDescriptor.Descriptor n},
          (⟨s.outer, d0⟩ : Σ n, TensorDescriptor.Descriptor n) = ⟨n, y⟩ →
          s.descriptor.allocationClass = y.allocationClass ∧ s.descriptor.base = y.base :=
        fun h => ⟨hcls.trans (congrArg (fun p : Σ n, TensorDescriptor.Descriptor n =>
          p.2.allocationClass) h), hbase.trans (congrArg (fun p : Σ n, TensorDescriptor.Descriptor n
            => p.2.base) h)⟩
      rcases hK with hK | ⟨hex, hK⟩
      · obtain ⟨h1, h2⟩ := key hK
        apply hb
        rw [h2]
        exact hp.kvBacking (h1.symm.trans hc)
      · obtain ⟨h1, h2⟩ := key hK
        apply hb
        rw [h2]
        exact hp.extraKvBacking hex (h1.symm.trans hc)
  · obtain ⟨hw, hrows, c, hc, -, hor⟩ := tensor_store_origin hp hX hFw hnu hi
    have hlt := ctaid_lt hp g
    have hO := hBad.2.1
    rw [hrows] at hO
    have hcol : [0, 64, 256, 320].getD c 0 ≤ 320 := by
      interval_cases c <;> simp
    exact tile_inBounds (tensor_store_map hp hX hFw hi) (x := 128 * MbarRow.warp L g +
      [0, 64, 256, 320].getD c 0) (by omega) hlt.1 hlt.2 hor hO
  · exact noTensorPrefetch hX hi

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
