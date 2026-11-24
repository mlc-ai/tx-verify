-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! Tensor map of the Inkling 2 Small relative-attention decode kernel (`_rel_verify_kernel`).

The kernel receives one tensor map, `kv_desc`, by value in the 128-byte `.align 64` parameter
`param_1` (`rel_verify_sm100a.ptx:14`; the PTX takes its address with `mov.b64` and `cvta.param`
at lines 60 and 63). The map is the one `_decode_attention` builds on the paged cache viewed as
`kv_rows`, a 2D bf16 tensor of `num_blocks * page_rows` rows of `slot_stride` elements
(`vllm/models/inkling2/ops/attention.py:1241-1247`, vLLM PR #67325 at
`d664cd1e96052857aea2aa844eeba571c24758b4`). A cache slot is a row; a row holds K of each KV head
followed by its V, 128 elements each, so K of head `h` sits at column `h * head_cols` and V at
column `h * head_cols + 128` (`attention.py:576-578`).

`TensorDescriptor.from_tensor(kv_rows, block, layout)` makes a tiled map with the tensor's
shape and strides (`manifest.json`: `global_dimensions [num_blocks * 64, 512]`, byte stride 1024,
`CU_TENSOR_MAP_DATA_TYPE_BFLOAT16`, `CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE`). TMA dimension 0 is the
contiguous one, so the extents are `(slot_stride, rows)` and the outer byte stride is
`2 * slot_stride`. The Gluon block `[min(page, 128), head_dim] = [64, 128]` has a 256-byte inner
row, which a 128-byte swizzle cannot hold in one box; the compiler splits it into two copies of
the box `(64, 64)`, a 128-byte inner row of 64 bf16 elements (`manifest.json`:
`box_dimensions_ptx_order [64, 64]`, `swizzle_bytes 128`, `logical_block_tma_copies 2`).

The allocation class is a device attribute of the global allocation, so it stays a parameter.
-/
namespace PTX.Kernels.InklingRelDecode
open TensorDescriptor

/-- The map over the `(rows, slot_stride)` bf16 view of the paged cache: box `(64, 64)`, 128-byte
swizzle, zero fill. -/
def mapKv (base slotStride rows : Nat) (cls : AllocationClass) : Descriptor 1 where
  format := .bf16
  base := base
  extent := ![slotStride, rows]
  outerStride := ![2 * slotStride]
  box := ⟨![64, 64], fun _ => 1⟩
  swizzle := .b128
  fill := .zero
  allocationClass := cls

end PTX.Kernels.InklingRelDecode
