-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Tensor maps of the FlashMLA SM100 sparse decode head64 kernel (`v41_h64_no_split`).

The kernel receives the four maps by value in the `__grid_constant__` `TmaParams` object, the
1024-byte `.align 128` parameter `param_1` (`v41_h64_no_split_plain.ptx:30`). The used descriptors
sit at `param_1 + 128` (Q), `+512` (O), `+768` (the KV cache) and `+896` (the extra KV cache)
(PTX lines 3709, 2114 and 4345-4353). The host builds Q and O with CuTe's `make_tma_copy` and the
KV maps with `make_kv_quant_part_tensor_map`, which calls `ku::make_tensor_map` and
`cuTensorMapEncodeTiled` (deepseek-ai/FlashMLA 395cb3af
`csrc/cuda_kernels/sm100/decode/sparse/head64/kernel.cuh:683-715`,
`csrc/cuda_kernels/sm100/kv_cache_utils.cuh:42-61`,
`csrc/3rdparty/kerutils/include/kerutils/host/host.h:95-146`).

## Q and O

`params.q` is a bf16 `[b, s_q, h_q, d_qk]` tensor with unit last stride and `params.out` is bf16
`[b, s_q, h_q, d_v]` (`csrc/params.h:132-140`). The host views them with the CuTe layouts
`(h_q, D_Q, s_q, b)` and element strides `(stride_q_h_q, 1, stride_q_s_q, stride_q_b)`, and
`(stride_o_h_q, 1, stride_o_s_q, stride_o_b)` respectively (`kernel.cuh:683-707`); the strides are
element counts, not bytes (`csrc/params.h:148-153`). TMA dimension 0 is the contiguous head
dimension, so the map extents are `(512, 64, s_q, b)`, with `D_Q = D_V = 512` (`config.h:40-42`)
and `h_q = 64` forced by the public dispatch (`csrc/api/sparse_decode.cpp:76`). The outer byte
strides are twice the host element strides. (When `s_q == 1 && b > 1` the host sets
`stride_q_s_q = stride_q_b`, `csrc/api/sparse_decode.cpp:109-114`; that is a launch fact about the
strides, not about the map.)

The box is `(64, 64, 1, 1)` for both. The PTX Q loads are eight rank-4 copies with dimension-0
coordinates `0, 64, ..., 448`, dimension-1 coordinate `0` and dimensions 2, 3 the query and batch
indices, each into its own 8192-byte shared frame, with `expect_tx` 65536
(`v41_h64_no_split_plain.ptx:3714-3756`): eight boxes of 64 head-dimension elements by 64 rows of
bf16. The O stores are four unrolled rank-4 copies issued by each of the two epilogue warps (eight
stores), with dimension-0 coordinates `64 * block` over the eight 64-column tiles of `d_v` and the
same last two coordinates (lines 2488, 2861, 3233, 3606). Sixty-four bf16 elements are one
128-byte swizzle span, so the swizzle is `.b128`; the shared tiles are
`UMMA::Layout_K_SW128_Atom<bf16>` at 64 rows (`config.h:87-104`).

## KV and extra KV

The KV cache is a paged cache of token rows of `BYTES_PER_TOKEN = 528` bytes: 512 e4m3 bytes, one
per `d_qk` dimension, followed by 16 ue8m0 scale bytes, one per 32 dimensions
(`csrc/cuda_kernels/kv_cache_format.h:5-20`). `KVCachePart<KVCacheFormat<V41>, 1, 0>` has
`RAW_TOKEN_OFFSET = 0` and `RAW_TOKEN_DATA_BYTES = 528` (`kv_cache_format.h:24-35`), so the map's
base is `params.kv` and its dimension 0 is the token row in `.u32` words, 132 = 528 / 4.
Dimension 1 flattens the paged cache into token rows: block `i`'s tokens start `block_stride`
bytes apart and successive tokens 528 bytes apart, so the extent is
`num_blocks * (block_stride / 528)`; the index warp computes a token's row as
`block_idx * (block_stride / 528) + idx_in_block` (`kernel.cuh:540-541`, `:584`). The outer byte
stride is the 528-byte token row, which the host asserts (`row_stride_bytes == TOKEN_STRIDE`)
together with `block_stride % 528 == 0` (`kv_cache_utils.cuh:50-51`).

The box is 144 words = 576 bytes, not 528: the shared row is
`RAW_TOKEN_SMEM_STRIDE = QUANT_BYTES + 64 = 576` bytes (`config.h:54-57`), the 528-byte token row
plus 48 bytes of padding that keep adjacent rows 64 bytes apart modulo 128 bytes for the
dequantizer's `LDS.64`; the padding also makes four rows (2304 bytes) 128-byte aligned
(`config.h:59-60`). The last twelve words of the box lie past the extent's 132, so the TMA
zero-fills them; the map's fill is `.zero`. One gather4 carries four token rows into four
consecutive 576-byte shared rows, so its transfer box is `Descriptor.fourRows` of this map (box
dimension 1 becomes 4 with unit traversal). The PTX issues sixteen gather4 loads with dimension-0
coordinate `0` and four row coordinates each, and `expect_tx` 36864 = 64 x 576 (lines
4357-4452).

The host passes `CU_TENSOR_MAP_DATA_TYPE_UINT32` ("UINT32 keeps the TMA box dimension <= 256",
`kv_cache_utils.cuh:39`), `CU_TENSOR_MAP_SWIZZLE_NONE`, `CU_TENSOR_MAP_L2_PROMOTION_L2_128B` (the
function's default argument) and the default `CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE`
(`kv_cache_utils.cuh:53-61`, `csrc/3rdparty/kerutils/include/kerutils/host/host.h:95-105`). A
four-byte element makes the 576-byte inner box a multiple of 16, and with no swizzle no swizzle
width bounds it.

The extra KV map is built by the same function for `params.extra_kv`, `params.extra_num_blocks`
and `params.stride_extra_kv_block` (`kernel.cuh:712-714`). In this instantiation the extra format
is also V41, so its row and box are the same 528 and 576 bytes; the FP4 extra cache (288-byte
rows, 72-word box) is a different instantiation and is not encoded here.

## Parameters and launch obligations

The out-of-bounds fill and the allocation class of Q and O stay parameters. The host's descriptors
set the fill to `CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE` (zero fill) and the L2 promotion to
`CU_TENSOR_MAP_L2_PROMOTION_L2_128B`
(`csrc/3rdparty/cutlass/include/cute/atom/copy_traits_sm90_tma.hpp:1034-1035`); with `h_q = 64`
and the kernel's coordinates every box lies inside the extents, so the fill value is not observed.
The allocation class is a device attribute of the global allocation, not an encoding argument, so
it is a parameter of every map. L2 promotion is a cache hint with no memory-model effect and is
not represented.

What remains a launch obligation: the 16-byte alignment of each base address (asserted for the KV
caches at `kv_cache_utils.cuh:49`, asserted by CuTe for Q and O), the host strides whose byte
forms are multiples of 16 and below 2^40, `0 < s_q`, `0 < b`, `stride_kv_row = 528`,
`block_stride` a multiple of 528 and `num_blocks * (block_stride / 528) <= INT32_MAX`
(`kv_cache_utils.cuh:50-52`), and the coordinates the kernel passes: the head-dimension tile index
for Q and O, the query and batch block indices, and the per-token KV row (or -1 for an invalid
token, which the TMA zero-fills).
-/
namespace PTX.Kernels.FlashMlaSparseDecodeH64
open TensorDescriptor

/-- A rank-4 bf16 map over the `(h_q, 512, s_q, b)` view of `q` or `out`, with the head dimension
first: box `64 x 64 x 1 x 1`, 128-byte swizzle. `sH`, `sS` and `sB` are the host element strides
of the head, query and batch dimensions; bf16 elements are two bytes, so the map's outer byte
strides are twice those values. -/
def encodeTiled (base sH sS sB sq b : Nat) (fill : Fill) (cls : AllocationClass) :
    Descriptor 3 where
  format := .bf16
  base := base
  extent := ![512, 64, sq, b]
  outerStride := ![2 * sH, 2 * sS, 2 * sB]
  box := ⟨![64, 64, 1, 1], fun _ => 1⟩
  swizzle := .b128
  fill := fill
  allocationClass := cls

/-- Q: the strides are the host's `params.stride_q_h_q`, `params.stride_q_s_q` and
`params.stride_q_b`. -/
def mapQ (base sH sS sB sq b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sH sS sB sq b fill cls

/-- O: the strides are the host's `params.stride_o_h_q`, `params.stride_o_s_q` and
`params.stride_o_b`. -/
def mapO (base sH sS sB sq b : Nat) (fill : Fill) (cls : AllocationClass) : Descriptor 3 :=
  encodeTiled base sH sS sB sq b fill cls

theorem encodeTiled_valid {base sH sS sB sq b : Nat} {fill : Fill} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hH : 2 * sH % 16 = 0 ∧ 2 * sH < 2 ^ 40)
    (hS : 2 * sS % 16 = 0 ∧ 2 * sS < 2 ^ 40)
    (hB : 2 * sB % 16 = 0 ∧ 2 * sB < 2 ^ 40)
    (hSq : 0 < sq ∧ sq ≤ 2 ^ 32) (hBatch : 0 < b ∧ b ≤ 2 ^ 32) :
    Valid (encodeTiled base sH sS sB sq b fill cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [encodeTiled, Format.bytes],
    .inr (by simp [encodeTiled, Format.bytes, TensorTile.swizzleWidth]), fun _ => rfl, rfl⟩
  · fin_cases i
    · simp [encodeTiled]
    · simp [encodeTiled]
    · simpa [encodeTiled] using hSq
    · simpa [encodeTiled] using hBatch
  · fin_cases i
    · simpa [encodeTiled] using hH
    · simpa [encodeTiled] using hS
    · simpa [encodeTiled] using hB
  · fin_cases i <;> simp [encodeTiled]
  · fin_cases i <;> simp [encodeTiled]

theorem mapQ_valid {base sH sS sB sq b : Nat} {fill : Fill} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hH : 2 * sH % 16 = 0 ∧ 2 * sH < 2 ^ 40)
    (hS : 2 * sS % 16 = 0 ∧ 2 * sS < 2 ^ 40)
    (hB : 2 * sB % 16 = 0 ∧ 2 * sB < 2 ^ 40)
    (hSq : 0 < sq ∧ sq ≤ 2 ^ 32) (hBatch : 0 < b ∧ b ≤ 2 ^ 32) :
    Valid (mapQ base sH sS sB sq b fill cls) :=
  encodeTiled_valid hBase hH hS hB hSq hBatch

theorem mapO_valid {base sH sS sB sq b : Nat} {fill : Fill} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hH : 2 * sH % 16 = 0 ∧ 2 * sH < 2 ^ 40)
    (hS : 2 * sS % 16 = 0 ∧ 2 * sS < 2 ^ 40)
    (hB : 2 * sB % 16 = 0 ∧ 2 * sB < 2 ^ 40)
    (hSq : 0 < sq ∧ sq ≤ 2 ^ 32) (hBatch : 0 < b ∧ b ≤ 2 ^ 32) :
    Valid (mapO base sH sS sB sq b fill cls) :=
  encodeTiled_valid hBase hH hS hB hSq hBatch

/-- A rank-2 `.u32` map over the flattened paged KV cache: dimension 0 is one 528-byte token row
(132 words), dimension 1 is `numBlocks * (blockStride / 528)` token rows 528 bytes apart, and the
box is one 576-byte shared row (144 words) by one row. -/
def encodeKv (base numBlocks blockStride : Nat) (cls : AllocationClass) : Descriptor 1 where
  format := .u32
  base := base
  extent := ![132, numBlocks * (blockStride / 528)]
  outerStride := ![528]
  box := ⟨![144, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- The KV cache map: `params.kv` with `params.num_blocks` and `params.stride_kv_block`. -/
def mapKv (base numBlocks blockStride : Nat) (cls : AllocationClass) : Descriptor 1 :=
  encodeKv base numBlocks blockStride cls

/-- The extra KV cache map: `params.extra_kv` with `params.extra_num_blocks` and
`params.stride_extra_kv_block`. -/
def mapExtraKv (base numBlocks blockStride : Nat) (cls : AllocationClass) : Descriptor 1 :=
  encodeKv base numBlocks blockStride cls

theorem encodeKv_valid {base numBlocks blockStride : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hRows : 0 < numBlocks * (blockStride / 528) ∧
      numBlocks * (blockStride / 528) ≤ 2 ^ 32) :
    Valid (encodeKv base numBlocks blockStride cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [encodeKv, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [encodeKv]
    · simpa [encodeKv] using hRows
  · fin_cases i; simp [encodeKv]
  · fin_cases i <;> simp [encodeKv]
  · fin_cases i <;> simp [encodeKv]

theorem mapKv_valid {base numBlocks blockStride : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hRows : 0 < numBlocks * (blockStride / 528) ∧
      numBlocks * (blockStride / 528) ≤ 2 ^ 32) :
    Valid (mapKv base numBlocks blockStride cls) :=
  encodeKv_valid hBase hRows

theorem mapExtraKv_valid {base numBlocks blockStride : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0)
    (hRows : 0 < numBlocks * (blockStride / 528) ∧
      numBlocks * (blockStride / 528) ≤ 2 ^ 32) :
    Valid (mapExtraKv base numBlocks blockStride cls) :=
  encodeKv_valid hBase hRows

end PTX.Kernels.FlashMlaSparseDecodeH64
