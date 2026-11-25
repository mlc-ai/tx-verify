-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorDescriptor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Tensor maps of the FlashKDA forward recurrence kernel (packed batch, FP32 state).

A tensor map (TMA descriptor) tells the hardware copy engine how a tensor lies in global memory
and which box of it one copy moves. The kernel `_flash_kda_fwd_recurrence`
(`csrc/smxx/fwd_kernel2.cuh:137`) receives eleven of them by value: each of its parameters
0 to 10 is a CuTe `TiledCopy` object, a 256-byte `.param .align 128` object whose first 128
bytes are the descriptor. The host builds them in `launch_fwd` (`csrc/smxx/fwd_launch.cu`) with
`make_tma_copy(op, gmem_tensor, smem_layout)`; CuTe turns each into one call of
`cuTensorMapEncodeTiled` (`cute/atom/copy_traits_sm90_tma.hpp:1041`).

Below, `H` is the number of heads, `N` the number of sequences, `T` the total number of tokens
of the packed batch (`T_total`) and `total_tiles` the workspace capacity per head. Dimension 0
of a map is the innermost one; its stride is the element size and is not stored.

## How CuTe orders the dimensions

CuTe takes the map's dimensions from the shared-memory layout of one copy
(`construct_tma_gbasis`): dimension 0 is the global mode that is contiguous in shared memory,
then the next shared mode, and the global modes the box does not span are appended as
dimensions of box size 1. The extents and byte strides are those of the global layout
(`fill_tma_gmem_shape_stride`). The fill is `CU_TENSOR_MAP_FLOAT_OOB_FILL_NONE`, which fills
out-of-bounds elements with zero (`copy_traits_sm90_tma.hpp:1035`).

All bf16 arrays use the shared layouts of `K2Layouts` (`fwd_kernel2.cuh:10-74`), built from
the atom `GMMA::Layout_K_INTER_Atom<bf16>`: 8 rows by 8 feature columns, the 8 columns
contiguous, no swizzle (`Swizzle<0,4,3>`). One copy therefore moves 8 consecutive features of
all rows of a tile: the box is `[8, rows, 1]`, and a tile of 128 features takes 16 copies with
dimension-0 coordinates `0, 8, …, 120`. The FP32 state uses `GMMA::Layout_K_SW32_Atom<float>`
(8 floats = one 32-byte swizzle unit, `Swizzle<1,4,3>`), so its box is `[8, 128, 1]` with the
32-byte swizzle.

## The eleven maps

With `n = H * total_tiles` (the source's `n_ht`) and `m = N * H`; the definitions below cite
the lines of `fwd_launch.cu`:

| param | source name | format | extents | outer byte strides | box | swizzle |
|---|---|---|---|---|---|---|
| 0 | `tma_load_v` | bf16 | `[128, T, H]` | `[256 * H, 256]` | `[8, 16, 1]` | none |
| 1 | `tma_load_beta2` | bf16 | `[H * T]` | none | `[32]` | none |
| 2 | `tma_load_ws_kd` | bf16 | `[128, 16, n]` | `[256, 4096]` | `[8, 16, 1]` | none |
| 3 | `tma_load_ws_qd` | the same as 2 |  |  |  |  |
| 4 | `tma_load_ws_kr` | the same as 2 |  |  |  |  |
| 5 | `tma_load_ws_gt` | f32 | `[128, n]` | `[512]` | `[128, 1]` | none |
| 6 | `tma_load_ws_inv` | bf16 | `[16, 16, n]` | `[32, 512]` | `[8, 16, 1]` | none |
| 7 | `tma_load_ws_mqk` | the same as 6 |  |  |  |  |
| 8 | `tma_load_initial_state` | f32 | `[128, 128, m]` | `[512, 65536]` | `[8, 128, 1]` | 32 B |
| 9 | `tma_store_final_state` | the same as 8 |  |  |  |  |
| 10 | `tma_store_out` | the same as 0 |  |  |  |  |

The global layouts are: `v` and `out` are `[T, H, 128]` arrays viewed as `(H, T, 128)` with
element strides `(128, 128 * H, 1)` (`fwd_launch.cu:50`), so the token dimension has the larger
stride and comes before the head dimension; `beta` is the contiguous `[H * T]` array (line 52);
the workspace arrays are row-major `(H * total_tiles, 16, 128)`, `(H * total_tiles, 128)` and
`(H * total_tiles, 16, 16)` (lines 73-77), six arrays laid one after the other from the
workspace pointer (lines 62-69, `workspaceArray`); the states are row-major `(N * H, 128, 128)`
(line 53), value row before key column.

## Cross-check with the compiled kernel

The coordinates the PTX passes agree with these dimensions
(`Kernels/FlashKdaFwd/packed_fp32_sm100a.ptx`, instruction indices of the decoded program; the
compiler unrolled the tile loop of the loads three times, and the indices are those of its first
copy):

* initial state, 333-378: 16 rank-3 loads `(8 i, 0, H * seq + head)`, `expect_tx` 65536 =
  16 copies of 8 * 128 floats;
* `v`, 1470-1515: 16 rank-3 loads `(8 i * s, bos + 16 t, head)`, where `s` is the 32-bit word at
  offset 128 of the parameter object (the scale of dimension 0, equal to 1, see `Spec.lean`);
* `beta`, 1519: one rank-1 load at `(H-major index of the tile's first token) & ~7`;
* workspace, 1521-1640: rank-3 loads `(8 i, 0, slot)` (16 each for the three row arrays, 2 each
  for `INV` and `Mqk`) and one rank-2 load `(0, slot)` for `g_total`, with
  `slot = head * total_tiles + tile_base + t`; `expect_tx` 17984 per tile =
  4096 + 64 + 3 * 4096 + 512 + 2 * 512;
* `out`, 3052-3082: 16 rank-3 stores `(8 i * s, bos + 16 t, head)`;
* final state, 3786-3831: 16 rank-3 stores `(8 i, 0, H * seq + head)`.

The mangled parameter types record the same boxes: the `TmaGmemBasis` layouts of the eleven
`AuxTmaParams` have the shapes `(8, 16, 1)`, `(32)`, `(8, 16, 1)` three times, `(128, 1)`,
`(8, 16, 1)` twice, `(8, 128, 1)` twice and `(8, 16, 1)`.

## Parameters and launch obligations

The allocation class of the global allocation is a device attribute, not an argument of the
encoding call, so it is a parameter of every map (as in the FlashMLA kernel). The L2 promotion
is a cache hint without effect on the memory model and is not represented.

The remaining launch obligations are those of `TensorDescriptor.Valid`: 16-byte aligned bases,
positive extents of at most `2 ^ 32`, strides below `2 ^ 40` (the `*_valid` theorems below).
-/

namespace PTX.Kernels.FlashKdaFwd
open TensorDescriptor

/-- The base address of the workspace array whose per-tile data starts `offset` bytes into the
per-tile record: the host places the six arrays one after the other, each with
`n_ht = H * total_tiles` entries, so an array starts at `workspace + n_ht * offset`
(`fwd_launch.cu:62-69`). The offsets are `0` (`k_decayed`), `4096` (`q_decayed`), `8192`
(`k_restored`), `12288` (`g_total`), `12800` (`INV`) and `13312` (`Mqk`). -/
def workspaceArray (workspace heads totalTiles offset : Nat) : Nat :=
  workspace + heads * totalTiles * offset

/-- A rank-3 bf16 map over a `[tokens, heads, 128]` array (`v` or `out`): dimension 0 is the
feature, dimension 1 the token (byte stride `256 * heads`), dimension 2 the head (byte stride
256). The box is 8 features by 16 tokens of one head. -/
def tokenMap (base tokens heads : Nat) (cls : AllocationClass) : Descriptor 2 where
  format := .bf16
  base := base
  extent := ![128, tokens, heads]
  outerStride := ![256 * heads, 256]
  box := ⟨![8, 16, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- A rank-1 bf16 map over a contiguous array of `count` elements, with a box of 32 elements
(`beta`). -/
def logitMap (base count : Nat) (cls : AllocationClass) : Descriptor 0 where
  format := .bf16
  base := base
  extent := ![count]
  outerStride := ![]
  box := ⟨![32], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- A rank-3 bf16 map over a row-major `[slots, 16, 128]` workspace array (`k_decayed`,
`q_decayed`, `k_restored`): dimension 0 is the feature, dimension 1 the row of the tile (256
bytes), dimension 2 the workspace slot (4096 bytes). The box is 8 features by the 16 rows of
one slot. -/
def tileRowsMap (base slots : Nat) (cls : AllocationClass) : Descriptor 2 where
  format := .bf16
  base := base
  extent := ![128, 16, slots]
  outerStride := ![256, 4096]
  box := ⟨![8, 16, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- A rank-2 FP32 map over a row-major `[slots, 128]` workspace array (`g_total`): dimension 0
is the feature, dimension 1 the workspace slot (512 bytes). The box is the 128 features of one
slot. -/
def totalDecayMap (base slots : Nat) (cls : AllocationClass) : Descriptor 1 where
  format := .f32
  base := base
  extent := ![128, slots]
  outerStride := ![512]
  box := ⟨![128, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- A rank-3 bf16 map over a row-major `[slots, 16, 16]` workspace array (`INV`, `Mqk`):
dimension 0 is the column, dimension 1 the row (32 bytes), dimension 2 the workspace slot (512
bytes). The box is 8 columns by the 16 rows of one slot. -/
def tileSquareMap (base slots : Nat) (cls : AllocationClass) : Descriptor 2 where
  format := .bf16
  base := base
  extent := ![16, 16, slots]
  outerStride := ![32, 512]
  box := ⟨![8, 16, 1], fun _ => 1⟩
  swizzle := .none
  fill := .zero
  allocationClass := cls

/-- A rank-3 FP32 map over a row-major `[planes, 128, 128]` state array: dimension 0 is the key
column, dimension 1 the value row (512 bytes), dimension 2 the plane of one sequence and head
(65536 bytes). The box is 8 key columns by the 128 value rows of one plane, with the 32-byte
swizzle. -/
def stateMap (base planes : Nat) (cls : AllocationClass) : Descriptor 2 where
  format := .f32
  base := base
  extent := ![128, 128, planes]
  outerStride := ![512, 65536]
  box := ⟨![8, 128, 1], fun _ => 1⟩
  swizzle := .b32
  fill := .zero
  allocationClass := cls

/-! ### The eleven maps of the launch -/

/-- Parameter 0, `tma_load_v` (`fwd_launch.cu:106`): the values, `[T, H, 128]` bf16. -/
def mapV (values heads tokens : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tokenMap values tokens heads cls

/-- Parameter 1, `tma_load_beta2` (`fwd_launch.cu:107`): the gate logits, `[H * T]` bf16. -/
def mapBeta (logits heads tokens : Nat) (cls : AllocationClass) : Descriptor 0 :=
  logitMap logits (heads * tokens) cls

/-- Parameter 2, `tma_load_ws_kd` (`fwd_launch.cu:109`): the workspace array `k_decayed`. -/
def mapKDecayed (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tileRowsMap (workspaceArray workspace heads totalTiles 0) (heads * totalTiles) cls

/-- Parameter 3, `tma_load_ws_qd` (`fwd_launch.cu:110`): the workspace array `q_decayed`. -/
def mapQDecayed (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tileRowsMap (workspaceArray workspace heads totalTiles 4096) (heads * totalTiles) cls

/-- Parameter 4, `tma_load_ws_kr` (`fwd_launch.cu:111`): the workspace array `k_restored`. -/
def mapKRestored (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tileRowsMap (workspaceArray workspace heads totalTiles 8192) (heads * totalTiles) cls

/-- Parameter 5, `tma_load_ws_gt` (`fwd_launch.cu:112`): the workspace array `g_total`. -/
def mapGTotal (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 1 :=
  totalDecayMap (workspaceArray workspace heads totalTiles 12288) (heads * totalTiles) cls

/-- Parameter 6, `tma_load_ws_inv` (`fwd_launch.cu:113`): the workspace array `INV`. -/
def mapInv (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tileSquareMap (workspaceArray workspace heads totalTiles 12800) (heads * totalTiles) cls

/-- Parameter 7, `tma_load_ws_mqk` (`fwd_launch.cu:114`): the workspace array `Mqk`. -/
def mapMqk (workspace heads totalTiles : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tileSquareMap (workspaceArray workspace heads totalTiles 13312) (heads * totalTiles) cls

/-- Parameter 8, `tma_load_initial_state` (`fwd_launch.cu:126`): the FP32 initial state,
`[N * H, 128, 128]`. -/
def mapInitialState (initial sequences heads : Nat) (cls : AllocationClass) : Descriptor 2 :=
  stateMap initial (sequences * heads) cls

/-- Parameter 9, `tma_store_final_state` (`fwd_launch.cu:127`): the FP32 final state,
`[N * H, 128, 128]`. -/
def mapFinalState (final sequences heads : Nat) (cls : AllocationClass) : Descriptor 2 :=
  stateMap final (sequences * heads) cls

/-- Parameter 10, `tma_store_out` (`fwd_launch.cu:116`): the output, `[T, H, 128]` bf16. -/
def mapOut (output heads tokens : Nat) (cls : AllocationClass) : Descriptor 2 :=
  tokenMap output tokens heads cls

/-! ### Validity -/

theorem tokenMap_valid {base tokens heads : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hTokens : 0 < tokens ∧ tokens ≤ 2 ^ 32)
    (hHeads : 0 < heads ∧ heads < 2 ^ 32) : Valid (tokenMap base tokens heads cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [tokenMap, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [tokenMap]
    · simpa [tokenMap] using hTokens
    · simpa [tokenMap] using ⟨hHeads.1, hHeads.2.le⟩
  · fin_cases i
    · have h : 256 * heads % 16 = 0 ∧ 256 * heads < 2 ^ 40 := by omega
      simpa [tokenMap] using h
    · simp [tokenMap]
  · fin_cases i <;> simp [tokenMap]
  · fin_cases i <;> simp [tokenMap]

theorem logitMap_valid {base count : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hCount : 0 < count ∧ count ≤ 2 ^ 32) :
    Valid (logitMap base count cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => i.elim0, fun i => ?_, fun i => ?_,
    by simp [logitMap, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    simpa [logitMap] using hCount
  · fin_cases i
    simp [logitMap]
  · fin_cases i
    simp [logitMap]

theorem tileRowsMap_valid {base slots : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hSlots : 0 < slots ∧ slots ≤ 2 ^ 32) :
    Valid (tileRowsMap base slots cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [tileRowsMap, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [tileRowsMap]
    · simp [tileRowsMap]
    · simpa [tileRowsMap] using hSlots
  · fin_cases i <;> simp [tileRowsMap]
  · fin_cases i <;> simp [tileRowsMap]
  · fin_cases i <;> simp [tileRowsMap]

theorem totalDecayMap_valid {base slots : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hSlots : 0 < slots ∧ slots ≤ 2 ^ 32) :
    Valid (totalDecayMap base slots cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [totalDecayMap, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [totalDecayMap]
    · simpa [totalDecayMap] using hSlots
  · fin_cases i
    simp [totalDecayMap]
  · fin_cases i <;> simp [totalDecayMap]
  · fin_cases i <;> simp [totalDecayMap]

theorem tileSquareMap_valid {base slots : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hSlots : 0 < slots ∧ slots ≤ 2 ^ 32) :
    Valid (tileSquareMap base slots cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [tileSquareMap, Format.bytes], .inl rfl, fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [tileSquareMap]
    · simp [tileSquareMap]
    · simpa [tileSquareMap] using hSlots
  · fin_cases i <;> simp [tileSquareMap]
  · fin_cases i <;> simp [tileSquareMap]
  · fin_cases i <;> simp [tileSquareMap]

theorem stateMap_valid {base planes : Nat} {cls : AllocationClass}
    (hBase : base % 16 = 0) (hPlanes : 0 < planes ∧ planes ≤ 2 ^ 32) :
    Valid (stateMap base planes cls) := by
  refine ⟨by decide, hBase, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_,
    by simp [stateMap, Format.bytes],
    .inr (by simp [stateMap, Format.bytes, TensorTile.swizzleWidth]), fun h => (by cases h), rfl⟩
  · fin_cases i
    · simp [stateMap]
    · simp [stateMap]
    · simpa [stateMap] using hPlanes
  · fin_cases i <;> simp [stateMap]
  · fin_cases i <;> simp [stateMap]
  · fin_cases i <;> simp [stateMap]

end PTX.Kernels.FlashKdaFwd
