-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Numeric
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Data.Indices
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.Code
public import Lemmas.Flow.Segment
public import Lemmas.Flow.Store
public import Lemmas.Flow.StoreBytes
public import Lemmas.Flow.StoreValue
public import Lemmas.Flow.Events
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.Next
public import Lemmas.Flow.Word
public import Lemmas.Flow.SegChain

@[expose] public section

/-! # `wg2`: the FP8 dequantizer of the FlashMLA sparse decode kernel

Warpgroup 2 (pcs 2606-3610, `kernel.cuh:620-660` and `dequant_utils.cuh`,
`KVBlockDequantizer`) turns each KV block's raw e4m3 rows and ue8m0 scales — which the raw
producer warp wrote into shared memory — into the block's K-major SW128 bf16 tile:

* it reads the launch's batch count `b`, its own two runtime lengths (`topk_length` /
  `extra_topk_length` with `ld.global.nc`, pcs 2620 and 2630, the assumption A6 `ncReadOnly`),
  and forms the two padded block counts `orig_topk_padded` (pcs 2622-2626, 2631-2636) and
  `total_topk_padded` (pcs 2637-2639), which bound the blocks it walks;
* before the loop it passes the `bar_q_utccp` mbarrier (pc 2644) — the main loop opens once the
  query copy is in — and after the loop the CTA-wide named barrier `everyone_sync`
  (`barrier.sync 12, 384`, pc 3610);
* for each block `b` of `total_topk_padded / 64` it waits `bar_raw_ready[buf]` (pc 2677) and
  `bar_sv_done[buf]` (pc 2684), reads the row's 16 ue8m0 scale bytes (pcs 2695, 2920, 3145, 3370,
  `ld.shared.v4.b32`, 16 bytes at byte 512 of the 576-byte raw row) and its 32 raw words (eight
  `ld.shared.b64` per row), converts every e4m3 pair with `cvt.rn.bf16x2.e4m3x2` and every ue8m0
  pair with `cvt.rn.bf16x2.ue8m0x2`, multiplies with `mul.bf16x2`, and writes the 32 16-byte
  chunks of the SW128 bf16 tile with `st.weak.shared::cta.b128` (the first at pc 2752);
* it then fences the tile for the async proxy (`fence.proxy.async.shared::cta`, pc 3595) and
  arrives on `bar_quant_part_dequant_ready[buf]` (pc 3597) and `bar_raw_free[buf]` (pc 3599),
  flips the ring slot and the phase parity (pcs 3600-3604) and steps the block counter;
* after the last block it passes `barrier.sync 12, 384` and returns at the program's `ret`
  (pc 3611, role `done`).

Both arrivals are `mbarrier.arrive` (`kernel.cuh:657-658`); the role never waits on
`bar_raw_free` — the raw producer does, and the dequantizer only signals it.

## The two caches are one body

`dequant_utils.cuh`'s `KVBlockDequantizer` is one template, and the kernel instantiates it once
per cache (`dequant_orig`, `dequant_extra`, `kernel.cuh:645-646`). In this no-split V4.1
instance both formats are `KVCacheFormat<V41>` (`Data/Indices.bytesPerToken`: 512 e4m3 bytes and
16 ue8m0 bytes per 528-byte token), so both instantiations compile to the same body and the
role's arithmetic is the same for both caches: no byte, scale or tile offset reads the block's
cache. `D.extra` records the tag (`isExtraBlock`) for the protocol layer, which needs it to
match a block with its cache's tensor map, and `tag_free` shows the formulas have no cache
argument.

## The sites

The abstract states (`Site`) are the role's event instructions: the two `.nc` length reads, the
three mbarrier waits and the two arrivals, the 4 scale loads, the 32 raw loads, the 32
`st.weak.shared::cta.b128` stores, the proxy fence and the named barrier. The unrolled body
names a site by its position: `raw r s` is the raw word of row `r` (`local_row_idx`) and step
`s` (`local_col_idx`), `scale r` the scale row of row `r`, and `store r s` the tile chunk of
`(r, s)`. `Site.pc` gives each its program counter. The compiler hoisted each step's raw load
above the previous step's store (`dequant_utils.cuh` reads the next word before the current
store), so program order interleaves them: `raw r 0`, `raw r 1`, `store r 0`, `raw r 2`,
`store r 1`, ..., `store r 7`.

`D` is the role's small state — the next site, the block, the ring slot `buf` and phase parity
`par`, the cache tag, and the two runtime lengths — and `Inv` is the loop invariant: the ring
slot is the block's slot of the two-slot buffer ring (`buf = block % 2`), the parity counts the
ring's phases (`par = block / 2 % 2`, which is what the code's `%r457 = par != buf ? 1 : 0`
maintains), the block is one of the row's padded blocks with its cache tag, and the
dequantizer's positions fit the two shared buffers.

## The dequantizer's geometry

A thread is `idx_in_group = tid % 8` of `group_idx = (tid % 128) / 8` (the constructor of
`KVBlockDequantizer`). The block's raw rows are `RAW_TOKEN_SMEM_STRIDE = 576` bytes each
(`config.h:54-57`: 512 data bytes, 16 scale bytes, 48 padding), and a group owns the rows
`16 * lr + group_idx` for `lr < 4` (`ROWS_PER_GROUP`), eight lanes per token. Every lane reads
the eight e4m3 bytes at byte `64 * j + 8 * idx_in_group` of its row and the row's 16 scale
bytes, of which it uses the scale of the 32-element quant tile that covers its elements,
`2 * j + [4 ≤ idx_in_group]`. The destination is the SW128 K-major bf16 tile of 64 rows x 512
elements: `dstOff` below is `group_idx / 8 * (8 * 128) + row_in_atom * 128 +
(idx_in_group ^ row_in_atom) * 16` of the source (the 8-row swizzle atom, the XOR acting on the
16-byte lane index), and `tileOff` adds `2048 * lr` (a group's rows are `NUM_GROUPS * 128`
bytes apart) and `8192 * j` (a step is `B_TOPK * 128`). `logicalElem` is the element of the
token row the chunk carries and `tileElem` where the swizzle puts it.

## The numeric steps

Three rules produce the stored bf16 values, and the file names them where the values are formed:

* `cvt.rn.bf16x2.e4m3x2` is Core's exact conversion, so the bf16 value of an e4m3 byte is
  `e4m3Val` of it;
* `cvt.rn.bf16x2.ue8m0x2` is Core's `2^(e-127)` for `1 ≤ e ≤ 254`; the pattern `0` — which PTX
  leaves without a value and CUDA 13.2 reads as `2^-127` — is `Assumptions.cvtUe8m0`, one of
  `Assumptions.all`, and `ue8m0Val_zero` records that one pattern's value;
* `mul.bf16x2` is `Assumptions.mulBf16x2`: each half is the exact real product of its two bf16
  inputs, not the IEEE-rounded one (`mulBf16x2_pair` names the rule's output).

With those three, `dequant_chunk` is the dataflow fact the role owes: the eight bf16 values the
chunk of `(r, s)` carries are `dequant` of the raw row at the eight consecutive elements
`64 * j + 8 * idx_in_group + e`, and `dequant_scale` shows that the scale byte the code picks is
exactly the one `dequant` names (`512 + t / 32`).

## Entry and thread soundness

The launch machine starts with the shared prologue, whose register-limit event gives the
dequantizer its four entry registers. `entry_of_handoff` extracts those facts and proves the
thread's batch and query bounds. `start_all` covers the optional length pointers. The length
events use `seg_mainCeil` and `seg_extraCeil` to reach the first query wait. Ring state at that
wait starts at block zero.

`steps_all` proves every role site's continuation. `stepAt_scale` reads four events of one
scale vector. Between those events `D.sc` records the words and `accAt` gives the corresponding
thread accumulator. `scaleTail` proves the sixteen extracted bytes and the row's first tile
address. `stepAt_raw` records and unpacks the first word and verifies the remaining raw loads.
`run_chunkCompute` checks the compiler's select, conversion, multiply and pack sequence for
all 32 chunks. `fires_tileStore_payload` states the address and exact bytes of each store.
`stepAt_store` accounts for prefetched words and the next row, and the fence and barrier
steps carry the ring through its last block.

`machine_sound` composes these steps with the launch events and the shared prologue's start.
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
-- `seg_fp` always elaborates its value tactic, even for a segment that writes no register
-- (the poll retries); its generated tactics then legitimately have no goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Wg2

/-- The assumptions the role is evaluated under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ## The thread's place in the launch

`Proof/Thread/Prologue.lean` defines a thread's CTA and thread index (`ctaOf`, `tidOf`,
`laneOf`, `warpOf`), the CTA's `%ctaid` coordinates (`ctaidX`, `ctaidY`) and the shared address
`sb` of a byte above the dynamic shared base. -/

/-- The batch whose KV blocks the thread's CTA dequantizes (`%ctaid.y`). -/
def eOf (L : Launch) (g : Nat) : Nat := ctaidY L g

/-- The query of the thread's CTA (`%ctaid.x`). The dequantizer's arithmetic does not read it:
which blocks a CTA walks depends on the batch alone. -/
def qOf (L : Launch) (g : Nat) : Nat := ctaidX L g

/-! ## The dequantizer's constants

`dequant_utils.cuh`'s `KVBlockDequantizer<F, D, B_TOPK, RAW_TOKEN_SMEM_STRIDE,
SCALE_SMEM_STRIDE>` at the kernel's V4.1 instantiation, and `config.h`'s shared-memory plan. -/

/-- `B_TOPK` (`config.h:48`): the token rows of one KV block. -/
def topkBlock : Nat := 64

/-- `GROUP_SIZE` (`dequant_utils.cuh`): the lanes of one dequantizer group. -/
def groupSize : Nat := 8

/-- `NUM_GROUPS = 128 / GROUP_SIZE`: the groups of the warpgroup. -/
def numGroups : Nat := 16

/-- `ROWS_PER_GROUP = B_TOPK / NUM_GROUPS`: the token rows one group converts. -/
def rowsPerGroup : Nat := 4

/-- `ELEMS_PER_STEP = GROUP_SIZE * 8`: the elements of one row a group's step covers (one
swizzle-atom column). -/
def elemsPerStep : Nat := 64

/-- `NUM_STEPS = D / ELEMS_PER_STEP`: the steps of one row. -/
def numSteps : Nat := 8

/-- `RAW_BYTES_PER_STEP` for the FP8 format: one byte per element. -/
def rawBytesPerStep : Nat := 64

/-- `RAW_BYTES_PER_THREAD_STEP = RAW_BYTES_PER_STEP / GROUP_SIZE`: the raw word of one lane. -/
def rawBytesPerThread : Nat := 8

/-- `F::QUANT_BYTES`: the e4m3 bytes of a V4.1 token row (`kv_cache_format.h:19`). -/
def quantBytes : Nat := 512

/-- `NUM_SCALES = D / QUANT_TILE_SIZE`: the scale bytes of one token row. -/
def numScales : Nat := 16

/-- `SCALE_LOAD_BYTES`: the whole words a scale row is loaded in. -/
def scaleLoadBytes : Nat := 16

/-- `RAW_TOKEN_SMEM_STRIDE` (`config.h:54-57`): 512 e4m3 bytes, 16 ue8m0 scale bytes and 48
padding bytes per raw token row. -/
def rawRowStride : Nat := 576

/-- The bytes of one `raw_quant` block: `B_TOPK` rows of `RAW_TOKEN_SMEM_STRIDE`. -/
def rawBufBytes : Nat := 36864

/-- The bytes of one bf16 `dequant` tile: `B_TOPK * D` bf16 values. -/
def dequantBytes : Nat := 65536

/-! ## The shared-memory offsets of the role

`SharedMemoryPlan` (`config.h:141-172`): the two `dequant` tiles at bytes 0 and 65536 of `u`,
the two `raw_quant` blocks at 131072 and 167936 (`131072 + 36864`), and the mbarriers of the
barrier block (`Data/Barriers.mbars`). -/

/-- The shared byte offset of the bf16 tile of ring slot `buf`. -/
def tileBase (buf : Nat) : Nat := dequantBytes * buf

/-- The shared byte offset of the raw block of ring slot `buf`. -/
def rawBase (buf : Nat) : Nat := 131072 + rawBufBytes * buf

/-- The shared byte offset of `bar_q_utccp` (`Data/Barriers.mbars`). -/
def qUtccpOff : Nat := 222784

/-- The shared byte offset of `bar_raw_ready[buf]` (`Data/Barriers.mbars`). -/
def rawReadyOff (buf : Nat) : Nat := 222808 + 8 * buf

/-- The shared byte offset of `bar_raw_free[buf]` (`Data/Barriers.mbars`). -/
def rawFreeOff (buf : Nat) : Nat := 222824 + 8 * buf

/-- The shared byte offset of `bar_quant_part_dequant_ready[buf]` (`Data/Barriers.mbars`). -/
def dequantReadyOff (buf : Nat) : Nat := 222792 + 8 * buf

/-- The shared byte offset of `bar_sv_done[buf]` (`Data/Barriers.mbars`). -/
def svDoneOff (buf : Nat) : Nat := 222936 + 8 * buf

/-! ## The dequantizer's positions

`dequant_utils.cuh`'s constructor and `run`: `group_idx = idx_in_warpgroup / GROUP_SIZE`,
`idx_in_group = idx_in_warpgroup % GROUP_SIZE`, `raw_offset = group_idx *
RAW_TOKEN_SMEM_STRIDE + idx_in_group * RAW_BYTES_PER_THREAD_STEP`,
`dst_offset = group_idx / 8 * (8 * 128) + (group_idx % 8) * 128 +
(idx_in_group ^ (group_idx % 8)) * 16`. -/

/-- `idx_in_warpgroup`: the thread's index in the warpgroup (`%r5 = %tid.x % 128`). -/
def idxInWg (L : Launch) (g : Nat) : Nat := tidOf L g % 128

/-- The dequantizer's `group_idx` (`%r512 = %r5 >> 3`). -/
def groupIdx (L : Launch) (g : Nat) : Nat := idxInWg L g / groupSize

/-- The dequantizer's `idx_in_group` (`%r513 = %tid.x & 7`). -/
def idxInGroup (L : Launch) (g : Nat) : Nat := tidOf L g % groupSize

/-- The group's row in its 8-row swizzle atom (`group_idx % 8`). -/
def rowInAtom (L : Launch) (g : Nat) : Nat := groupIdx L g % 8

/-- `idx_in_group < GROUP_SIZE`. -/
theorem idxInGroup_lt (L : Launch) (g : Nat) : idxInGroup L g < groupSize := by
  unfold idxInGroup groupSize
  exact Nat.mod_lt _ (by decide)

/-- `group_idx < NUM_GROUPS`. -/
theorem groupLt (L : Launch) (g : Nat) : groupIdx L g < numGroups := by
  unfold groupIdx idxInWg numGroups groupSize
  have := Nat.mod_lt (tidOf L g) (show 0 < 128 by decide)
  omega

/-- `group_idx % 8 < 8`. -/
theorem rowInAtom_lt (L : Launch) (g : Nat) : rowInAtom L g < 8 := by
  unfold rowInAtom
  exact Nat.mod_lt _ (by decide)

/-- A three-bit XOR of two three-bit numbers is three bits: the swizzle's XOR of the 16-byte
lane index with the row's position in the atom stays inside the atom row. -/
theorem xor_lt_eight {a b : Nat} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 := by
  interval_cases a <;> interval_cases b <;> decide

/-- The token row (of the block's 64) the group's `lr`-th raw row is. -/
def rawRow (L : Launch) (g : Nat) (lr : Nat) : Nat := lr * numGroups + groupIdx L g

/-- The byte offset of the group's `lr`-th raw row within the block's raw buffer
(`raw_offset` plus `lr * NUM_GROUPS * RAW_TOKEN_SMEM_STRIDE`): the rows are
`RAW_TOKEN_SMEM_STRIDE = 576` bytes apart. -/
def rawRowOff (L : Launch) (g : Nat) (lr : Nat) : Nat := rawRowStride * rawRow L g lr

/-- The byte offset of the row's 16 ue8m0 scale bytes within the raw buffer: byte 512 of the
row (`raw + F::QUANT_BYTES`). -/
def scaleRowOff (L : Launch) (g : Nat) (lr : Nat) : Nat :=
  rawRowOff L g lr + quantBytes

/-- The byte offset of the row's `s`-th raw word: `raw_offset + idx_in_group * 8 + s * 64`. -/
def rawWordOff (L : Launch) (g : Nat) (lr s : Nat) : Nat :=
  rawRowOff L g lr + idxInGroup L g * rawBytesPerThread + s * rawBytesPerStep

/-- The byte of the row whose e4m3 value the lane's `e`-th element of step `s` reads: the lane's
eight bytes of the step's word (`dequant_utils.cuh`: elements
`[s * 64 + idx_in_group * 8, + 8)` of the row lie in this word). -/
def elemByte (L : Launch) (g : Nat) (s e : Nat) : Nat :=
  s * elemsPerStep + idxInGroup L g * rawBytesPerThread + e

/-- The ue8m0 scale byte of the lane's step `s`: `local_col_idx * ELEMS_PER_STEP /
QUANT_TILE_SIZE + (idx_in_group >= GROUP_SIZE / 2)`, the scale of the 32-element quant tile that
covers the lane's eight elements. -/
def scaleIdx (L : Launch) (g : Nat) (s : Nat) : Nat :=
  2 * s + (if groupSize / 2 ≤ idxInGroup L g then 1 else 0)

/-- The offset of the thread's first bf16 chunk in the SW128 tile (`dst_offset`: the 8-row
swizzle atoms stacked along the rows, the 16-byte lane index XORed with the row's position in
the atom). -/
def dstOff (L : Launch) (g : Nat) : Nat :=
  groupIdx L g / 8 * (8 * 128) + rowInAtom L g * 128 +
    (idxInGroup L g ^^^ rowInAtom L g) * 16

/-- The offset of the thread's chunk of `(lr, s)` in the tile: `dst + dst_offset +
local_row_idx * NUM_GROUPS * 128 + local_col_idx * B_TOPK * 128`. -/
def tileOff (L : Launch) (g : Nat) (lr s : Nat) : Nat :=
  dstOff L g + numGroups * 128 * lr + topkBlock * 128 * s

/-- The element of the token row the chunk of `(lr, s)` carries, `e` bytes in: the lane's eight
consecutive elements of the step. -/
def logicalElem (L : Launch) (g : Nat) (s e : Nat) : Nat :=
  s * elemsPerStep + idxInGroup L g * rawBytesPerThread + e

theorem elemByte_eq_logicalElem (L : Launch) (g s e : Nat) :
    elemByte L g s e = logicalElem L g s e := rfl

/-- The thread's raw row is one of the block's 64. -/
theorem rawRow_lt {L : Launch} {g lr : Nat} (hlr : lr < rowsPerGroup) :
    rawRow L g lr < topkBlock := by
  have := groupLt L g
  unfold rawRow topkBlock numGroups rowsPerGroup at *
  omega

/-! ## The e4m3 and ue8m0 byte formulas

`dequant row t = e4m3Val (row t) * ue8m0Val (row (512 + t / 32))`: the value of element `t` of a
row multiplies the e4m3 byte `t` by the scale byte of its 32-element quant tile. The lemmas
below say that the bytes the code reads are exactly those two, and `ue8m0Val_zero` states the
one pattern PTX leaves without a value. -/

/-- **The scale-byte formula**: element `s * 64 + idx * 8 + e` (`e < 8`) lies in the quant tile
`2 * s + [4 ≤ idx]`, which is `scaleIdx`, so the scale byte `dequant` names is the one the code
reads. -/
theorem scaleIdx_eq (L : Launch) (g s e : Nat) (he : e < rawBytesPerThread) :
    logicalElem L g s e / 32 = scaleIdx L g s := by
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  unfold logicalElem scaleIdx elemsPerStep rawBytesPerThread groupSize
  unfold rawBytesPerThread at he
  have h3 : (s * 64 + idxInGroup L g * 8 + e) / 32 = 2 * s + idxInGroup L g / 4 := by omega
  rw [h3]
  split_ifs with h
  · have : idxInGroup L g / 4 = 1 := by omega
    omega
  · have : idxInGroup L g / 4 = 0 := by omega
    omega

/-- **The scale-byte formula of `dequant`**: the value of element `t` of a raw row is the e4m3
byte `t` times the ue8m0 scale byte at `512 + scaleIdx`, the layout the raw producer writes
(the scale bytes at byte 512 of each `RAW_TOKEN_SMEM_STRIDE`-byte row) and this role reads. -/
theorem dequant_scale (row : Nat → Nat) {t s : Nat} (h : t / 32 = s) :
    dequant row t = e4m3Val (row t) * ue8m0Val (row (512 + s)) := by
  unfold dequant
  rw [h]

/-- **The dataflow fact of one chunk**: the eight bf16 values the thread's chunk of `(lr, s)`
carries are the dequantized values of eight consecutive elements of the raw row. The chunk's
`e`-th value is `dequant` of the row at element `logicalElem s e`, i.e. `e4m3Val` of the byte
`elemByte` (`scaleIdx_eq`, `dequant_scale`) times `ue8m0Val` of the scale byte `scaleIdx`; the
tile element it lands in is the swizzled one (`tileElem`). -/
theorem dequant_chunk (row : Nat → Nat) (L : Launch) (g : Nat) (s : Nat) :
    ∀ e < rawBytesPerThread,
      dequant row (logicalElem L g s e) =
        e4m3Val (row (elemByte L g s e)) * ue8m0Val (row (512 + scaleIdx L g s)) := by
  intro e he
  rw [dequant_scale row (scaleIdx_eq L g s e he), elemByte_eq_logicalElem]

/-- The raw bytes the chunk reads are inside the row's 512 e4m3 bytes. -/
theorem elemByte_lt {L : Launch} {g s e : Nat} (hs : s < numSteps)
    (he : e < rawBytesPerThread) : elemByte L g s e < quantBytes := by
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  unfold elemByte elemsPerStep rawBytesPerThread quantBytes numSteps at *
  omega

/-- The scale byte the chunk reads is one of the row's 16. -/
theorem scaleIdx_lt {L : Launch} {g s : Nat} (hs : s < numSteps) :
    scaleIdx L g s < numScales := by
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  unfold scaleIdx numScales numSteps groupSize at *
  split_ifs <;> omega

/-! ## The geometry fits the two shared buffers -/

/-- A raw word of the block is inside the block's 36864 bytes. -/
theorem rawWord_fit {L : Launch} {g lr s : Nat} (hlr : lr < rowsPerGroup)
    (hs : s < numSteps) : rawWordOff L g lr s + rawBytesPerThread ≤ rawBufBytes := by
  have hrow := rawRow_lt (L := L) (g := g) hlr
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  unfold rawWordOff rawRowOff rawRowStride rawBufBytes topkBlock rawBytesPerThread
    rawBytesPerStep numSteps at *
  omega

/-- A scale row is inside the block's 36864 bytes. -/
theorem scaleRow_fit {L : Launch} {g lr : Nat} (hlr : lr < rowsPerGroup) :
    scaleRowOff L g lr + scaleLoadBytes ≤ rawBufBytes := by
  have hrow := rawRow_lt (L := L) (g := g) hlr
  unfold scaleRowOff rawRowOff rawRowStride quantBytes scaleLoadBytes rawBufBytes topkBlock at *
  omega

theorem dstOff_lt (L : Launch) (g : Nat) : dstOff L g < 65536 := by
  have hg : groupIdx L g < 16 := groupLt L g
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  have hra : rowInAtom L g < 8 := rowInAtom_lt L g
  have hxor : idxInGroup L g ^^^ rowInAtom L g < 8 := xor_lt_eight h1 hra
  unfold dstOff at *
  omega

/-- The thread's tile chunk is inside the tile's 65536 bytes. -/
theorem tile_fit {L : Launch} {g lr s : Nat} (hlr : lr < rowsPerGroup) (hs : s < numSteps) :
    tileOff L g lr s + 16 ≤ dequantBytes := by
  have hg := groupLt L g
  have h1 : idxInGroup L g < 8 := by
    have := idxInGroup_lt L g
    unfold groupSize at this
    exact this
  have hra : rowInAtom L g < 8 := rowInAtom_lt L g
  have hxor : idxInGroup L g ^^^ rowInAtom L g < 8 := xor_lt_eight h1 hra
  unfold tileOff dstOff numGroups topkBlock rowsPerGroup numSteps dequantBytes at *
  omega

/-! ## The sites -/

/-- One state per event instruction of the role. `raw r s` is the `ld.shared.b64` of row `r` and
step `s`, `scale r j` element `j` of the `ld.shared.v4.b32` of row `r`'s 16 scale bytes (the
four elements share the load's pc, `sub = j`), and `store r s` the
`st.weak.shared::cta.b128` of `(r, s)`. -/
inductive Site where
  /-- The row's runtime main-cache length, `ld.global.nc` (2620). -/
  | lenOrig
  /-- The row's runtime extra-cache length, `ld.global.nc` (2630). -/
  | lenExtra
  /-- The `bar_q_utccp` wait before the loop (2644). -/
  | qUtccp
  /-- The wait on `bar_raw_ready[buf]` (2677). -/
  | rawReady
  /-- The wait on `bar_sv_done[buf]` (2684). -/
  | svDone
  /-- Element `j` of the 16 scale bytes of row `r`, `ld.shared.v4.b32` (2695, 2920, 3145,
  3370); the four elements share the load's pc. -/
  | scale (r : Fin 4) (j : Fin 4)
  /-- The raw word of row `r` and step `s`, `ld.shared.b64`. -/
  | raw (r : Fin 4) (s : Fin 8)
  /-- The 16-byte bf16 chunk of `(r, s)`, `st.weak.shared::cta.b128`. -/
  | store (r : Fin 4) (s : Fin 8)
  /-- `fence.proxy.async.shared::cta` (3595). -/
  | fence
  /-- The arrival on `bar_quant_part_dequant_ready[buf]` (3597). -/
  | ready
  /-- The arrival on `bar_raw_free[buf]` (3599). -/
  | free
  /-- `barrier.sync 12, 384` (3610). -/
  | barrier
  deriving DecidableEq, Repr

/-- The program counter of a site. -/
def Site.pc : Site → Nat
  | .lenOrig => 2620
  | .lenExtra => 2630
  | .qUtccp => 2644
  | .rawReady => 2677
  | .svDone => 2684
  | .scale r _ => [2695, 2920, 3145, 3370].getD r.val 0
  | .raw r s =>
    ([[2729, 2737, 2760, 2784, 2808, 2832, 2856, 2880],
      [2954, 2962, 2985, 3009, 3033, 3057, 3081, 3105],
      [3179, 3187, 3210, 3234, 3258, 3282, 3306, 3330],
      [3404, 3412, 3435, 3459, 3483, 3507, 3531, 3555]].getD r.val []).getD s.val 0
  | .store r s =>
    ([[2752, 2776, 2800, 2824, 2848, 2872, 2896, 2919],
      [2977, 3001, 3025, 3049, 3073, 3097, 3121, 3144],
      [3202, 3226, 3250, 3274, 3298, 3322, 3346, 3369],
      [3427, 3451, 3475, 3499, 3523, 3547, 3571, 3594]].getD r.val []).getD s.val 0
  | .fence => 3595
  | .ready => 3597
  | .free => 3599
  | .barrier => 3610

/-- The size in bytes of a site's access. -/
def Site.width : Site → Nat
  | .scale _ _ => 4
  | .raw _ _ => rawBytesPerThread
  | .store _ _ => 16
  | .qUtccp | .rawReady | .svDone | .ready | .free => 8
  | .lenOrig | .lenExtra | .fence | .barrier => 0

/-- The row a site belongs to. -/
def Site.row : Site → Option Nat
  | .scale r _ | .raw r _ | .store r _ => some r.val
  | _ => none

/-- The column (step) a site belongs to. -/
def Site.step : Site → Option Nat
  | .raw _ s | .store _ s => some s.val
  | _ => none

/-- The sub-step of a site: the element of the four-element scale load. -/
def Site.sub : Site → Nat
  | .scale _ j => j.val
  | _ => 0

/-- Whether the site is one of the dequantizer's body (a load, a store, the fence or an
arrival). -/
def Site.inBody : Site → Bool
  | .scale _ _ | .raw _ _ | .store _ _ | .fence | .ready | .free => true
  | _ => false

/-! ## The abstract state and its invariant -/

/-- The role's state: the next event, the block whose rows it dequantizes, the buffer ring slot
and phase parity, the block's cache tag, the two runtime lengths, and the bytes the shared loads
returned (the raw word of the current step, the word read ahead, and the row's scale bytes). -/
structure D where
  site : Site
  /-- The block whose raw rows the body converts (`0 ≤ block < totalBlocks`). -/
  block : Nat
  /-- The buffer ring slot (`%r2988`). -/
  buf : Nat
  /-- The phase parity the two waits use (`%r457`): `bar_raw_ready[buf]` at `par`,
  `bar_sv_done[buf]` at `par ^ 1`. -/
  par : Nat
  /-- The block's cache tag (`isExtraBlock`). Both caches are V4.1 here, so the dequantizer's
  arithmetic does not read it (`tag_free`). -/
  extra : Bool
  /-- The row's main-cache length (`%r2985`). -/
  len0 : Nat
  /-- The row's extra-cache length (`%r2986`). -/
  len1 : Nat
  /-- The eight raw bytes (little-endian) of the step whose values the next store writes: the
  word `ld.shared.b64` returned for the current step. -/
  raw : Nat
  /-- The eight raw bytes of the step prefetched ahead: the word the loop reads before it stores
  the current step's chunk (`dequant_utils.cuh`'s `cur_data`). -/
  nxt : Nat
  /-- The ue8m0 scale bytes (little-endian, low byte first) the current row's scale load has
  returned so far: at site `.scale r j` the low `4 * j` bytes are words `0 .. j - 1`. -/
  sc : Nat

/-- A loaded byte string as the integer its little-endian word holds; zero when the bytes are
not an integer pattern. -/
def bytesNat (bs : List (Option Byte)) : Nat := (littleEndianBits bs).getD 0

/-- The 32-bit word of one scale load element. -/
def scaleBits (bs : List (Option Byte)) : Nat := bytesNat bs % 256 ^ 4

/-- A raw load is represented by a full 64-bit word. -/
def rawBits (bs : List (Option Byte)) : Nat := bytesNat bs % 2 ^ 64

/-- Word `i` of the scale bytes the state has read (`D.sc`, little-endian). -/
def scaleWord (d : D) (i : Nat) : Nat := d.sc / 256 ^ (4 * i) % 256 ^ 4

/-- The values a vector scale load has returned before its current element: element `j` of the
load follows the words `0 .. j - 1` of the row's scale bytes, which `D.sc` holds. Every other
site carries no pending values. A thread state between two elements of a `ld.shared.v4.b32`
holds exactly these (`afterLoad` appends the element it read). -/
def accAt (d : D) : List Value :=
  match d.site with
  | .scale _ j => (List.range j.val).map fun i => b32 (scaleWord d i)
  | _ => []

/-- A state outside a scale load has no pending values. -/
theorem accAt_of_not_scale {d : D} (h : ∀ r j, d.site ≠ .scale r j) : accAt d = [] := by
  unfold accAt
  cases hsite : d.site <;> simp_all

/-- The pending values of a scale site are the words before its element. -/
theorem accAt_of_scale {d : D} {r : Fin 4} {j : Fin 4} (hd : d.site = .scale r j) :
    accAt d = (List.range j.val).map fun i => b32 (scaleWord d i) := by
  unfold accAt
  rw [hd]

/-- The low words of the scale accumulator are unchanged by a later word. -/
theorem scaleWord_low {s j i w : Nat} (hi : i < j) :
    (s % 256 ^ (4 * j) + 256 ^ (4 * j) * w) / 256 ^ (4 * i) % 256 ^ 4 =
      s / 256 ^ (4 * i) % 256 ^ 4 := by
  have hpos : 0 < 256 ^ (4 * i) := pow_pos (by norm_num) _
  have hpow : (256 : Nat) ^ (4 * j) = 256 ^ (4 * i) * 256 ^ (4 * (j - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow]
  have hrw : s % (256 ^ (4 * i) * 256 ^ (4 * (j - i))) +
      256 ^ (4 * i) * 256 ^ (4 * (j - i)) * w =
      s % (256 ^ (4 * i) * 256 ^ (4 * (j - i))) +
        256 ^ (4 * i) * (256 ^ (4 * (j - i)) * w) := by ring
  rw [hrw, Nat.add_mul_div_left _ _ hpos]
  rw [Nat.mod_mul_right_div_self]
  have h4 : 4 ≤ 4 * (j - i) := by omega
  obtain ⟨k, hk⟩ := Nat.pow_dvd_pow 256 h4
  rw [hk, Nat.mul_assoc, Nat.add_mul_mod_self_left,
    Nat.mod_mod_of_dvd _ ⟨k, rfl⟩]

/-- The new word of the scale accumulator: element `j` of the load is word `j` of the state. -/
theorem scaleWord_update {s j w : Nat} (hw : w < 256 ^ 4) :
    (s % 256 ^ (4 * j) + 256 ^ (4 * j) * w) / 256 ^ (4 * j) % 256 ^ 4 = w := by
  have hpos : 0 < 256 ^ (4 * j) := pow_pos (by norm_num) _
  rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (Nat.mod_lt _ hpos), Nat.zero_add,
    Nat.mod_eq_of_lt hw]

/-- **The scale load's accumulator advances by one word**: after element `j`, the pending values
are the words before it and the word it read. -/
theorem accAt_scale_succ {d : D} {r : Fin 4} {j : Fin 4} (hd : d.site = .scale r j)
    {w : Nat} (hw : w < 256 ^ 4) (hj : j.val + 1 < 4) :
    accAt { d with
      site := .scale r ⟨j.val + 1, hj⟩
      sc := d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * w } =
      accAt d ++ [b32 w] := by
  rw [accAt_of_scale (d := { d with
        site := .scale r ⟨j.val + 1, hj⟩
        sc := d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * w }) (r := r)
      (j := ⟨j.val + 1, hj⟩) rfl,
    accAt_of_scale hd, List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    show b32 (scaleWord { d with
        site := .scale r ⟨j.val + 1, hj⟩
        sc := d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * w } i) = b32 (scaleWord d i)
    congr 1
    exact scaleWord_low hi
  · rw [List.cons.injEq]
    exact ⟨by congr 1; exact scaleWord_update hw, rfl⟩

/-- A site that is not a scale element has sub-step zero. -/
theorem Site.sub_eq_zero_of_not_scale {s : Site} (h : ∀ r j, s ≠ .scale r j) : s.sub = 0 := by
  cases s with
  | scale r j => exact absurd rfl (h r j)
  | _ => rfl

/-- A raw load returns one 64-bit word of finite e4m3 values. -/
def RawWordOk (word : Nat) : Prop :=
  word < 2 ^ 64 ∧ ∀ i : Fin 8, Numeric.byteAt word i.val ≠ 127 ∧ Numeric.byteAt word i.val ≠ 255

instance (word : Nat) : Decidable (RawWordOk word) := by unfold RawWordOk; infer_instance

/-- The sixteen scale bytes exclude the ue8m0 NaN pattern. -/
def ScaleWordOk (word : Nat) : Prop :=
  ∀ i : Fin 16, Numeric.byteAt word i.val < 255

instance (word : Nat) : Decidable (ScaleWordOk word) := by unfold ScaleWordOk; infer_instance

/-- The values held in the row's scale, current raw and prefetched registers are finite. -/
def PayloadOk (d : D) : Prop :=
  match d.site with
  | .raw _ s => ScaleWordOk d.sc ∧ (s.val ≠ 0 → RawWordOk d.raw)
  | .store _ s => ScaleWordOk d.sc ∧ RawWordOk d.raw ∧ (s.val + 1 < 8 → RawWordOk d.nxt)
  | _ => True

/-- **The role's loop invariant**: the ring slot is the block's slot of the two-slot buffer
ring, the parity counts the ring's phases, the block is one of the row's padded blocks with its
cache tag, and the dequantizer's positions fit the two shared buffers. -/
structure Inv (P : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The ring slot is one of the two buffers. -/
  bufLt : d.buf < 2
  /-- The parity is a bit. -/
  parLt : d.par < 2
  /-- The ring slot is the block's position in the two-slot ring. -/
  bufBlock : d.buf = d.block % 2
  /-- The parity counts the ring's phases. -/
  parBlock : d.par = d.block / 2 % 2
  /-- The first length is the row's runtime main-cache length. -/
  len0 : d.len0 = P.topkLen (eOf L g)
  /-- The second length is the row's runtime extra-cache length. -/
  len1 : d.len1 = P.extraTopkLen (eOf L g)
  /-- The block is one of the row's padded blocks. -/
  block : d.block < totalBlocks d.len0 d.len1
  /-- The tag is the block's: the extra cache's blocks follow the main cache's. -/
  extra : d.extra = isExtraBlock d.block d.len0
  /-- The dequantizer's group index is one of the warpgroup's 16. -/
  groupLt : groupIdx L g < numGroups
  /-- The dequantizer's lane in its group is one of the 8. -/
  idxLt : idxInGroup L g < groupSize
  /-- A raw word of the block fits the block's raw buffer. -/
  rawFit : ∀ lr < rowsPerGroup,
    rawWordOff L g lr (numSteps - 1) + rawBytesPerThread ≤ rawBufBytes
  /-- A scale row of the block fits the block's raw buffer. -/
  scaleFit : ∀ lr < rowsPerGroup, scaleRowOff L g lr + scaleLoadBytes ≤ rawBufBytes
  /-- A tile chunk of the block fits the block's bf16 tile. -/
  tileFit : ∀ lr < rowsPerGroup, tileOff L g lr (numSteps - 1) + 16 ≤ dequantBytes
  /-- The `bar_q_utccp` wait is the first block's: the body's first pass resets the ring slot,
  the parity and the block counter (pcs 2654, 2665, 2666). -/
  qUtccpBlock : d.site = .qUtccp → d.block = 0
  /-- The two runtime lengths fit 31 signed bits, so the block-count arithmetic's signed
  ceiling (`ku::ceil`) does not overflow. The launch's `topk`/`extra_topk` budgets give it for
  the row's lengths (`Pre.topkRange`, `Pre.extraTopkRange`). -/
  lenLt : d.len0 < 2 ^ 31 ∧ d.len1 < 2 ^ 31
  /-- The CTA is a row of the batch, so `Pre.paddedRange` bounds its padded count. -/
  batch : eOf L g < P.b
  /-- The dequantizer reads finite raw elements and scales. -/
  payloadOk : PayloadOk d

/-- The first site of the role: the site of its first event under the parameters' length
pointers. A null length pointer reads the parameter's constant instead of the row's runtime
length, so the role's first event is then the next one. -/
def firstSite (P : Params) : Site :=
  if P.topkLenBase.isSome then .lenOrig
  else if P.extraTopkLenBase.isSome then .lenExtra
  else .qUtccp

/-- The initial state: the first site, block 0, ring slot 0 with parity 0, the main cache's tag
(block 0 is a main-cache block) and the two lengths the parameters give. -/
def init (P : Params) (L : Launch) (g : Nat) : D where
  site := firstSite P
  block := 0
  buf := 0
  par := 0
  extra := false
  len0 := P.topkLen (eOf L g)
  len1 := P.extraTopkLen (eOf L g)
  raw := 0
  nxt := 0
  sc := 0

/-- The pre-loop length reads complete before the ring counters are initialized. -/
def lenOrigNext (P : Params) (L : Launch) (g : Nat) : D :=
  { init P L g with site := if P.extraTopkLenBase.isSome then .lenExtra else .qUtccp }

def lenExtraNext (P : Params) (L : Launch) (g : Nat) : D :=
  { init P L g with site := .qUtccp }

/-- The block hand-off after the two arrivals: the next block in the ring slot's successor with
the parity flipped when it leaves the slot (`%r457 = par != buf ? 1 : 0`), or the final
barrier. -/
def afterFree (d : D) : D :=
  if d.block + 1 < totalBlocks d.len0 d.len1 then
    { d with
      site := .rawReady
      block := d.block + 1
      buf := 1 - d.buf
      par := if d.par = d.buf then 0 else 1
      extra := isExtraBlock (d.block + 1) d.len0 }
  else
    { d with site := .barrier }

/-! ## The register table

The scalar table covers launch reads, block counts, ring fields, geometry and shared addresses.
`payloadFacts` tracks unpacked scale bytes, input pairs, pending raw words and packed stores.
-/

/-- The registers the role tracks. -/
def tracked : List Nat :=
  [134, 351, 457, 459, 460, 461, 463, 464, 466, 512, 513, 514, 515, 516, 517, 518, 2429, 2430,
   2431, 2432, 2433, 2434, 2435, 2436, 2437, 2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445,
   2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460,
   2461, 2462, 2472, 2552, 2632, 2712, 2783, 2784, 2787, 2788, 2789, 2791, 2792,
   2793, 2794, 2795, 2796, 2817,
   2878, 2879, 2985, 2986, 2987, 2988, 2991, 553, 3833, 3835, 130, 131, 132, 3017, 3018]

/-- The scale byte registers are filled from the highest source word down. -/
def scaleByteFacts (r : Fin 4) (d : D) : List (Nat × Value) :=
  (List.range 16).map fun j =>
    (353 + 24 * r.val + j,
      .bits 16 (BitVec.ofNat 64 (scaleWord d (3 - j / 4) / 256 ^ ((j + 2) % 4) % 256)))

/-- The current raw word's four packed e4m3 pairs. -/
def rawPairFacts (r : Fin 4) (step w : Nat) : List (Nat × Value) :=
  (List.range 4).map fun j =>
    (192 + 40 * r.val + 5 * step + j, .bits 16 (BitVec.ofNat 64 (w / 2 ^ (16 * j) % 2 ^ 16)))

/-- Position of the chunk in the four rows unrolled by the compiler. -/
def chunkIndex (r : Fin 4) (s : Fin 8) : Nat := 8 * r.val + s.val

def chunkPackReg (r : Fin 4) (s : Fin 8) : Nat := 4039 + chunkIndex r s

def storeBaseReg (r : Fin 4) (s : Fin 8) : Nat := 2472 + 10 * chunkIndex r s

/-- Destination of an eight-byte shared load of the raw input. -/
def rawLoadReg (r : Fin 4) (s : Nat) : Nat := 3837 + 48 * r.val + (6 * s - 2)

/-- The store keeps its address and packed value, and a prefetched word until the next chunk. -/
def storePayload (L : Launch) (g : Nat) (r : Fin 4) (s : Fin 8) (d : D) :
    List (Nat × Value) :=
  [(chunkPackReg r s, Numeric.dequantChunk d.raw (Numeric.byteAt d.sc (scaleIdx L g s.val))),
   (storeBaseReg r s, sb L (tileBase d.buf + tileOff L g r.val s.val))] ++
  (if s.val + 1 < 8 then [(rawLoadReg r (s.val + 1), b64 d.nxt)] else []) ++ scaleByteFacts r d

/-- Register facts for raw loads and tile stores. -/
def payloadFacts (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  match d.site with
  | .raw r s =>
    scaleByteFacts r d ++ if s.val = 0 then [] else rawPairFacts r (s.val - 1) d.raw
  | .store r s => storePayload L g r s d
  | _ => []

/-- The registers of state `d` with their values. The six sign-correction words of the two
`ku::ceil` computations (`%r2431`, `%r2432`, `%r2438`, `%r2439`, `%r2447`, `%r2448`) are zero:
`Pre` gives `topkLen ≤ topk` and `extraTopkLen ≤ extra_topk` with `s_q * topk < 2 ^ 31`, so the
lengths are nonnegative and below `2 ^ 31`, and the `shr.s32 x 31` / `shr.u32 0 >> 26` trick adds
nothing. -/
def table (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let t := tidOf L g
  let gp := groupIdx L g
  let ix := idxInGroup L g
  let rowa := rowInAtom L g
  let orig := origPadded d.len0
  let total := totalBlocks d.len0 d.len1
  let padded := orig + ceilToMultiple d.len1 topkBlock
  [(459, b32 (ctaidX L g)), (460, b32 (ctaidY L g)), (461, b32 t), (463, b32 (t % 128)),
   (464, b32 (t / 32)), (466, b32 (t % 32)),
   (2991, .ptr 64 false (.param (param "0")) 0), (553, sb L 0),
   -- before the `topk_length` read (`%r2985` is live before it) the register holds the
   -- parameter's constant; the runtime length replaces it at pc 2620
   (2429, b32 P.b), (2985, b32 (if d.site = .lenOrig then P.topk else d.len0)),
   -- before the `extra_topk_length` read (`%r2986` is live before it) the register holds the
   -- parameter's constant; the runtime length replaces it at pc 2630
   (2986, b32 (if d.site = .lenOrig ∨ d.site = .lenExtra then P.extra_topk else d.len1)),
   (3017, b64 (Thread.paramWord L 80 8)), (3018, b64 (Thread.paramWord L 144 8)),
   (130, .pred (decide (P.b ≤ ctaidY L g))),
   (131, .pred (Thread.ptrIsNull L 80)), (132, .pred (Thread.ptrIsNull L 144)),
   (2430, b32 (d.len0 + 63)), (2437, b32 (d.len1 + 63)),
   (514, b32 (ceilToMultiple d.len0 topkBlock)),
   (2441, b32 (ceilToMultiple d.len1 topkBlock)),
   (2442, b32 orig), (515, b32 padded),
   (2431, b32 0), (2432, b32 0), (2433, b32 (d.len0 + 63)),
   (2438, b32 0), (2439, b32 0), (2440, b32 (d.len1 + 63)),
   (2443, b32 (d.len1 + 63 + orig)),
   -- the difference `ceil - (len1 + 63)` wraps to the 32-bit word; equal to its natural
   -- value except when the padded length is already a multiple of 64 (then both are 2 ^ 32)
   (2444, b32 ((ceilToMultiple d.len1 topkBlock + (2 ^ 32 - (d.len1 + 63))) % 2 ^ 32)),
   (2447, b32 0), (2448, b32 0), (2449, b32 padded), (2450, b32 total),
   (512, b32 gp), (513, b32 ix), (134, .pred (groupSize / 2 ≤ ix)),
   (2446, b32 rowa),
   (2451, b32 (rowa ^^^ ix)), (2452, b32 ((rowa ^^^ ix) * 16)),
   (2453, b32 (gp * 128)), (2454, b32 (rowa * 128)), (2455, b32 (t * 16)),
   (2456, b32 (gp / 8 * 1024)), (2457, b32 (rowa * 128 ||| gp / 8 * 1024)),
   (516, b32 (dstOff L g)), (517, b32 (ix * rawBytesPerThread)),
   (518, b32 (gp * rawRowStride)),
   (351, .bits 16 (BitVec.ofNat 64 d.par)), (457, .bits 16 (BitVec.ofNat 64 d.par)),
   (2435, b32 d.par), (2459, b32 d.par), (2462, b32 (1 - d.par)),
   (2436, b32 10000000), (2460, b32 10000000),
   (2445, sb L 0), (2787, sb L 0), (2788, sb L (8 * d.buf)),
   (2434, sb L qUtccpOff), (2458, sb L (rawReadyOff d.buf)),
   (2461, sb L (svDoneOff d.buf)), (2783, sb L (dequantReadyOff d.buf)),
   (2784, sb L (rawFreeOff d.buf)), (2789, b32 (2 ^ 32 - 1 - d.buf)),
   (2791, sb L (rawBase 1)), (2792, sb L (rawBase 0)),
   (2794, sb L (tileBase 1)),
   (2793, sb L (rawBase d.buf)), (2795, sb L (tileBase d.buf)),
   (2472, sb L (tileBase d.buf + dstOff L g)),
   (2552, sb L (tileBase d.buf + tileOff L g 1 0)),
   (2632, sb L (tileBase d.buf + tileOff L g 2 0)),
   (2712, sb L (tileBase d.buf + tileOff L g 3 0)),
   (2796, sb L (rawBase d.buf + rawRowOff L g 0)),
   (2817, sb L (rawBase d.buf + rawWordOff L g 0 0)),
   (2987, b32 (d.block + (2 ^ 32 - total))), (2988, b32 d.buf),
   -- the two `.nc` length addresses: the row's pointer word plus four bytes per batch
   (3833, b64 ((Thread.paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (3835, b64 ((Thread.paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (2878, b32 12), (2879, b32 384)]

/-- The value of a register at state `d`: the table's, else the zero word. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table P L g d).lookup r).getD (b32 0)

/-- The facts of state `d`: the live registers the role tracks, with their table values. -/
def baseFacts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsFrom ((Flow.live d.site.pc).filter fun r => tracked.contains r) (valueOf P L g d)

/-- The facts of state `d` at an arbitrary program counter: the registers tracked and live
there, with the state's table values. The checkpoints of the role's long local segments use it
between two sites. -/
def atFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) : List (Nat × Value) :=
  factsFrom ((Flow.live pc).filter fun r => tracked.contains r) (valueOf P L g d)

/-- Every site carries its control and address facts and any live dequantization values. -/
def facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  payloadFacts L g d ++ baseFacts P L g d

theorem baseFacts_eq_atFacts {P : Params} {L : Launch} {g : Nat} {d : D} :
    baseFacts P L g d = atFacts P L g d d.site.pc := rfl

/-- A concrete state of an abstract state: at the site's program counter and sub-step, with the
site's facts and the values its vector load has returned so far. -/
def AtD (P : Params) (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = accAt d ∧ t.fault = none ∧
    Holds t.regs (facts P L g d)

theorem AtD.baseRegs {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : AtD P L g d t) : Holds t.regs (baseFacts P L g d) :=
  ((holds_append _ _ _).mp h.2.2.2.2).2

theorem AtD.payloadRegs {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : AtD P L g d t) : Holds t.regs (payloadFacts L g d) :=
  ((holds_append _ _ _).mp h.2.2.2.2).1

/-- A concrete state of a state outside a scale load: the sub-step and accumulator are the
empty ones. -/
theorem at_of_atD {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (hat : AtD P L g d t) (hd : ∀ r j, d.site ≠ .scale r j) :
    At t d.site.pc (baseFacts P L g d) :=
  ⟨hat.1, by rw [hat.2.1]; exact Site.sub_eq_zero_of_not_scale hd,
    by rw [hat.2.2.1]; exact accAt_of_not_scale hd,
    hat.2.2.2.1, hat.baseRegs⟩

/-! ## The successor relation -/

/-- The successor of a `scale` site: the next element of the load, the next row's load, or the
first raw word. -/
def afterScale (r : Fin 4) (j : Fin 4) : Site :=
  if hj : j.val + 1 < 4 then .scale r ⟨j.val + 1, hj⟩ else .raw r ⟨0, by decide⟩

/-- The successor of a raw word: the row's next word, else the store of the step it pairs with
(the compiler reads step `s + 1` before storing step `s`). -/
def afterRaw (r : Fin 4) (s : Fin 8) : Site :=
  if s.val = 0 then .raw r ⟨1, by omega⟩
  else .store r ⟨s.val - 1, by have := s.isLt; omega⟩

/-- The successor of a store: the next step's raw word, or the last step's store, or the next
row's scale load, or the fence. -/
def afterStore (r : Fin 4) (s : Fin 8) : Site :=
  if h2 : s.val + 2 < 8 then .raw r ⟨s.val + 2, h2⟩
  else if h1 : s.val + 1 < 8 then .store r ⟨s.val + 1, h1⟩
  else if h : r.val + 1 < 4 then .scale ⟨r.val + 1, h⟩ ⟨0, by decide⟩
  else .fence

/-- The abstract successor after event `e`.

A length load continues only on the row's runtime length (`Assumption.ncReadOnly` fixes its
bytes to the launch content). A wait continues to the next site on success and stays at the
wait otherwise. A shared load continues on an access of its size at the site's address and
records the returned bits. A store continues only on
a shared write of 16 bytes at the chunk's address. The two arrivals continue unconditionally,
and the last block hands off to the named barrier. -/
def nextSite (P : Params) (L : Launch) (g : Nat) (s : Site) (d : D) (e : Event) :
    Option (Option D) :=
  match s with
    | .lenOrig =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.topkLen (eOf L g)) then
            some (some (lenOrigNext P L g))
          else some none
        | .error _ => some none
      | _ => none
    | .lenExtra =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.extraTopkLen (eOf L g)) then
            some (some (lenExtraNext P L g))
          else some none
        | .error _ => some none
      | _ => none
    | .qUtccp =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .rawReady } else d))
      | _ => none
    | .rawReady =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .svDone } else d))
      | _ => none
    | .svDone =>
      match e.kind with
      | .wait _ _ ok _ _ =>
        some (some (if ok then { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ }
          else d))
      | _ => none
    | .scale r j =>
      match e.kind with
      | .rd a bs =>
        if a.loc = ⟨.shared, ctaOf L g,
              L.sharedBase + rawBase d.buf + scaleRowOff L g r.val + 4 * j.val⟩ ∧
            a.size = 4 then
          -- the element is a 32-bit word: the bytes rebuild to the value the state records
          match rebuild 3 bs with
          | .ok v =>
            if v = b32 (scaleBits bs) then
              let d' := { d with
                site := afterScale r j
                sc := d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * scaleBits bs }
              if j.val = 3 ∧ ¬ ScaleWordOk d'.sc then some none else some (some d')
            else some none
          | .error _ => some none
        else some none
      | _ => none
    | .raw r s =>
      match e.kind with
      | .rd a bs =>
        if a.loc = ⟨.shared, ctaOf L g,
              L.sharedBase + rawBase d.buf + rawWordOff L g r.val s.val⟩ ∧
            a.size = rawBytesPerThread then
          if rebuild 3 bs = .ok (b64 (rawBits bs)) ∧ RawWordOk (rawBits bs) then
            some (some (if s.val = 0 then
              { d with site := afterRaw r s, raw := rawBits bs }
            else
              { d with site := afterRaw r s, nxt := rawBits bs }))
          else some none
        else some none
      | _ => none
    | .store r s =>
      match e.kind with
      | .wr a _ =>
        if a.loc = ⟨.shared, ctaOf L g,
              L.sharedBase + tileBase d.buf + tileOff L g r.val s.val⟩ ∧
            a.size = 16 then
          -- the word the next store converts is the one the loop read ahead; after the row's
          -- last store there is none until the next row's first load
          some (some (if s.val + 1 < 8 then
            { d with site := afterStore r s, raw := d.nxt, nxt := d.nxt }
          else
            { d with site := afterStore r s, raw := 0, nxt := 0 }))
        else some none
      | _ => none
    | .fence =>
      match e.kind with
      | .fenceProxy _ _ => some (some { d with site := .ready })
      | _ => none
    | .ready =>
      match e.kind with
      | .arrive _ _ _ _ _ => some (some { d with site := .free })
      | _ => none
    | .free =>
      match e.kind with
      | .arrive _ _ _ _ _ => some (some (afterFree d))
      | _ => none
    | .barrier =>
      match e.kind with
      | .bar _ _ _ => some none
      | _ => none

/-- The abstract successor after event `e`: the site the state is at decides it. -/
def next (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  nextSite P L g d.site d e

/-- The named barrier has no continuing event: the thread's next instruction is the program's
`ret`, which belongs to the `done` role. -/
theorem nextSite_barrier (P : Params) (L : Launch) (g : Nat) (d : D) {a b : Nat}
    {c : Option Nat} {m : BarMode} : nextSite P L g .barrier d ⟨a, .bar b c m⟩ = some none := rfl

/-- The role's code machine. -/
def code (P : Params) (L : Launch) (g : Nat) : Code kernel asms L g where
  D := D
  init := init P L g
  pc := fun d => d.site.pc
  facts := facts P L g
  sub := fun d => d.site.sub
  acc := accAt
  inv := Inv P L g
  next := next P L g

/-! ## The sites are events -/

/-- The pcs of the role's event instructions, in program order. -/
def eventPcs : List Nat :=
  [2620, 2630, 2644, 2677, 2684, 2695, 2920, 3145, 3370] ++
    [2729, 2737, 2760, 2784, 2808, 2832, 2856, 2880,
     2954, 2962, 2985, 3009, 3033, 3057, 3081, 3105,
     3179, 3187, 3210, 3234, 3258, 3282, 3306, 3330,
     3404, 3412, 3435, 3459, 3483, 3507, 3531, 3555] ++
    [2752, 2776, 2800, 2824, 2848, 2872, 2896, 2919,
     2977, 3001, 3025, 3049, 3073, 3097, 3121, 3144,
     3202, 3226, 3250, 3274, 3298, 3322, 3346, 3369,
     3427, 3451, 3475, 3499, 3523, 3547, 3571, 3594] ++
    [3595, 3597, 3599, 3610]

/-- Every pc of `eventPcs` holds an unguarded event instruction. -/
theorem eventPcs_ok :
    eventPcs.all (fun pc => match codeAt pc with
      | some i => !i.op.isLocal && i.guard.isNone
      | none => false) = true := by
  decide +kernel

/-- A site's pc is one of the role's event pcs. -/
theorem mem_eventPcs (s : Site) : s.pc ∈ eventPcs := by
  cases s with
  | scale r j =>
    have h : r.val < 4 := r.isLt
    simp only [Site.pc]
    interval_cases r.val <;> decide
  | raw r s =>
    have h1 : r.val < 4 := r.isLt
    have h2 : s.val < 8 := s.isLt
    simp only [Site.pc]
    interval_cases r.val <;> interval_cases s.val <;> decide
  | store r s =>
    have h1 : r.val < 4 := r.isLt
    have h2 : s.val < 8 := s.isLt
    simp only [Site.pc]
    interval_cases r.val <;> interval_cases s.val <;> decide
  | lenOrig => decide
  | lenExtra => decide
  | qUtccp => decide
  | rawReady => decide
  | svDone => decide
  | fence => decide
  | ready => decide
  | free => decide
  | barrier => decide

/-- Every site is an unguarded event instruction of the decoded program: the site's pc holds an
instruction that performs an event and has no guard, so the machine's guard obligation is
immediate. -/
theorem site_event (P : Params) (L : Launch) (g : Nat) (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts P L g d) ins.guard := by
  have hok := List.all_eq_true.mp eventPcs_ok d.site.pc (mem_eventPcs d.site)
  rcases h : codeAt d.site.pc with _ | ins
  · rw [h] at hok
    exact absurd hok (by decide)
  · rw [h] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hok
    exact ⟨ins, h, hok.1, by rw [hok.2]; trivial⟩

/-! ## The invariant's arithmetic -/

/-- The code's parity flip (`%r457 = par != buf ? 1 : 0`) is the parity of the next block. -/
theorem par_flip (b : Nat) :
    (if b / 2 % 2 = b % 2 then 0 else 1) = (b + 1) / 2 % 2 := by
  have hq : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have e0 : b % 2 = 0 → (b + 1) / 2 = b / 2 := by omega
  have e1 : b % 2 = 1 → (b + 1) / 2 = b / 2 + 1 := by omega
  rcases hq with h | h
  · rw [e0 h, h]
    split_ifs with h'
    · exact h'.symm
    · have h1 : b / 2 % 2 = 1 := by omega
      rw [h1]
  · rw [e1 h, h]
    split_ifs with h'
    · have h1 : (b / 2 + 1) % 2 = 0 := by omega
      rw [h1]
    · have h1 : (b / 2 + 1) % 2 = 1 := by omega
      rw [h1]

/-- The code's slot flip (`%r2988 = ~buf & 1`) is the next block's slot. -/
theorem buf_flip (b : Nat) : 1 - b % 2 = (b + 1) % 2 := by omega

/-- Block 0 is a main-cache block: the row has at least one main-cache block. -/
theorem isExtraBlock_zero (len : Nat) : isExtraBlock 0 len = false := by
  unfold isExtraBlock
  rw [decide_eq_false_iff_not]
  have := numOrigBlocks_pos len
  omega

/-- **The block hand-off preserves the loop invariant**: the ring slot is the next block's
slot, the parity is the next block's phase, and the tag is the next block's. -/
theorem handoff_inv {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d) :
    Inv P L g (afterFree d) := by
  unfold afterFree
  split
  · rename_i hstep
    refine ⟨?_, ?_, ?_, ?_, h.len0, h.len1, hstep, rfl, h.groupLt, h.idxLt, h.rawFit,
      h.scaleFit, h.tileFit, ?_, h.lenLt, h.batch, trivial⟩
    · show 1 - d.buf < 2
      omega
    · show (if d.par = d.buf then 0 else 1) < 2
      split <;> omega
    · show 1 - d.buf = (d.block + 1) % 2
      rw [h.bufBlock, buf_flip]
    · show (if d.par = d.buf then 0 else 1) = (d.block + 1) / 2 % 2
      rw [h.parBlock, h.bufBlock, par_flip]
    · intro hq
      simp at hq
  · refine ⟨h.bufLt, h.parLt, h.bufBlock, h.parBlock, h.len0, h.len1, h.block, h.extra,
      h.groupLt, h.idxLt, h.rawFit, h.scaleFit, h.tileFit, ?_, h.lenLt, h.batch, trivial⟩
    intro hq
    simp at hq

/-- A change of site leaves the ring and geometry facts unchanged. -/
theorem inv_setSite {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d) (s : Site)
    (hs : s ≠ .qUtccp) (hpayload : PayloadOk { d with site := s } := by trivial) :
    Inv P L g { d with site := s } :=
  ⟨h.bufLt, h.parLt, h.bufBlock, h.parBlock, h.len0, h.len1, h.block, h.extra, h.groupLt,
    h.idxLt, h.rawFit, h.scaleFit, h.tileFit, fun hq => absurd hq hs, h.lenLt, h.batch, hpayload⟩

/-- The launch's sparse budget fits 31 signed bits. -/
theorem topk_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    P.topk < 2 ^ 31 := by
  have h1 := hpre.topkRange
  have h2 := Nat.le_mul_of_pos_left P.topk hpre.sqPos
  omega

/-- The launch's extra sparse budget fits 31 signed bits. -/
theorem extra_topk_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    P.extra_topk < 2 ^ 31 := by
  have h1 := hpre.extraTopkRange
  have h2 := Nat.le_mul_of_pos_left P.extra_topk hpre.sqPos
  omega

/-- The row's main-cache runtime length fits 31 signed bits. -/
theorem topkLen_lt {P : Params} {L : Launch} {mem0 : Mem0} {e : Nat}
    (hpre : Pre P L mem0) (h : e < P.b) : P.topkLen e < 2 ^ 31 := by
  have hp := hpre.paramTopkLen
  cases hb : P.topkLenBase with
  | none =>
    rw [hb] at hp
    rw [hp.2 e h]
    exact topk_lt hpre
  | some x =>
    rw [hb] at hp
    exact lt_of_le_of_lt (((hp.2.2 e h) 0 (by omega)).2 e h) (topk_lt hpre)

/-- The row's extra-cache runtime length fits 31 signed bits. -/
theorem extraTopkLen_lt {P : Params} {L : Launch} {mem0 : Mem0} {e : Nat}
    (hpre : Pre P L mem0) (h : e < P.b) : P.extraTopkLen e < 2 ^ 31 := by
  have hp := hpre.paramExtraTopkLen
  cases hb : P.extraTopkLenBase with
  | none =>
    rw [hb] at hp
    rw [hp.2 e h]
    exact extra_topk_lt hpre
  | some x =>
    rw [hb] at hp
    exact lt_of_le_of_lt (((hp.2.2 e h) 0 (by omega)).2 e h) (extra_topk_lt hpre)

/-- The initial state satisfies the invariant, given the launch's data and the CTA's place in
the grid (the two lengths it starts from are the row's runtime lengths). -/
theorem init_inv {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (g : Nat) (hb : eOf L g < P.b) : Inv P L g (init P L g) := by
  have hpos : 0 < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) :=
    totalBlocks_pos _ _
  refine ⟨by simp [init], by simp [init], by simp [init], by simp [init], rfl, rfl, ?_,
    ?_, groupLt L g, idxInGroup_lt L g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [init] using hpos
  · simp [init, isExtraBlock_zero]
  · intro lr hlr
    exact rawWord_fit (L := L) (g := g) (lr := lr) (s := numSteps - 1) hlr
      (by unfold numSteps; omega)
  · intro lr hlr
    exact scaleRow_fit (L := L) (g := g) (lr := lr) hlr
  · intro lr hlr
    exact tile_fit (L := L) (g := g) (lr := lr) (s := numSteps - 1) hlr
      (by unfold numSteps; omega)
  · intro _
    simp [init]
  · exact ⟨by simpa [init] using topkLen_lt hpre hb,
      by simpa [init] using extraTopkLen_lt hpre hb⟩
  · exact hb
  · unfold init firstSite
    split
    · trivial
    · split <;> trivial

/-! ## The tag is not read

Both `Dequantizer` instantiations are `KVBlockDequantizer<KVCacheFormat<V41>, ...>`
(`kernel.cuh:645-646`), so `bytesPerToken`, `QUANT_BYTES`, `QUANT_TILE_SIZE`,
`RAW_TOKEN_SMEM_STRIDE` and the tile layout are the same constants for both caches. These are
the role's whole byte and offset vocabulary, and none of them takes a cache argument: the tag
`D.extra` is recorded for the protocol layer only. -/

/-! ## The entry interface and the role's soundness -/

/-- The prologue's hand-off to the role: a thread state at pc 2607, after the prologue's
`setmaxnreg.inc 208` at pc 2606, with the prologue's registers.

`Proof/Thread/Prologue.lean` stops at warpgroup 2's first event (pc 2606) and its table
(`Prologue.values`) gives these values there; none of these registers is written anywhere else
in the program, so they hold at 2607 too. The registers the role's first instructions read are
`%r2 = %ctaid.y`, `%r3 = %tid.x`, `%r5 = %tid % 128` and `%rd2` (the `param_0` pointer); `%r1 =
%ctaid.x`, `%r6` (the warp index), `%r8` (the lane) and the dynamic shared base are the rest of
the prologue's table and the launch data the role's position and geometry rest on. -/
structure Entry (P : Params) (L : Launch) (g : Nat) (t : TState) : Prop where
  /-- The thread is at pc 2607, after the prologue's `setmaxnreg.inc 208`. -/
  pc : t.pc = 2607
  /-- The state is at an instruction boundary. -/
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  /-- The launch reads and parameter address used at entry. -/
  regs : Holds t.regs (factsFrom [460, 461, 463, 2991]
    (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g))
  /-- The CTA is a batch index of the grid. -/
  batch : ctaidY L g < P.b
  /-- The CTA is a query index of the grid. -/
  query : ctaidX L g < P.s_q

/-- The role's soundness from its entry: the entry state reaches the initial abstract state and
every abstract state's event continues to its successor. -/
structure Sound (P : Params) (L : Launch) (g : Nat) : Prop where
  /-- Local instructions from the prologue's entry facts reach the first site's state. -/
  start : ∀ (mem0 : Mem0) (t : TState), Pre P L mem0 → Entry P L g t →
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g)
  /-- Every site's event reaches its successor's state (`Code.StepAt`), or the role's end. -/
  steps : ∀ d, (code P L g).StepAt d

/-- **The site obligation of every state**: every state sits at an unguarded event
instruction. -/
theorem stepAt_site (P : Params) (L : Launch) (g : Nat) (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts P L g d) ins.guard :=
  site_event P L g d

/-- **`Code.StepAt` reduces to the step alone**: every state's site obligation is `site_event`,
so a state's `StepAt` is its per-event continuation. -/
theorem stepAt_of (P : Params) (L : Launch) (g : Nat) (d : D)
    (hstep : ∀ {t : TState} {e : Event} {u : TState} (ins : Instr),
      (code P L g).AtD d t → Inv P L g d → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) →
      (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)) :
    (code P L g).StepAt d :=
  ⟨fun _ => site_event P L g d, hstep⟩

/-! ## The named barrier's step

The role's last event is `barrier.sync 12, 384`, the whole CTA's `everyone_sync`. Its step is
complete: the facts at pc 3610 are the barrier's two operands, and the machine stops there (the
program's next instruction is the `ret`, role `done`). -/

/-- The two registers live at pc 3610 are the barrier's id and count. -/
theorem facts_barrier {d : D} (hpc : d.site.pc = 3610) :
    2878 ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r) ∧
      2879 ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r) := by
  rw [hpc]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- `barrier.sync 12, 384` with the CTA's block size as its count is the whole CTA's arrival on
the named barrier `12`: `everyone_sync` (`config.h:22-28`, `Data/Barriers.namedBars`). -/
theorem event_barrier {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hat : (code P L g).AtD d t) (hpc : d.site.pc = 3610) :
    eventTmpl asms L g t (.barSyncN (.reg 2878) (.reg 2879) false) =
      .bar 12 (PTX.next t) none .sync := by
  obtain ⟨h1, h2⟩ := facts_barrier (d := d) hpc
  have hm := AtD.baseRegs hat
  have h2878 : t.regs 2878 = some (b32 12) := by
    have h := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 2878) h1)
    simpa [facts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h
  have h2879 : t.regs 2879 = some (b32 384) := by
    have h := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 2879) h2)
    simpa [facts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h
  have h12 : readBits L g t 32 (.reg 2878) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h2878 (by decide)
  have h384 : readBits L g t 32 (.reg 2879) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h2879 (by decide)
  simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
    show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
    show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hpre.block,
    show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and,
    or_true, reduceCtorEq]

/-- **The named barrier's step**: an arrival event of `barrier.sync 12, 384` ends the role (the
thread's next instruction is the `ret`). -/
theorem step_barrier {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .barrier) {t u : TState} {e : Event} {ins : Instr}
    (hat : (code P L g).AtD d t) (_hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 3610 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_15)
  rw [event_barrier hpre hat hpc] at hf
  obtain ⟨he, -⟩ := hf
  refine Or.inl (Or.inl ?_)
  rw [he]
  simp only [next, hd]
  exact nextSite_barrier P L g d

/-- **The named barrier's `StepAt`**: the role's last event sits at an unguarded barrier
instruction and its arrival ends the role. -/
theorem stepAt_barrier {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .barrier) : (code P L g).StepAt d :=
  stepAt_of P L g d fun _ hat hinv hc hf => step_barrier hpre d hd hat hinv hc hf

/-! ## The proxy fence's step and the first arrival's

The fence that publishes the tile to the async proxy, and the arrival it is followed by. Both
have a one-instruction local tail (the `add.s32` that forms the next arrival's address word), so
the address arithmetic is `trunc32_add` with the shared window's bound. -/

/-- The value table's entries, as `simp` reduces them after a segment's evaluation. -/
macro "wg2_values" : tactic =>
  `(tactic| simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- `fence.proxy.async.shared::cta` fires the proxy fence of the async proxy at CTA scope
(`fenceTmpl_asyncCta`): it orders the thread's prior shared writes before its later ones. -/
theorem event_fence {t : TState} :
    eventTmpl asms L g t (.fence (.proxy (.async (some (.shared .cta))))) =
      .fenceProxy (.async (some (.shared .cta))) none (PTX.next t) :=
  fenceTmpl_asyncCta L g t

/-- An arrival whose object and operands evaluate fires the arrival event naming them and
continues at the next instruction (`tmaTmpl`, `mbarStateDest` with no state destination). -/
theorem fires_arrive_next {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {base : Nat} {off : Int} {tx count : Opnd} {cluster rel : Bool} {sc : MbarScope}
    {pc : Nat} {e : Event} {o : Option TState} {m : Loc} {bytes n : BitVec 64}
    (hm : (if cluster then mbarClusterLoc L g t base off else mbarLoc L g t base off) = .ok m)
    (hb : readBits L g t 32 tx = .ok bytes) (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl A L g t (.mbarArrive base off tx count cluster rel sc none)) e o) :
    ∃ rel' sc', e = ⟨pc, .arrive m bytes.toNat n.toNat rel' sc'⟩ ∧ o = some (PTX.next t) := by
  cases cluster <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm <;>
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hb, hn, bind,
      Except.bind, pure, Except.pure, ofExec] at hf <;>
  cases rel <;> cases sc <;> simp only [widenMbarScope] at hf <;> split_ifs at hf <;>
  exact ⟨_, _, hf.1, hf.2⟩

/-- The shared window's base is eight-byte aligned, and so is an mbarrier offset: an address
word of the role is an eight-byte aligned shared address. -/
theorem sharedAddr_align {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {off : Nat} (h : off % 8 = 0) : (L.sharedBase + off) % 8 = 0 := by
  have h8 : L.sharedBase % 8 = 0 := by
    rw [hpre.sharedBase]
    have := hpre.sharedAlignment
    omega
  omega

section
variable {P : Params} {L : Launch} {g : Nat}

/-- **The proxy fence's step**: the fence event and the one `add.s32` that forms
`bar_quant_part_dequant_ready[buf]`'s address word (pc 3596). -/
theorem step_fence {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .fence) {t u : TState}
    {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 3595 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_5)
  rw [event_fence] at hf
  obtain ⟨he, hu⟩ := hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have h0 : At u 3596
      (factsFrom ((Flow.live 3595).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    rw [hu']
    have h5 : At t 3595 (factsFrom ((Flow.live 3595).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
      rw [← hpc]
      exact at_of_atD hat (by rw [hd]; intro r j h; nomatch h)
    exact At.next h5
  have hbnd : L.sharedBase + 8 * d.buf + 222792 < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    have h2 := hinv.bufLt
    omega
  have hword : Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 8 * d.buf)) +
        truncBits 32 (BitVec.ofInt 64 222792))) = sb L (dequantReadyOff d.buf) := by
    refine Eq.trans (congrArg (Value.bits 32)
      (trunc32_add (x := L.sharedBase + 8 * d.buf) (c := 222792) (by omega) hbnd)) ?_
    rw [show L.sharedBase + 8 * d.buf + 222792 = L.sharedBase + (222792 + 8 * d.buf) by omega]
    rfl
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3597 (factsFrom ((Flow.live 3597).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .ready })) := by
    seg_fp h0 using
      try wg2_values
      all_goals exact hword
  refine Or.inl (Or.inr ⟨{ d with site := .ready }, t', ?_, run_rtg hr, ht, ?_⟩)
  · rw [next, he, hd]
    rfl
  · exact inv_setSite hinv .ready (by decide)

/-- **The proxy fence's `StepAt`**. -/
theorem stepAt_fence {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .fence)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun _ hat hinv hc hf => step_fence hpre d hd hat hinv hc hf

/-- **The first arrival's step**: `mbarrier.arrive` on `bar_quant_part_dequant_ready[buf]`
(pc 3597), whose address word the fence's segment formed, and the one `add.s32` that forms
`bar_raw_free[buf]`'s address word (pc 3598). -/
theorem step_ready {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .ready) {t u : TState}
    {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 3597 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_8)
  have hop : (⟨none, .mbarArrive 2783 0 (.imm 0) (.imm 1) false true .cta none⟩ : Instr).op =
      .mbarArrive 2783 0 (.imm 0) (.imm 1) false true .cta none := rfl
  rw [hop] at hf
  have h2783 : t.regs 2783 = some (sb L (dequantReadyOff d.buf)) := by
    have hmem : 2783 ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r) := by
      rw [hpc]; decide +kernel
    have h := holds_mem (AtD.baseRegs hat) (mem_factsFrom (val := valueOf P L g d) (r := 2783) hmem)
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h
  have hb : L.sharedBase + dequantReadyOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    unfold dequantReadyOff
    have h2 := hinv.bufLt
    omega
  have hm : mbarLoc L g t 2783 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + dequantReadyOff d.buf⟩ :=
    mbarLoc_b32 h2783 hb (sharedAddr_align hpre (by unfold dequantReadyOff; omega))
  rw [hpc] at hf
  obtain ⟨rel', sc', he, hu⟩ := fires_arrive_next (A := asms) (t := t) (base := 2783)
    (off := 0) (tx := .imm 0) (count := .imm 1) (cluster := false) (rel := true) (sc := .cta)
    (pc := 3597) (e := e) (o := some u)
    (m := ⟨.shared, g / L.block, L.sharedBase + dequantReadyOff d.buf⟩)
    (bytes := truncBits 32 (BitVec.ofInt 64 0)) (n := truncBits 32 (BitVec.ofInt 64 1))
    hm (by simp [readBits, pure, Except.pure]) (by simp [readBits, pure, Except.pure]) hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have h0 : At u 3598
      (factsFrom ((Flow.live 3597).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    rw [hu']
    have h5 : At t 3597 (factsFrom ((Flow.live 3597).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
      rw [← hpc]
      exact at_of_atD hat (by rw [hd]; intro r j h; nomatch h)
    exact At.next h5
  have hbnd : L.sharedBase + 8 * d.buf + 222824 < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    have h2 := hinv.bufLt
    omega
  have hword : Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 8 * d.buf)) +
        truncBits 32 (BitVec.ofInt 64 222824))) = sb L (rawFreeOff d.buf) := by
    refine Eq.trans (congrArg (Value.bits 32)
      (trunc32_add (x := L.sharedBase + 8 * d.buf) (c := 222824) (by omega) hbnd)) ?_
    rw [show L.sharedBase + 8 * d.buf + 222824 = L.sharedBase + (222824 + 8 * d.buf) by omega]
    rfl
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3599 (factsFrom ((Flow.live 3599).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .free })) := by
    seg_fp h0 using
      try wg2_values
      all_goals exact hword
  refine Or.inl (Or.inr ⟨{ d with site := .free }, t', ?_, run_rtg hr, ht, ?_⟩)
  · rw [next, he, hd]
    rfl
  · exact inv_setSite hinv .free (by decide)

/-- **The first arrival's `StepAt`**. -/
theorem stepAt_ready {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .ready)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun _ hat hinv hc hf => step_ready hpre d hd hat hinv hc hf

/-! ## Reading the role's facts

The steps below evaluate a site's local tail from the facts of the state at the site. These
helpers turn a tracked, live register into its stated value, carry a fired poll's predicate into
the next instruction's facts, and restate a state's facts at a concrete program counter. -/

/-- A tracked register that is live at the state's site holds the table's value. -/
theorem AtD.reg {d : D} {t : TState} (h : AtD P L g d t) {r : Nat}
    (hm : r ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  have hh := holds_mem h.baseRegs (mem_factsFrom (val := valueOf P L g d) hm)
  simpa [baseFacts] using hh

/-- A register live at a pcs-`pc` state, valued by the facts of state `d`. -/
theorem AtD.regAt {d : D} {t : TState} (h : AtD P L g d t) {pc : Nat} (hpc : d.site.pc = pc)
    {r : Nat} (hm : r ∈ (Flow.live pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  subst hpc
  exact h.reg hm

/-- A scalar checkpoint with the state's payload and register facts gives its concrete state. -/
theorem AtD.of_all_facts {d : D} {t : TState} {pc : Nat} (hpc : d.site.pc = pc)
    (hsub : d.site.sub = 0) (hacc : accAt d = [])
    (h : At t pc (payloadFacts L g d ++ atFacts P L g d pc)) : AtD P L g d t := by
  refine ⟨h.1.trans hpc.symm, h.2.1.trans hsub.symm, h.2.2.1.trans hacc.symm, h.2.2.2.1, ?_⟩
  simpa only [facts, baseFacts_eq_atFacts, hpc] using h.2.2.2.2

/-- A scalar checkpoint that carries no numeric payload needs just the register facts. -/
theorem AtD.of_facts {d : D} {t : TState} {pc : Nat} (hpc : d.site.pc = pc) (hsub : d.site.sub = 0)
    (hacc : accAt d = []) (h : At t pc (atFacts P L g d pc))
    (hp : payloadFacts L g d = [] := by rfl) :
    AtD P L g d t :=
  AtD.of_all_facts hpc hsub hacc (by simpa only [hp, List.nil_append] using h)

/-! ## The vector scale load -/

/-- The four scale loads share a base register, and are one raw row group apart. -/
def scaleLoad (r : Fin 4) : MemAccess where
  kind := .load
  space := some (.shared .cta)
  sem := .weak
  elem := .int .b 32
  vec := 4
  addr := ⟨.reg 2796 32, ((512 + 9216 * r.val : Nat) : Int)⟩
  dsts := (List.range 4).map fun j =>
    some ([2797, 2818, 2838, 2858].getD r.val 0 + j)

theorem scaleLoad_code (r j : Fin 4) :
    kernel.code[(Site.scale r j).pc]? = some ⟨none, .mem (scaleLoad r)⟩ := by
  fin_cases r
  · exact Flow.code_2695
  · exact Flow.code_2920
  · exact Flow.code_3145
  · exact Flow.code_3370

/-- A scale-vector element reads four bytes at its row's recorded scale address. -/
theorem scale_template {mem0 : Mem0} {d : D} {r j : Fin 4} {t : TState} (hpre : Pre P L mem0)
    (hd : d.site = .scale r j) (hat : AtD P L g d t) (hinv : Inv P L g d) :
    eventTmpl asms L g t (.mem (scaleLoad r)) =
      .read
        { loc := ⟨.shared, ctaOf L g,
            L.sharedBase + rawBase d.buf + scaleRowOff L g r.val + 4 * j.val⟩
          size := 4
          elem := j.val }
        (afterLoad t (scaleLoad r).regs) := by
  have hr : t.regs 2796 = some (b32 (L.sharedBase + rawBase d.buf + rawRowOff L g 0)) := by
    have hm : 2796 ∈ (Flow.live d.site.pc).filter (fun reg => tracked.contains reg) := by
      rw [hd]
      fin_cases r
      · change 2796 ∈ (Flow.live 2695).filter (fun reg => tracked.contains reg)
        decide +kernel
      · change 2796 ∈ (Flow.live 2920).filter (fun reg => tracked.contains reg)
        decide +kernel
      · change 2796 ∈ (Flow.live 3145).filter (fun reg => tracked.contains reg)
        decide +kernel
      · change 2796 ∈ (Flow.live 3370).filter (fun reg => tracked.contains reg)
        decide +kernel
    have hv := hat.reg hm
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] at hv
    simpa [sb, Nat.add_assoc] using hv
  have hsum : L.sharedBase + rawBase d.buf + rawRowOff L g 0 + (512 + 9216 * r.val) =
      L.sharedBase + rawBase d.buf + scaleRowOff L g r.val := by
    simp only [scaleRowOff, rawRowOff, rawRow, rawRowStride, numGroups, quantBytes]
    omega
  have hmod : (L.sharedBase + rawBase d.buf + rawRowOff L g 0 + (512 + 9216 * r.val)) %
      16 = 0 := by
    have hbase : L.sharedBase % 1024 = 0 := by
      rw [hpre.sharedBase]
      exact hpre.sharedAlignment
    simp only [rawBase, rawBufBytes, rawRowOff, rawRowStride]
    omega
  have hlt : L.sharedBase + rawBase d.buf + rawRowOff L g 0 + (512 + 9216 * r.val) <
      2 ^ 32 := by
    rw [hsum]
    have hs := sharedBase_lt hpre
    have hfit := hinv.scaleFit r.val r.isLt
    have hb := hinv.bufLt
    simp only [rawBase, rawBufBytes, scaleLoadBytes] at hfit ⊢
    omega
  have hs : t.sub = j.val := by rw [hat.2.1, hd]; rfl
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 2796) (w := 32)
    rfl rfl rfl rfl (by simp [scaleLoad])]
  change loadTmpl asms L g t .shared false 32 (scaleLoad r).regs 2796
    ((512 + 9216 * r.val : Nat) : Int) = _
  simp only [loadTmpl, effAddr_b32_off hr hlt, bind, Except.bind]
  have hn : (scaleLoad r).regs.length = 4 := by
    simp [scaleLoad, MemAccess.regs, List.filterMap_map]
  rw [hn, elemAcc_ok (by decide) (by simpa using hmod), hs, hsum]
  rfl

/-- Each scale element reads four bytes of the row's scale vector. -/
theorem fires_scale {mem0 : Mem0} {d : D} {r j : Fin 4} {t u : TState} {e : Event}
    (hpre : Pre P L mem0) (hd : d.site = .scale r j) (hat : AtD P L g d t) (hinv : Inv P L g d)
    (hf : Fires d.site.pc (eventTmpl asms L g t (.mem (scaleLoad r))) e (some u)) :
    ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, ctaOf L g,
        L.sharedBase + rawBase d.buf + scaleRowOff L g r.val + 4 * j.val⟩ ∧
      ac.size = 4 ∧ u = afterLoad t (scaleLoad r).regs bs := by
  rw [scale_template hpre hd hat hinv] at hf
  obtain ⟨bs, _, rfl, hu⟩ := hf
  exact ⟨_, bs, rfl, rfl, rfl, Option.some.inj hu⟩

/-- The first three scale elements preserve the projected registers and extend the accumulator. -/
theorem step_scale_element {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r j : Fin 4}
    (hd : d.site = .scale r j) (hj : j.val + 1 < 4) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (scaleLoad r)⟩ := by
      rw [hd]
      exact scaleLoad_code r j
    have hi := Option.some.inj (hc.symm.trans hc')
    subst ins
    obtain ⟨ac, bs, he, ha, hsize, hu⟩ := fires_scale hpre hd hat hinv hf
    change AtD P L g d t at hat
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b32 (scaleBits bs))
    · let s : Site := .scale r ⟨j.val + 1, hj⟩
      let d' : D := { d with
        site := s
        sc := d.sc % 256 ^ (4 * j.val) + 256 ^ (4 * j.val) * scaleBits bs }
      have hs : t.sub = j.val := by rw [hat.2.1, hd]; rfl
      have hu' : u = { t with sub := j.val + 1, acc := t.acc ++ [b32 (scaleBits bs)] } := by
        rw [hu, afterLoad, hv, hs]
        simp [scaleLoad, MemAccess.regs, hj]
      have hs' : d'.site = s := rfl
      have hpc' : d'.site.pc = d.site.pc := by rw [hs', hd]; rfl
      have hw : scaleBits bs < 256 ^ 4 := Nat.mod_lt _ (by decide)
      have ha' : accAt d' = accAt d ++ [b32 (scaleBits bs)] := accAt_scale_succ hd hw hj
      have hvals : valueOf P L g d' = valueOf P L g d := by
        funext reg
        simp [valueOf, table, d', s, hd]
      have hnot : d'.site ≠ .qUtccp := by
        intro heq
        rw [hs'] at heq
        nomatch heq
      have hnew : Inv P L g d' :=
        ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
          hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
          fun h => (hnot h).elim, hinv.lenLt, hinv.batch, trivial⟩
      have hj3 : j.val ≠ 3 := by omega
      refine Or.inl (Or.inr ⟨d', u, ?_, .refl, ?_⟩)
      · simp [next, nextSite, hd, ha, hsize, hv, d', s, afterScale, hj, hj3]
      · rw [hu']
        change AtD P L g d' _ ∧ Inv P L g d'
        refine ⟨⟨hat.1.trans hpc'.symm, rfl, ?_, hat.2.2.2.1, ?_⟩, hnew⟩
        · rw [ha', hat.2.2.1]
        · simpa only [facts, baseFacts, hpc', hvals, payloadFacts, hs', s, hd, Site.pc,
            List.nil_append] using hat.baseRegs
    · refine Or.inl (Or.inl ?_)
      cases hb : rebuild 3 bs with
      | error f => simp [next, nextSite, hd, ha, hsize, hb]
      | ok v =>
        have hne : v ≠ b32 (scaleBits bs) := fun eq => hv (hb.trans (congrArg Except.ok eq))
        simp [next, nextSite, hd, ha, hsize, hb, hne]

/-- **After a fired poll**: the thread is at the next instruction, its predicate is the poll's
outcome, and every tracked fact of the polling state still holds. -/
theorem at_afterWait {d : D} {t u : TState} (hat : AtD P L g d t) {p pc : Nat} {ok : Bool}
    (hpc : d.site.pc = pc) (hu : u = PTX.next (setReg t p (.pred ok)))
    (hp : p ∉ (Flow.live pc).filter (fun r => tracked.contains r))
    (hns : ∀ r j, d.site ≠ .scale r j) :
    At u (pc + 1) ((p, .pred ok) :: factsFrom ((Flow.live pc).filter (fun r =>
      tracked.contains r)) (valueOf P L g d)) := by
  have hholds := hat.baseRegs
  obtain ⟨hpc', hsub, hacc, hfault, -⟩ := hat
  subst hpc
  subst hu
  refine ⟨by simp [PTX.next, setReg, hpc'], ?_, ?_, ?_, ?_⟩
  · simp [PTX.next, setReg, hsub, Site.sub_eq_zero_of_not_scale hns]
  · simp [PTX.next, setReg, hacc, accAt_of_not_scale hns]
  · simp [PTX.next, setReg, hfault]
  · rw [holds_cons]
    refine ⟨by simp [setReg, PTX.next], ?_⟩
    refine holds_of_pointwise fun r hr => ?_
    have hne : r ≠ p := fun e => hp (e ▸ hr)
    have h := holds_mem hholds (mem_factsFrom (val := valueOf P L g d) hr)
    simpa [setReg, PTX.next, Function.update_of_ne hne] using h
end

/-- The block count of a row fits 32 bits: each of the two lengths is below `2 ^ 31`, so the
padded counts are below `2 ^ 32 + 190` and their sum divided by the 64 rows of a block is far
below `2 ^ 32`. -/
theorem totalBlocks_lt {len0 len1 : Nat} (h0 : len0 < 2 ^ 31) (h1 : len1 < 2 ^ 31) :
    totalBlocks len0 len1 < 2 ^ 32 := by
  have hc1 : ceilToMultiple len1 FlashMlaSparseDecodeH64.topkBlock ≤ len1 + 63 := by
    unfold ceilToMultiple FlashMlaSparseDecodeH64.topkBlock
    have := Nat.div_mul_le_self (len1 + 64 - 1) 64
    omega
  have ho : origPadded len0 ≤ len0 + 63 + 64 := by
    unfold origPadded
    simp only [FlashMlaSparseDecodeH64.topkBlock, ceilToMultiple]
    have h2 := Nat.div_mul_le_self (len0 + 64 - 1) 64
    have : max ((len0 + 64 - 1) / 64 * 64) 64 ≤ max (len0 + 63) 64 := by
      apply max_le
      · omega
      · omega
    omega
  unfold totalBlocks
  have hsum : origPadded len0 + ceilToMultiple len1 FlashMlaSparseDecodeH64.topkBlock ≤
      len0 + len1 + 190 := by omega
  have hq : (origPadded len0 + ceilToMultiple len1 FlashMlaSparseDecodeH64.topkBlock) /
      FlashMlaSparseDecodeH64.topkBlock ≤ (len0 + len1 + 190) / 64 := by
    rw [show FlashMlaSparseDecodeH64.topkBlock = 64 from rfl]
    exact Nat.div_le_div_right hsum
  have hbig : (len0 + len1 + 190) / 64 < 2 ^ 32 := by omega
  omega

/-! ## The bit normal forms of the body's arithmetic

The steps below evaluate the integer instructions of the role's tails. Three operations of the
decoded program have no rule in `norm_bits`: the `xor` of the swizzle's lane index, the `and`
masks that duplicate a byte or clear the low six bits of a block count, and the `shr` of the
signed ceiling. The lemmas here put them in the `Nat` normal form `norm_bits` ends in. -/

/-- Xor of two 64-bit patterns in the `Nat` normal form. -/
theorem nf_xor (a b : Nat) : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 ^^^ b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 18446744073709551616 ^^^ b % 18446744073709551616 < 18446744073709551616 :=
    Nat.xor_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt h1]

/-- The `and` with the byte mask `255`. -/
theorem land255 (x : Nat) : x &&& 255 = x % 256 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 8
  rw [show (255 : Nat) = 2 ^ 8 - 1 from by decide]
  exact h

/-- The `and` with the bit mask `1`. -/
theorem land1 (x : Nat) : x &&& 1 = x % 2 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 1
  rw [show (1 : Nat) = 2 ^ 1 - 1 from by decide]
  exact h

/-- The `and` that clears the low six bits of a 32-bit word: the whole-word ceiling of
`ku::ceil` (`(x + 63) & -64`). -/
theorem land_neg64_of_lt {x : Nat} (h : x < 2 ^ 32) :
    x &&& ((2 ^ 32 : Nat) - 64) = x / 64 * 64 := by
  have hdiv : (x &&& ((2^32 : Nat) - 64)) / 64 = x / 64 := by
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.and_div_two_pow]
    have hm : ((2^32 : Nat) - 2^6) / 2^6 = 2^26 - 1 := by decide
    rw [hm, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : (x &&& ((2^32 : Nat) - 64)) % 64 = 0 := by
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.and_mod_two_pow]
    have hm : ((2^32 : Nat) - 2^6) % 2^6 = 0 := by decide
    rw [hm, Nat.and_zero]
  have hx : x % 64 + 64 * (x / 64) = x := Nat.mod_add_div x 64
  omega

/-- The same mask on an arbitrary `Nat` word. -/
theorem land_neg64 (x : Nat) : x &&& ((2 ^ 32 : Nat) - 64) = x % 2 ^ 32 - x % 64 := by
  have hmask : ((2 ^ 32 : Nat) - 64) < 2 ^ 32 := by decide
  have h1 : x &&& ((2 ^ 32 : Nat) - 64) =
      (x % 2 ^ 32) &&& (((2 ^ 32 : Nat) - 64) % 2 ^ 32) := by
    rw [← Nat.and_mod_two_pow (n := 32)]
    exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow x hmask)).symm
  rw [h1, show (((2 ^ 32 : Nat) - 64) % 2 ^ 32) = (2 ^ 32 : Nat) - 64 from by decide]
  rw [land_neg64_of_lt (Nat.mod_lt _ (by decide))]
  omega

/-- A shared address word formed by `add.s32` of a constant: the truncated sum is the single
normal-form word when the exact sum fits 32 bits (`trunc32_add`). -/
theorem addr_eq {x c off : Nat} (h : x + c = off) (hc : 0 ≤ c)
    (hb : x + c < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) +
      truncBits 32 (BitVec.ofInt 64 c))) = b32 off := by
  refine Eq.trans (congrArg (Value.bits 32) (trunc32_add (x := x) (c := c) hc hb)) ?_
  rw [h]
  rfl

/-- Close a `seg_fp` value equation with the role's bit normal forms. The given lemmas come
last: an empty splice in front of them would leave the list without its leading lemma. -/
macro "wg2_close" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| seg_close [true_and, and_true, nf_xor, land255, land1, land_neg64,
    Nat.xor_self, Nat.zero_and, Nat.zero_xor, Nat.xor_zero, Nat.mod_add_div, Nat.div_add_mod,
    $ls,*])

/-- The truncated sum of two 32-bit words is the single word when the exact sum fits 32 bits:
`trunc32_add` with the second operand read as the word it is. -/
theorem trunc32_add_word {a b : Nat} (hb : b < 2 ^ 32) (h : a + b < 2 ^ 32) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) + truncBits 32 (BitVec.ofNat 64 b)) =
      BitVec.ofNat 64 (a + b) := by
  have ha : a < 2 ^ 32 := by omega
  have ha64 : a < 2 ^ 64 := by omega
  have hb64 : b < 2 ^ 64 := by omega
  have h64 : a + b < 2 ^ 64 := by omega
  rw [truncBits_ofNat ha (by omega), truncBits_ofNat hb (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64, Nat.mod_eq_of_lt hb64,
    Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]

/-! ## Completed scale vector and scale-byte extraction -/

def scaleWordFacts (r : Fin 4) (d : D) : List (Nat × Value) :=
  (List.range 4).map fun j =>
    ([2797, 2818, 2838, 2858].getD r.val 0 + j, b32 (scaleWord d j))

theorem scaleLast_regs (r : Fin 4) (d : D) (t : TState) :
    Holds (setRegs t (scaleLoad r).regs
      [b32 (scaleWord d 0), b32 (scaleWord d 1), b32 (scaleWord d 2), b32 (scaleWord d 3)]).regs
      (scaleWordFacts r d) := by
  fin_cases r <;> simp [scaleLoad, scaleWordFacts, MemAccess.regs, setRegs, setReg, Holds,
    show List.range 4 = [0, 1, 2, 3] from by decide]

theorem scaleLast_live (r : Fin 4) {reg : Nat}
    (h : reg ∈ Flow.live (Site.scale r ⟨3, by decide⟩).pc) :
    reg ∉ (scaleLoad r).regs := by
  have hall : (Flow.live (Site.scale r ⟨3, by decide⟩).pc).all
      (fun i => !(scaleLoad r).regs.contains i) = true := by
    fin_cases r <;> decide +kernel
  simpa using (List.all_eq_true.mp hall) reg h

def scaleFinalState (d : D) (r : Fin 4) (w : Nat) : D :=
  { d with
    site := .raw r ⟨0, by decide⟩
    sc := d.sc % 256 ^ 12 + 256 ^ 12 * w }

theorem scaleFinal_words (d : D) (r : Fin 4) {w : Nat} (hw : w < 256 ^ 4)
    (hd : d.site = .scale r ⟨3, by decide⟩) :
    accAt d ++ [b32 w] =
      [b32 (scaleWord (scaleFinalState d r w) 0), b32 (scaleWord (scaleFinalState d r w) 1),
        b32 (scaleWord (scaleFinalState d r w) 2), b32 (scaleWord (scaleFinalState d r w) 3)] := by
  have h0 : scaleWord (scaleFinalState d r w) 0 = scaleWord d 0 :=
    scaleWord_low (s := d.sc) (j := 3) (i := 0) (w := w) (by decide)
  have h1 : scaleWord (scaleFinalState d r w) 1 = scaleWord d 1 :=
    scaleWord_low (s := d.sc) (j := 3) (i := 1) (w := w) (by decide)
  have h2 : scaleWord (scaleFinalState d r w) 2 = scaleWord d 2 :=
    scaleWord_low (s := d.sc) (j := 3) (i := 2) (w := w) (by decide)
  have h3 : scaleWord (scaleFinalState d r w) 3 = w :=
    scaleWord_update (s := d.sc) (j := 3) hw
  rw [h0, h1, h2, h3, accAt_of_scale hd]
  rfl

theorem afterLoad_scale_last {P : Params} {L : Launch} {g : Nat} {d : D} {r : Fin 4} {t : TState}
    {bs : List (Option Byte)} (hd : d.site = .scale r ⟨3, by decide⟩) (hat : AtD P L g d t)
    (hv : rebuild 3 bs = .ok (b32 (scaleBits bs))) :
    At (afterLoad t (scaleLoad r).regs bs) (d.site.pc + 1)
      (scaleWordFacts r (scaleFinalState d r (scaleBits bs)) ++
        atFacts P L g (scaleFinalState d r (scaleBits bs)) d.site.pc) := by
  let d' := scaleFinalState d r (scaleBits bs)
  let words := [b32 (scaleWord d' 0), b32 (scaleWord d' 1), b32 (scaleWord d' 2),
    b32 (scaleWord d' 3)]
  have hs : t.sub = 3 := by rw [hat.2.1, hd]; rfl
  have hn : (scaleLoad r).regs.length = 4 := by fin_cases r <;> rfl
  have hwords : t.acc ++ [b32 (scaleBits bs)] = words := by
    rw [hat.2.2.1]
    exact scaleFinal_words d r (w := scaleBits bs) (Nat.mod_lt _ (by decide)) hd
  have hload : afterLoad t (scaleLoad r).regs bs =
      { setRegs t (scaleLoad r).regs words with pc := t.pc + 1, sub := 0, acc := [] } := by
    simp [afterLoad, hv, hs, hwords, hn]
  have hfault : (setRegs t (scaleLoad r).regs words).fault = t.fault := by
    fin_cases r <;> rfl
  rw [hload]
  refine ⟨congrArg (· + 1) hat.1, rfl, rfl, hfault.trans hat.2.2.2.1, ?_⟩
  · rw [holds_append]
    refine ⟨scaleLast_regs r d' t, holds_of_pointwise ?_⟩
    intro reg hr
    have hm : reg ∈ Flow.live (Site.scale r ⟨3, by decide⟩).pc := by
      have := List.mem_filter.mp hr
      simpa only [hd] using this.1
    have hnReg := scaleLast_live r hm
    have hreg : (setRegs t (scaleLoad r).regs words).regs reg = t.regs reg := by
      fin_cases r <;>
        simp [scaleLoad, MemAccess.regs,
          show List.range 4 = [0, 1, 2, 3] from by decide] at hnReg <;>
        simp [scaleLoad, MemAccess.regs, setRegs, setReg, words,
          show List.range 4 = [0, 1, 2, 3] from by decide,
          hnReg.1, hnReg.2.1, hnReg.2.2.1, hnReg.2.2.2]
    change (setRegs t (scaleLoad r).regs words).regs reg = _
    rw [hreg]
    have hval : valueOf P L g d' reg = valueOf P L g d reg := by
      simp [d', scaleFinalState, valueOf, table, hd]
    rw [hval]
    exact hat.reg hr
theorem scalePermute (a : Nat) (ha : a < 2 ^ 32) (i : Fin 4) :
    prmtBits none a 0 (30576 + i.val) = a / 256 ^ i.val % 256 := by
  have h7 : a / 72057594037927936 = 0 := Nat.div_eq_of_lt (by omega)
  fin_cases i <;> norm_num [prmtBits, h7]

theorem scalePermute_cvt (a i : Nat) (ha : a < 2 ^ 32) (hi : i < 4) :
    truncBits 16 (truncBits 32 (BitVec.ofNat 64
      (prmtBits none (truncBits 32 (BitVec.ofNat 64 a)).toNat
        (truncBits 32 (BitVec.ofInt 64 0)).toNat
        (truncBits 32 (BitVec.ofInt 64 (30576 + (i : Int)))).toNat))) =
      BitVec.ofNat 64 (a / 256 ^ i % 256) := by
  have ha64 : a < 2 ^ 64 := by omega
  have hbyte : a / 256 ^ i % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [truncBits_ofNat ha (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha64]
  have hzero : (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 := by decide
  have hcontrol : (truncBits 32 (BitVec.ofInt 64 (30576 + (i : Int)))).toNat = 30576 + i := by
    interval_cases i <;> decide
  rw [hzero, hcontrol, scalePermute a ha ⟨i, hi⟩]
  rw [truncBits_ofNat (show a / 256 ^ i % 256 < 2 ^ 32 by omega) (by omega),
    truncBits_ofNat (show a / 256 ^ i % 256 < 2 ^ 16 by omega) (by omega)]

macro "scale_segment_facts" h:ident : tactic =>
  `(tactic| simp only [scaleWordFacts, scaleByteFacts,
    show List.range 4 = [0, 1, 2, 3] from by decide,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by decide,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append] at $h ⊢)

open Lean Elab Tactic in
elab "scale_segment_value" : tactic => do
  let target ← getMainTarget
  let some permute := target.find? (fun e => e.isAppOfArity ``PTX.prmtBits 4)
    | throwError "expected a scale permute"
  let ctl ← PTX.Flow.natValue (permute.getArg! 3)
  unless 30576 ≤ ctl && ctl < 30580 do
    throwError "unexpected scale selector {ctl}"
  let i := Syntax.mkNumLit (toString (ctl - 30576))
  evalTactic (← `(tactic| exact congrArg (Value.bits 16)
    (scalePermute_cvt _ $i (Nat.mod_lt _ (by decide)) (by decide))))

def ScaleTail (P : Params) (L : Launch) (g : Nat) (d : D) (r : Fin 4) : Prop :=
  Seg kernel asms L g 33 ((Site.scale r ⟨3, by decide⟩).pc + 1)
    (scaleWordFacts r d ++ atFacts P L g d (Site.scale r ⟨3, by decide⟩).pc)
    (Site.raw r ⟨0, by decide⟩).pc
    (scaleByteFacts r d ++ atFacts P L g d (Site.raw r ⟨0, by decide⟩).pc)

section ScaleTail

variable {P : Params} {L : Launch} {g : Nat} {d : D}

theorem scaleTail_zero
    (hbase : L.sharedBase + rawBase d.buf + rawWordOff L g 0 0 < 2 ^ 32) :
    ScaleTail P L g d 0 := by
  intro u h
  have hsum : (L.sharedBase + (rawBase d.buf + rawRowOff L g 0)) +
      idxInGroup L g * rawBytesPerThread < 2 ^ 32 := by
    simpa only [rawWordOff, Nat.zero_mul, Nat.add_zero, Nat.add_assoc] using hbase
  have hb : idxInGroup L g * rawBytesPerThread < 2 ^ 32 := by omega
  scale_segment_facts h
  seg_fp h using
    first
    | scale_segment_value
    | rw [trunc32_add_word hb hsum]
      simp [valueOf, table, PTX.Flow.lookupLit, b32, sb, rawWordOff, Nat.add_assoc]

theorem scaleTail_one
    (haddr : L.sharedBase + (tileBase d.buf + dstOff L g) + 2048 < 2 ^ 32) :
    ScaleTail P L g d 1 := by
  intro u h
  scale_segment_facts h
  seg_fp h using
    first
    | scale_segment_value
    | rw [show BitVec.ofInt 64 2048 = BitVec.ofNat 64 2048 by rfl,
        trunc32_add_word (by decide) haddr]
      simp [valueOf, table, PTX.Flow.lookupLit, b32, sb, tileOff, numGroups, Nat.add_assoc]

theorem scaleTail_two
    (haddr : L.sharedBase + (tileBase d.buf + dstOff L g) + 4096 < 2 ^ 32) :
    ScaleTail P L g d 2 := by
  intro u h
  scale_segment_facts h
  seg_fp h using
    first
    | scale_segment_value
    | rw [show BitVec.ofInt 64 4096 = BitVec.ofNat 64 4096 by rfl,
        trunc32_add_word (by decide) haddr]
      simp [valueOf, table, PTX.Flow.lookupLit, b32, sb, tileOff, numGroups, Nat.add_assoc]

theorem scaleTail_three
    (haddr : L.sharedBase + (tileBase d.buf + dstOff L g) + 6144 < 2 ^ 32) :
    ScaleTail P L g d 3 := by
  intro u h
  scale_segment_facts h
  seg_fp h using
    first
    | scale_segment_value
    | rw [show BitVec.ofInt 64 6144 = BitVec.ofNat 64 6144 by rfl,
        trunc32_add_word (by decide) haddr]
      simp [valueOf, table, PTX.Flow.lookupLit, b32, sb, tileOff, numGroups, Nat.add_assoc]

theorem scaleTail (r : Fin 4)
    (hbase : L.sharedBase + rawBase d.buf + rawWordOff L g 0 0 < 2 ^ 32)
    (haddr : L.sharedBase + (tileBase d.buf + dstOff L g) + 2048 * r.val < 2 ^ 32) :
    ScaleTail P L g d r := by
  fin_cases r
  · exact scaleTail_zero hbase
  · exact scaleTail_one haddr
  · exact scaleTail_two haddr
  · exact scaleTail_three haddr
end ScaleTail

/-- The fourth scale element completes the vector and exposes its unpacked scale bytes. -/
theorem step_scale_final {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) {r : Fin 4} (hd : d.site = .scale r ⟨3, by decide⟩) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (scaleLoad r)⟩ := by
      rw [hd]
      exact scaleLoad_code r ⟨3, by decide⟩
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, bs, he, ha, hsize, hu⟩ := fires_scale hpre hd hat hinv hf
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b32 (scaleBits bs))
    · let d' := scaleFinalState d r (scaleBits bs)
      by_cases hfin : ScaleWordOk d'.sc
      · have hrawBase : L.sharedBase + rawBase d.buf + rawWordOff L g 0 0 < 2 ^ 32 := by
          have hshared := sharedBase_lt hpre
          have hfit := hinv.scaleFit 0 (by decide)
          have hbuf := hinv.bufLt
          have hgroup := hinv.idxLt
          simp only [scaleRowOff, quantBytes, scaleLoadBytes, rawBufBytes] at hfit
          simp only [groupSize] at hgroup
          simp only [rawBase, rawBufBytes, rawWordOff, rawBytesPerThread,
            Nat.zero_mul, Nat.add_zero]
          omega
        have haddr : L.sharedBase + (tileBase d.buf + dstOff L g) + 2048 * r.val < 2 ^ 32 := by
          have hshared := sharedBase_lt hpre
          have hfit := tile_fit (L := L) (g := g) r.isLt (show 0 < numSteps by decide)
          have hbuf := hinv.bufLt
          simp only [tileOff, topkBlock, numGroups, Nat.mul_zero, Nat.reduceMul, Nat.add_zero,
            dequantBytes] at hfit
          simp only [tileBase, dequantBytes]
          omega
        have hstart := afterLoad_scale_last hd hat hv
        rw [← hu, hd] at hstart
        obtain ⟨t', hr, ht⟩ :=
          scaleTail (P := P) (L := L) (g := g) (d := d') r hrawBase haddr u hstart
        have hnot : d'.site ≠ .qUtccp := by
          show Site.raw r ⟨0, by decide⟩ ≠ .qUtccp
          intro h
          nomatch h
        have hnew : Inv P L g d' :=
          ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
            hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
            fun h => (hnot h).elim, hinv.lenLt, hinv.batch,
            ⟨hfin, by simp⟩⟩
        refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, ?_⟩)
        · simpa [next, nextSite, hd, ha, hsize, hv, d', scaleFinalState, afterScale] using hfin
        · change AtD P L g d' t' ∧ Inv P L g d'
          have ht' : At t' (Site.raw r ⟨0, by decide⟩).pc
              (payloadFacts L g d' ++ atFacts P L g d' (Site.raw r ⟨0, by decide⟩).pc) := by
            simpa [payloadFacts, d', scaleFinalState] using ht
          exact ⟨AtD.of_all_facts (d := d') rfl rfl rfl ht', hnew⟩
      · exact Or.inl (Or.inl (by
          simpa [next, nextSite, hd, ha, hsize, hv, d', scaleFinalState] using hfin))
    · refine Or.inl (Or.inl ?_)
      cases hb : rebuild 3 bs with
      | error f => simp [next, nextSite, hd, ha, hsize, hb]
      | ok v =>
        have hne : v ≠ b32 (scaleBits bs) := fun eq => hv (hb.trans (congrArg Except.ok eq))
        simp [next, nextSite, hd, ha, hsize, hb, hne]

theorem stepAt_scale {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) {r j : Fin 4} (hd : d.site = .scale r j) :
    (code P L g).StepAt d := by
  by_cases hj : j.val + 1 < 4
  · exact step_scale_element hpre d hd hj
  have h3 : j = ⟨3, by decide⟩ := by
    apply Fin.eq_of_val_eq
    change j.val = 3
    have := j.isLt
    omega
  exact step_scale_final hpre d (h3 ▸ hd)

/-! ## Raw-load footprint and the first word -/

/-- All raw words use the row-zero address with a constant row and word offset. -/
def rawLoad (r : Fin 4) (s : Fin 8) : MemAccess where
  kind := .load
  space := some (.shared .cta)
  sem := .weak
  elem := .int .b 64
  addr := ⟨.reg 2817 32, ((9216 * r.val + 64 * s.val : Nat) : Int)⟩
  dsts := [some (rawLoadReg r s.val)]

open Lean Elab Tactic Meta in
elab "wg2_code" : tactic => do
  let target ← whnf (← getMainTarget)
  let some (_, lhs, _) := target.eq? | throwError "expected an instruction lookup"
  unless lhs.isAppOfArity ``GetElem?.getElem? 7 do
    throwError "expected a lookup in the frozen instruction table"
  let pc ← PTX.Flow.natValue (lhs.getArg! 6)
  let proofId :=
    mkIdent ((`PTX.Kernels.FlashMlaSparseDecodeH64.Flow) ++ Name.mkSimple s!"code_{pc}")
  evalTactic (← `(tactic| exact $proofId))

theorem rawLoad_code (r : Fin 4) (s : Fin 8) :
    kernel.code[(Site.raw r s).pc]? = some ⟨none, .mem (rawLoad r s)⟩ := by
  fin_cases r <;> fin_cases s <;> wg2_code

theorem rawBase_live (r : Fin 4) (s : Fin 8) :
    2817 ∈ (Flow.live (Site.raw r s).pc).filter (fun reg => tracked.contains reg) := by
  fin_cases r <;> fin_cases s <;> decide +kernel

/-- A raw scalar load reads one word at its row and step's recorded address. -/
theorem raw_template {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D}
    {r : Fin 4} {s : Fin 8} {t : TState} (hpre : Pre P L mem0) (hd : d.site = .raw r s)
    (hat : AtD P L g d t) (hinv : Inv P L g d) :
    eventTmpl asms L g t (.mem (rawLoad r s)) =
      .read { loc := ⟨.shared, ctaOf L g,
        L.sharedBase + rawBase d.buf + rawWordOff L g r.val s.val⟩, size := 8 }
        (afterLoad t (rawLoad r s).regs) := by
  let a := L.sharedBase + rawBase d.buf + rawWordOff L g 0 0
  let off := 9216 * r.val + 64 * s.val
  have hr : t.regs 2817 = some (b32 a) := by
    have hm : 2817 ∈ (Flow.live d.site.pc).filter (fun reg => tracked.contains reg) := by
      rw [hd]
      exact rawBase_live r s
    have h := hat.reg hm
    simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] at h
    simpa [a, sb, Nat.add_assoc] using h
  have hsum : a + off = L.sharedBase + rawBase d.buf + rawWordOff L g r.val s.val := by
    simp only [a, off, rawWordOff, rawRowOff, rawRow, rawRowStride, numGroups, rawBytesPerStep]
    omega
  have hal : (a + off) % 8 = 0 := by
    have hbase : L.sharedBase % 1024 = 0 := by
      rw [hpre.sharedBase]
      exact hpre.sharedAlignment
    simp only [a, off, rawBase, rawBufBytes, rawWordOff, rawRowOff, rawRowStride,
      rawBytesPerThread, rawBytesPerStep]
    omega
  have hlt : a + off < 2 ^ 32 := by
    rw [hsum]
    have hs := sharedBase_lt hpre
    have hfit := rawWord_fit (L := L) (g := g) r.isLt s.isLt
    have hb := hinv.bufLt
    simp only [rawBase, rawBufBytes, rawBytesPerThread] at hfit ⊢
    omega
  have hsub : t.sub = 0 := by rw [hat.2.1, hd]; rfl
  let dst := 3837 + 48 * r.val + (6 * s.val - 2)
  change eventTmpl asms L g t (.mem
    { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 64,
      addr := ⟨.reg 2817 32, (off : Int)⟩, dsts := [some dst] }) = _
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 2817) (w := 32) rfl rfl rfl rfl rfl]
  simp only [MemAccess.regs, DType.width, loadTmpl, effAddr_b32_off hr hlt, bind, Except.bind,
    Bool.false_eq_true, ↓reduceIte, hsub]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp [Loc.at, hsum, ctaOf, rawLoad, rawLoadReg, dst]

/-- The raw load reads one eight-byte word of the block's raw buffer. -/
theorem fires_raw {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D} {r : Fin 4}
    {s : Fin 8} {t u : TState} {e : Event} (hpre : Pre P L mem0) (hd : d.site = .raw r s)
    (hat : AtD P L g d t) (hinv : Inv P L g d)
    (hf : Fires d.site.pc (eventTmpl asms L g t (.mem (rawLoad r s))) e (some u)) :
    ∃ ac bs, e = ⟨d.site.pc, .rd ac bs⟩ ∧
      ac.loc = ⟨.shared, ctaOf L g, L.sharedBase + rawBase d.buf + rawWordOff L g r.val s.val⟩ ∧
      ac.size = 8 ∧ u = afterLoad t (rawLoad r s).regs bs := by
  rw [raw_template hpre hd hat hinv] at hf
  obtain ⟨bs, _, rfl, hu⟩ := hf
  exact ⟨_, bs, rfl, rfl, rfl, Option.some.inj hu⟩

def FirstRawTail (P : Params) (L : Launch) (g : Nat) (d : D) (r : Fin 4) : Prop :=
  Seg kernel asms L g 7 ((Site.raw r 0).pc + 1)
    ((3837 + 48 * r.val, b64 d.raw) :: scaleByteFacts r d ++
      atFacts P L g d (Site.raw r 0).pc)
    (Site.raw r 1).pc
    (scaleByteFacts r d ++ rawPairFacts r 0 d.raw ++ atFacts P L g d (Site.raw r 1).pc)

macro "raw_pair_facts" h:ident : tactic =>
  `(tactic| simp only [rawPairFacts, scaleByteFacts,
    show List.range 4 = [0, 1, 2, 3] from by decide,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by decide,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append] at $h ⊢)

theorem firstRawTail_zero {P : Params} {L : Launch} {g : Nat} {d : D}
    (hw : d.raw < 2 ^ 64) : FirstRawTail P L g d 0 := by
  intro u h
  raw_pair_facts h
  seg_fp h using
    norm_bits [hw]

theorem firstRawTail_one {P : Params} {L : Launch} {g : Nat} {d : D}
    (hw : d.raw < 2 ^ 64) : FirstRawTail P L g d 1 := by
  intro u h
  raw_pair_facts h
  seg_fp h using norm_bits [hw]

theorem firstRawTail_two {P : Params} {L : Launch} {g : Nat} {d : D}
    (hw : d.raw < 2 ^ 64) : FirstRawTail P L g d 2 := by
  intro u h
  raw_pair_facts h
  seg_fp h using norm_bits [hw]

theorem firstRawTail_three {P : Params} {L : Launch} {g : Nat} {d : D}
    (hw : d.raw < 2 ^ 64) : FirstRawTail P L g d 3 := by
  intro u h
  raw_pair_facts h
  seg_fp h using norm_bits [hw]

theorem firstRawTail {P : Params} {L : Launch} {g : Nat} {d : D}
    (r : Fin 4) (hw : d.raw < 2 ^ 64) : FirstRawTail P L g d r := by
  fin_cases r
  · exact firstRawTail_zero hw
  · exact firstRawTail_one hw
  · exact firstRawTail_two hw
  · exact firstRawTail_three hw

def rawFirstState (d : D) (r : Fin 4) (w : Nat) : D :=
  { d with site := .raw r 1, raw := w }

private theorem holds_frame {R R' : Nat → Option Value} {F : List (Nat × Value)}
    (h : Holds R F) (hfr : ∀ v ∈ F, R' v.1 = R v.1) : Holds R' F := by
  induction F with
  | nil => trivial
  | cons v rest ih =>
    obtain ⟨r, w⟩ := v
    rw [holds_cons] at h ⊢
    exact ⟨(hfr (r, w) (by simp)).trans h.1,
      ih h.2 (fun v hv => hfr v (List.mem_cons_of_mem _ hv))⟩

/-- A scalar raw load updates only its destination register. -/
theorem afterLoad_first_raw {P : Params} {L : Launch} {g : Nat} {d : D} {r : Fin 4} {t : TState}
    {bs : List (Option Byte)} (hd : d.site = .raw r 0) (hat : AtD P L g d t)
    (hv : rebuild 3 bs = .ok (b64 (rawBits bs))) :
    let d' := rawFirstState d r (rawBits bs)
    At (afterLoad t (rawLoad r 0).regs bs) ((Site.raw r 0).pc + 1)
      ((3837 + 48 * r.val, b64 d'.raw) :: scaleByteFacts r d' ++
        atFacts P L g d' (Site.raw r 0).pc) := by
  let d' := rawFirstState d r (rawBits bs)
  let reg := 3837 + 48 * r.val
  have hs : t.sub = 0 := by rw [hat.2.1, hd]; rfl
  have ha : t.acc = [] := by rw [hat.2.2.1, accAt, hd]
  have hload : afterLoad t (rawLoad r 0).regs bs =
      { PTX.next (setReg t reg (b64 d'.raw)) with sub := 0, acc := [] } := by
    rw [afterLoad, hv, hs, ha]
    rfl
  rw [hload]
  refine ⟨?_, rfl, rfl, hat.2.2.2.1, ?_⟩
  · change t.pc + 1 = (Site.raw r 0).pc + 1
    rw [hat.1, hd]
  · change Holds (setReg t reg (b64 d'.raw)).regs
      ((reg, b64 d'.raw) :: (scaleByteFacts r d' ++ atFacts P L g d' (Site.raw r 0).pc))
    rw [holds_cons, holds_append]
    refine ⟨by simp [setReg, reg, d'], ?_, holds_of_pointwise ?_⟩
    · have hsc : Holds t.regs (scaleByteFacts r d') := by
        change Holds t.regs (scaleByteFacts r d)
        have hsc := hat.payloadRegs
        rw [payloadFacts, hd] at hsc
        simpa using hsc
      refine holds_frame hsc ?_
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv
      have hlt := List.mem_range.mp hj
      have hn : 353 + 24 * r.val + j ≠ reg := by dsimp [reg]; omega
      exact Function.update_of_ne hn _ _
    · intro x hx
      have hm := List.mem_filter.mp hx
      have hreg : tracked.contains reg = false := by fin_cases r <;> decide
      have hn : x ≠ reg := by grind
      simp only [setReg, Function.update_of_ne hn]
      have hval : valueOf P L g d' x = valueOf P L g d x := by
        simp [d', rawFirstState, valueOf, table, hd]
      rw [hval]
      exact hat.reg (by rwa [hd])

/-- The first raw word is split into four two-byte operands before the next load. -/
theorem stepAt_raw_first {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) {r : Fin 4} (hd : d.site = .raw r 0) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (rawLoad r 0)⟩ := by
      rw [hd]
      exact rawLoad_code r 0
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, bs, he, ha, hsize, hu⟩ := fires_raw hpre hd hat hinv hf
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b64 (rawBits bs)) ∧ RawWordOk (rawBits bs)
    · let d' := rawFirstState d r (rawBits bs)
      have hstart := afterLoad_first_raw hd hat hv.1
      rw [← hu] at hstart
      have hw : d'.raw < 2 ^ 64 := Nat.mod_lt _ (by decide)
      obtain ⟨t', hr, ht⟩ := firstRawTail (d := d') r hw u hstart
      have hnot : d'.site ≠ .qUtccp := by
        show Site.raw r 1 ≠ .qUtccp
        intro h
        nomatch h
      have hfin : ScaleWordOk d.sc := by
        have h := hinv.payloadOk
        rw [PayloadOk, hd] at h
        exact h.1
      have hnew : Inv P L g d' :=
        ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
          hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
          fun h => (hnot h).elim, hinv.lenLt, hinv.batch, ⟨hfin, fun _ => hv.2⟩⟩
      refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, ?_⟩)
      · simp [next, nextSite, hd, ha, hsize, rawBytesPerThread, hv.1, hv.2, d', rawFirstState,
          afterRaw]
      · change AtD P L g d' t' ∧ Inv P L g d'
        have ht' : At t' (Site.raw r 1).pc
            (payloadFacts L g d' ++ atFacts P L g d' (Site.raw r 1).pc) := by
          simpa [payloadFacts, d', rawFirstState, List.append_assoc] using ht
        exact ⟨AtD.of_all_facts (d := d') rfl rfl rfl ht', hnew⟩
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, ha, hsize, rawBytesPerThread, hv]))

/-! ## Local dequantization and tile store -/

section
open Numeric

def scaleSelectReg (r : Fin 4) (s : Fin 8) : Nat := 369 + 24 * r.val + s.val

def scaleDupReg (r : Fin 4) (s : Fin 8) : Nat := 191 + 5 * chunkIndex r s

def scaleWideReg (r : Fin 4) (s : Fin 8) : Nat := 2465 + 10 * chunkIndex r s

def rawPairReg (r : Fin 4) (s : Fin 8) (j : Fin 4) : Nat := scaleDupReg r s + 1 + j.val

def rawWideReg (r : Fin 4) (s : Fin 8) (j : Fin 4) : Nat :=
  2464 + 10 * chunkIndex r s + 2 * j.val + (if j.val = 0 then 0 else 1)

def pairProductReg (r : Fin 4) (s : Fin 8) (j : Fin 4) : Nat := rawWideReg r s j - 1

def hiPackReg (r : Fin 4) (s : Fin 8) : Nat :=
  3842 + 48 * r.val + 6 * s.val - (if s.val = 7 then 1 else 0)

def loPackReg (r : Fin 4) (s : Fin 8) : Nat := hiPackReg r s + 1

def tileChunkDelta (r : Fin 4) (s : Fin 8) : Nat := 2048 * r.val + 8192 * s.val

def storeAdd (r : Fin 4) (s : Fin 8) : IntInstr :=
  ⟨.add, .int .s 32, false, [some (storeBaseReg r s)], [.reg 2472, .imm (tileChunkDelta r s)]⟩

def dequantStart (r : Fin 4) (s : Fin 8) : Nat :=
  2738 + 225 * r.val + (if s.val = 0 then 0 else
    23 + 24 * (s.val - 1) - (if s.val = 7 then 1 else 0))

def chunkInstruction (pc : Nat) (op : Op) : Prop :=
  kernel.code[pc]? = some ⟨none, op⟩

structure ChunkCode (r : Fin 4) (s : Fin 8) : Prop where
  select : chunkInstruction (dequantStart r s)
    (.int (selScale 134 (368 + 24 * r.val - 2 * s.val) (367 + 24 * r.val - 2 * s.val)
      (scaleSelectReg r s)))
  duplicate : chunkInstruction (dequantStart r s + 1)
    (.int (dupScale (scaleSelectReg r s) (scaleDupReg r s)))
  scaleWiden : chunkInstruction (dequantStart r s + 2)
    (.cvt (pairCvt .ue8m0 (scaleDupReg r s) (scaleWideReg r s)))
  valueWiden (j : Fin 4) : chunkInstruction (dequantStart r s + 3 + 2 * j.val)
    (.cvt (pairCvt .e4m3 (rawPairReg r s j) (rawWideReg r s j)))
  multiply (j : Fin 4) : chunkInstruction (dequantStart r s + 4 + 2 * j.val)
    (.float (pairMul (rawWideReg r s j) (scaleWideReg r s) (pairProductReg r s j)))
  highPack : chunkInstruction (dequantStart r s + 11)
    (.move (packChunk 64 (pairProductReg r s 2) (pairProductReg r s 3) (hiPackReg r s)))
  lowPack : chunkInstruction (dequantStart r s + 12)
    (.move (packChunk 64 (pairProductReg r s 0) (pairProductReg r s 1) (loPackReg r s)))
  address : s.val ≠ 0 → chunkInstruction (dequantStart r s + 13) (.int (storeAdd r s))
  chunkPack : chunkInstruction (dequantStart r s + (if s.val = 0 then 13 else 14))
    (.move (packChunk 128 (loPackReg r s) (hiPackReg r s) (chunkPackReg r s)))

theorem chunkCode (r : Fin 4) (s : Fin 8) : ChunkCode r s := by
  constructor
  · fin_cases r <;> fin_cases s <;> wg2_code
  · fin_cases r <;> fin_cases s <;> wg2_code
  · fin_cases r <;> fin_cases s <;> wg2_code
  · intro j
    fin_cases r <;> fin_cases s <;> fin_cases j <;> wg2_code
  · intro j
    fin_cases r <;> fin_cases s <;> fin_cases j <;> wg2_code
  · fin_cases r <;> fin_cases s <;> wg2_code
  · fin_cases r <;> fin_cases s <;> wg2_code
  · intro hs
    fin_cases r <;> fin_cases s <;> first | exact (hs rfl).elim | wg2_code
  · fin_cases r <;> fin_cases s <;> wg2_code

private theorem run_chunkWrite {L : Launch} {g : Nat} {t : TState} {pc dst : Nat}
    {F : List (Nat × Value)} {v : Value} {op : Op} (hc : chunkInstruction pc op)
    (hl : op.isLocal = true) (h : At t pc F)
    (he : execLocalA asms L g t op = .ok (PTX.next (setReg t dst v)))
    (hf : ∀ p ∈ F, p.1 ≠ dst) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (pc + 1) ((dst, v) :: F) :=
  ⟨_, run_local hc hl h he, h.set hf⟩

section
variable {L : Launch} {g : Nat} {r : Fin 4}

/-- Select the lane's scale byte, duplicate it to both halves, and widen it to a bf16 pair. -/
theorem run_chunkScale {s : Fin 8} {t : TState} {F : List (Nat × Value)} {lo hi : Nat} {pick : Bool}
    (h : At t (dequantStart r s) F) (hp : t.regs 134 = some (.pred pick))
    (hhi : t.regs (368 + 24 * r.val - 2 * s.val) = some (bits16 hi))
    (hlo : t.regs (367 + 24 * r.val - 2 * s.val) = some (bits16 lo))
    (hs : (if pick then hi else lo) < 255)
    (hkeep : ∀ p ∈ F, p.1 ≠ scaleSelectReg r s ∧ p.1 ≠ scaleDupReg r s ∧ p.1 ≠ scaleWideReg r s) :
    ∃ u, run kernel asms L g 3 t = some u ∧
      At u (dequantStart r s + 3)
        ((scaleWideReg r s, Assumptions.bf16Pair (ue8m0Val (if pick then hi else lo))
          (ue8m0Val (if pick then hi else lo))) :: F) := by
  let scale := if pick then hi else lo
  have hpc : 2696 ≤ dequantStart r s := by
    unfold dequantStart
    omega
  obtain ⟨u1, hr1, h1⟩ := run_chunkWrite (chunkCode r s).select rfl h
    (execLocalA_selScale (by rw [h.1]; exact hpc) hp hhi hlo) (fun p hm => (hkeep p hm).1)
  have hsep1 : scaleSelectReg r s ≠ scaleDupReg r s := by
    unfold scaleSelectReg scaleDupReg chunkIndex
    omega
  have hp1 : 2696 ≤ u1.pc := by rw [h1.1]; omega
  have hkeep1 : ∀ p ∈ (scaleSelectReg r s, bits16 scale) :: F, p.1 ≠ scaleDupReg r s := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hsep1
    · exact (hkeep p hm).2.1
  obtain ⟨u2, hr2, h2⟩ := run_chunkWrite (chunkCode r s).duplicate rfl h1
    (execLocalA_dupScale hp1 h1.2.2.2.2.1 (by omega : scale < 256)) hkeep1
  have hp2 : 2696 ≤ u2.pc := by rw [h2.1]; omega
  have hsep2 : scaleDupReg r s ≠ scaleWideReg r s := by
    unfold scaleDupReg scaleWideReg
    omega
  have hsep3 : scaleSelectReg r s ≠ scaleWideReg r s := by
    unfold scaleSelectReg scaleWideReg chunkIndex
    omega
  have hkeep2 : ∀ p ∈ (scaleDupReg r s, bits16 (scale + 256 * scale)) ::
      (scaleSelectReg r s, bits16 scale) :: F, p.1 ≠ scaleWideReg r s := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hsep2
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact hsep3
      · exact (hkeep p hm).2.2
  obtain ⟨u3, hr3, h3⟩ := run_chunkWrite (chunkCode r s).scaleWiden rfl h2
    (execLocalA_ue8m0 hp2 h2.2.2.2.2.1 hs) hkeep2
  exact ⟨u3, run_comp (run_comp hr1 hr2) hr3, h3.mono ⟨h3.2.2.2.2.1, h3.2.2.2.2.2.2.2⟩⟩

/-- One e4m3 pair is widened and multiplied by the common scale. -/
theorem run_chunkPair {s : Fin 8} {j : Fin 4} {t : TState} {F : List (Nat × Value)}
    {word scale : Nat} (h : At t (dequantStart r s + 3 + 2 * j.val) F)
    (hraw : t.regs (rawPairReg r s j) = some (bits16 (word / 2 ^ (16 * j.val) % 2 ^ 16)))
    (hscale : t.regs (scaleWideReg r s) =
      some (Assumptions.bf16Pair (ue8m0Val scale) (ue8m0Val scale)))
    (hword : ∀ i : Fin 8, byteAt word i.val ≠ 127 ∧ byteAt word i.val ≠ 255)
    (hkeep : ∀ p ∈ F, p.1 ≠ rawWideReg r s j ∧ p.1 ≠ pairProductReg r s j) :
    ∃ t', run kernel asms L g 2 t = some t' ∧
      At t' (dequantStart r s + 5 + 2 * j.val)
        ((pairProductReg r s j, dequantPair word scale j.val) :: F) := by
  let lo := byteAt word (2 * j.val)
  let hi := byteAt word (2 * j.val + 1)
  have hlo : lo ≠ 127 ∧ lo ≠ 255 := hword ⟨2 * j.val, by omega⟩
  have hhi : hi ≠ 127 ∧ hi ≠ 255 := hword ⟨2 * j.val + 1, by omega⟩
  have hsite : 2696 ≤ t.pc := by rw [h.1]; unfold dequantStart; omega
  have hr := hraw
  rw [rawPairBits_eq] at hr
  let u := PTX.next (setReg t (rawWideReg r s j) (.pair (e4m3Widened lo) (e4m3Widened hi)))
  have hc := execLocalA_e4m3 (L := L) (g := g) (dst := rawWideReg r s j) hsite hr
    (byteAt_lt _ _) (byteAt_lt _ _) hlo.1 hlo.2 hhi.1 hhi.2
  have h1 : run kernel asms L g 1 t = some u :=
    run_local ((chunkCode r s).valueWiden j) rfl h hc
  have ha := h.set (r := rawWideReg r s j) (v := .pair (e4m3Widened lo) (e4m3Widened hi))
    (fun p hp => (hkeep p hp).1)
  have ha' : At u (dequantStart r s + 4 + 2 * j.val)
      ((rawWideReg r s j, .pair (e4m3Widened lo) (e4m3Widened hi)) :: F) := by
    have he : dequantStart r s + 3 + 2 * j.val + 1 = dequantStart r s + 4 + 2 * j.val := by omega
    exact he ▸ ha
  have hscale' : u.regs (scaleWideReg r s) =
      some (Assumptions.bf16Pair (ue8m0Val scale) (ue8m0Val scale)) := by
    have hne : scaleWideReg r s ≠ rawWideReg r s j := by
      unfold scaleWideReg rawWideReg
      split <;> omega
    simp [u, PTX.next, setReg, Function.update_of_ne hne, hscale]
  have hsite' : 2696 ≤ u.pc := by
    rw [ha'.1]
    unfold dequantStart
    omega
  have he := execLocalA_pairMul (L := L) (g := g) (dst := pairProductReg r s j)
    hsite' ha'.2.2.2.2.1 hscale'
  let v := PTX.next (setReg u (pairProductReg r s j) (dequantPair word scale j.val))
  have h2 : run kernel asms L g 1 u = some v :=
    run_local ((chunkCode r s).multiply j) rfl ha' he
  have hf : ∀ p ∈ (rawWideReg r s j, .pair (e4m3Widened lo) (e4m3Widened hi)) :: F,
      p.1 ≠ pairProductReg r s j := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · unfold pairProductReg rawWideReg
      omega
    · exact (hkeep p hp).2
  have hb := ha'.set (r := pairProductReg r s j) (v := dequantPair word scale j.val) hf
  have hh : At v (dequantStart r s + 5 + 2 * j.val)
      ((pairProductReg r s j, dequantPair word scale j.val) :: F) := by
    have heq : dequantStart r s + 4 + 2 * j.val + 1 = dequantStart r s + 5 + 2 * j.val := by omega
    have hb' := heq ▸ hb
    exact hb'.mono ⟨hb'.2.2.2.2.1, hb'.2.2.2.2.2.2⟩
  exact ⟨v, run_comp h1 h2, hh⟩

/-- Converted pairs already produced by the unrolled numeric instructions. -/
def convertedPairs (r : Fin 4) (s : Fin 8) (n : Nat) (hn : n ≤ 4)
    (word scale : Nat) : List (Nat × Value) :=
  ((List.finRange n).reverse).map fun j =>
    (pairProductReg r s ⟨j.val, by omega⟩, dequantPair word scale j.val)

theorem convertedPairs_succ (r : Fin 4) (s : Fin 8) {n : Nat} (hn : n < 4)
    (word scale : Nat) :
    convertedPairs r s (n + 1) (by omega) word scale =
      (pairProductReg r s ⟨n, hn⟩, dequantPair word scale n) ::
        convertedPairs r s n (by omega) word scale := by
  unfold convertedPairs
  rw [List.finRange_succ_last, List.reverse_append, List.map_append]
  simp [List.map_reverse, List.map_map, Function.comp_def]

theorem convertedPairs_disjoint {r : Fin 4} {s : Fin 8} {n : Nat} {h : n ≤ 4}
    {word scale : Nat} {q : Nat × Value}
    (hq : q ∈ convertedPairs r s n h word scale) (hn : n < 4) :
    q.1 ≠ rawWideReg r s ⟨n, hn⟩ ∧ q.1 ≠ pairProductReg r s ⟨n, hn⟩ := by
  obtain ⟨⟨j, hj⟩, _, rfl⟩ := List.mem_map.mp hq
  simp only [pairProductReg, rawWideReg]
  split_ifs <;> omega

/-- The four widen-multiply pairs run in order, retaining the supplied frame. -/
theorem run_chunkPairs {s : Fin 8} {t : TState} {F : List (Nat × Value)} {word scale : Nat}
    (n : Nat) (hn : n ≤ 4) (h : At t (dequantStart r s + 3) F)
    (hraw : ∀ j : Fin 4, (rawPairReg r s j, bits16 (word / 2 ^ (16 * j.val) % 2 ^ 16)) ∈ F)
    (hscale : (scaleWideReg r s, Assumptions.bf16Pair (ue8m0Val scale) (ue8m0Val scale)) ∈ F)
    (hword : ∀ i : Fin 8, byteAt word i.val ≠ 127 ∧ byteAt word i.val ≠ 255)
    (hkeep : ∀ p ∈ F, ∀ j : Fin 4, p.1 ≠ rawWideReg r s j ∧ p.1 ≠ pairProductReg r s j) :
    ∃ t', run kernel asms L g (2 * n) t = some t' ∧
      At t' (dequantStart r s + 3 + 2 * n) (convertedPairs r s n hn word scale ++ F) := by
  induction n with
  | zero => exact ⟨t, rfl, h⟩
  | succ n ih =>
    have hn' : n < 4 := by omega
    let j : Fin 4 := ⟨n, hn'⟩
    obtain ⟨u, hu, ha⟩ := ih (by omega)
    have hraw' := holds_mem ha.2.2.2.2 (List.mem_append_right _ (hraw j))
    have hscale' := holds_mem ha.2.2.2.2 (List.mem_append_right _ hscale)
    have hkeep' : ∀ p ∈ convertedPairs r s n (by omega) word scale ++ F,
        p.1 ≠ rawWideReg r s j ∧ p.1 ≠ pairProductReg r s j := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact convertedPairs_disjoint hp hn'
      · exact hkeep p hp j
    obtain ⟨u', hu', ha'⟩ := run_chunkPair ha hraw' hscale' hword hkeep'
    have hlen : 2 * n + 2 = 2 * (n + 1) := by omega
    have hpc : dequantStart r s + 5 + 2 * n = dequantStart r s + 3 + 2 * (n + 1) := by omega
    rw [convertedPairs_succ r s hn']
    exact ⟨u', hlen ▸ run_comp hu hu', hpc ▸ ha'⟩

private theorem pairProductReg_lt (r : Fin 4) (s : Fin 8) (j : Fin 4) :
    pairProductReg r s j < 2800 := by
  unfold pairProductReg rawWideReg chunkIndex
  split <;> omega

private theorem hiPackReg_gt (r : Fin 4) (s : Fin 8) : 3800 < hiPackReg r s := by
  unfold hiPackReg
  split <;> omega

/-- Pack four products into the two 64-bit halves of the shared store. -/
theorem run_chunkHalfPacks {s : Fin 8} {t : TState} {F : List (Nat × Value)} {word scale : Nat}
    (h : At t (dequantStart r s + 11) (convertedPairs r s 4 (by decide) word scale ++ F))
    (hkeep : ∀ p ∈ F, p.1 ≠ hiPackReg r s ∧ p.1 ≠ loPackReg r s) :
    ∃ u, run kernel asms L g 2 t = some u ∧
      At u (dequantStart r s + 13)
        ((loPackReg r s, .pair (dequantPair word scale 0) (dequantPair word scale 1)) ::
         (hiPackReg r s, .pair (dequantPair word scale 2) (dequantPair word scale 3)) :: F) := by
  let pairs := convertedPairs r s 4 (by decide) word scale
  have hprod (j : Fin 4) : (pairProductReg r s j, dequantPair word scale j.val) ∈ pairs := by
    apply List.mem_map.mpr
    exact ⟨j, by simp, rfl⟩
  have hframe (p : Nat × Value) (hm : p ∈ pairs ++ F) :
      p.1 ≠ hiPackReg r s ∧ p.1 ≠ loPackReg r s := by
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hm
      have hlow := pairProductReg_lt r s ⟨j.val, j.isLt⟩
      have hhigh := hiPackReg_gt r s
      unfold loPackReg
      constructor <;> omega
    · exact hkeep p hm
  have hpc : 2696 ≤ t.pc := by rw [h.1]; unfold dequantStart; omega
  have hread (j : Fin 4) := holds_mem h.2.2.2.2 (List.mem_append_left _ (hprod j))
  obtain ⟨t1, hr1, h1⟩ := run_chunkWrite (chunkCode r s).highPack rfl h
    (execLocalA_packChunk hpc (Or.inl rfl) (hread 2) (hread 3) rfl rfl)
    (fun p hm => (hframe p hm).1)
  have hpc1 : 2696 ≤ t1.pc := by rw [h1.1]; rw [h.1] at hpc; omega
  have hread1 (j : Fin 4) := holds_mem h1.2.2.2.2
    (List.mem_cons_of_mem _ (List.mem_append_left _ (hprod j)))
  have hframe1 : ∀ p ∈ (hiPackReg r s,
        joinValue (dequantPair word scale 2) (dequantPair word scale 3)) :: (pairs ++ F),
      p.1 ≠ loPackReg r s := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold loPackReg
      omega
    · exact (hframe p hm).2
  obtain ⟨t2, hr2, h2⟩ := run_chunkWrite (chunkCode r s).lowPack rfl h1
    (execLocalA_packChunk hpc1 (Or.inl rfl) (hread1 0) (hread1 1) rfl rfl) hframe1
  have htail := ((holds_append _ _ _).mp h2.2.2.2.2.2.2).2
  exact ⟨t2, run_comp hr1 hr2, h2.mono ⟨h2.2.2.2.2.1, h2.2.2.2.2.2.1, htail⟩⟩

theorem execLocalA_storeAdd {s : Fin 8} {t : TState} {a : Nat} (hpc : 2696 ≤ t.pc)
    (hb : t.regs 2472 = some (b32 a)) (hlt : a + tileChunkDelta r s < 2 ^ 32) :
    execLocalA asms L g t (.int (storeAdd r s)) =
      .ok (PTX.next (setReg t (storeBaseReg r s) (b32 (a + tileChunkDelta r s)))) := by
  rw [execLocalA_dequant hpc rfl rfl rfl rfl]
  change execInt L g t (storeAdd r s) = _
  simp only [storeAdd, execInt, DType.width, readValue, readBits, readReg, hb, b32,
    bind, Except.bind, pure, Except.pure, BitVec.ofInt_natCast]
  rw [trunc32_add_word (by omega) hlt]

private theorem hiPackReg_lt (r : Fin 4) (s : Fin 8) : hiPackReg r s < 4038 := by
  unfold hiPackReg
  omega

private theorem storeBaseReg_lt (r : Fin 4) (s : Fin 8) : storeBaseReg r s < 2800 := by
  unfold storeBaseReg chunkIndex
  omega

/-- Finish the address, if needed, and pack the final 128-bit register. -/
theorem run_chunkFinish {s : Fin 8} {t : TState} {F : List (Nat × Value)} {word scale base : Nat}
    (h : At t (dequantStart r s + 13)
      ((loPackReg r s, .pair (dequantPair word scale 0) (dequantPair word scale 1)) ::
       (hiPackReg r s, .pair (dequantPair word scale 2) (dequantPair word scale 3)) :: F))
    (hbase : (2472, b32 base) ∈ F)
    (hbase0 : s.val = 0 → (storeBaseReg r s, b32 (base + tileChunkDelta r s)) ∈ F)
    (hfit : base + tileChunkDelta r s < 2 ^ 32)
    (hkeep : ∀ p ∈ F, p.1 ≠ chunkPackReg r s ∧ (s.val ≠ 0 → p.1 ≠ storeBaseReg r s)) :
    ∃ u, run kernel asms L g (if s.val = 0 then 1 else 2) t = some u ∧
      At u (dequantStart r s + (if s.val = 0 then 14 else 15))
        ((chunkPackReg r s, dequantChunk word scale) ::
          (storeBaseReg r s, b32 (base + tileChunkDelta r s)) :: F) := by
  let lo := (loPackReg r s, Value.pair (dequantPair word scale 0) (dequantPair word scale 1))
  let hi := (hiPackReg r s, Value.pair (dequantPair word scale 2) (dequantPair word scale 3))
  let addr := (storeBaseReg r s, b32 (base + tileChunkDelta r s))
  let n := if s.val = 0 then 0 else 1
  have hn : n + 1 = (if s.val = 0 then 1 else 2) := by dsimp [n]; split <;> rfl
  have hp : dequantStart r s + 13 + n = dequantStart r s + (if s.val = 0 then 13 else 14) := by
    dsimp [n]; split <;> omega
  have hfin : dequantStart r s + (if s.val = 0 then 13 else 14) + 1 =
      dequantStart r s + (if s.val = 0 then 14 else 15) := by
    split <;> omega
  have hlow := storeBaseReg_lt r s
  have hhi := hiPackReg_gt r s
  have hhi' := hiPackReg_lt r s
  have hpref : ∃ v, run kernel asms L g n t = some v ∧
      At v (dequantStart r s + 13 + n) (lo :: hi :: addr :: F) := by
    by_cases hs : s.val = 0
    · have ht := h.mono (G := lo :: hi :: addr :: F)
        ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, holds_mem h.2.2.2.2.2.2 (hbase0 hs), h.2.2.2.2.2.2⟩
      simpa [n, hs] using (show ∃ v, run kernel asms L g 0 t = some v ∧
        At v (dequantStart r s + 13) (lo :: hi :: addr :: F) from ⟨t, rfl, ht⟩)
    · have hread : t.regs 2472 = some (b32 base) := holds_mem h.2.2.2.2
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hbase))
      have hpc : 2696 ≤ t.pc := by rw [h.1]; unfold dequantStart; omega
      have hf : ∀ p ∈ lo :: hi :: F, p.1 ≠ storeBaseReg r s := by
        intro p hm
        rcases List.mem_cons.mp hm with rfl | hm
        · change loPackReg r s ≠ storeBaseReg r s
          unfold loPackReg
          omega
        · rcases List.mem_cons.mp hm with rfl | hm
          · change hiPackReg r s ≠ storeBaseReg r s
            omega
          · exact (hkeep p hm).2 hs
      obtain ⟨v, hv, ha⟩ := run_chunkWrite ((chunkCode r s).address hs) rfl h
        (execLocalA_storeAdd hpc hread hfit) hf
      have hv' := ha.mono (G := lo :: hi :: addr :: F)
        ⟨ha.2.2.2.2.2.1, ha.2.2.2.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.2.2⟩
      exact ⟨v, by simpa [n, hs] using hv, by simpa [n, hs] using hv'⟩
  obtain ⟨v, hv, ha⟩ := hpref
  have ha' := hp ▸ ha
  have hpc' : 2696 ≤ v.pc := by rw [ha.1]; unfold dequantStart; omega
  have hframe : ∀ p ∈ lo :: hi :: addr :: F, p.1 ≠ chunkPackReg r s := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change loPackReg r s ≠ chunkPackReg r s
      unfold loPackReg chunkPackReg
      omega
    · rcases List.mem_cons.mp hm with rfl | hm
      · change hiPackReg r s ≠ chunkPackReg r s
        unfold chunkPackReg
        omega
      · rcases List.mem_cons.mp hm with rfl | hm
        · change storeBaseReg r s ≠ chunkPackReg r s
          unfold chunkPackReg
          omega
        · exact (hkeep p hm).1
  obtain ⟨u, hu, hlast⟩ := run_chunkWrite (chunkCode r s).chunkPack rfl ha'
    (execLocalA_packChunk hpc' (Or.inr rfl) ha.2.2.2.2.1 ha.2.2.2.2.2.1 rfl rfl) hframe
  have hend := hfin ▸ hlast
  exact ⟨u, hn ▸ run_comp hv hu, hend.mono ⟨hend.2.2.2.2.1, hend.2.2.2.2.2.2.2⟩⟩

/-- All register destinations in the contiguous arithmetic of one tile chunk. -/
def chunkWrites (r : Fin 4) (s : Fin 8) : List Nat :=
  [scaleSelectReg r s, scaleDupReg r s, scaleWideReg r s,
    hiPackReg r s, loPackReg r s, chunkPackReg r s] ++
  ((List.finRange 4).flatMap (fun j => [rawWideReg r s j, pairProductReg r s j]) ++
    if s.val = 0 then [] else [storeBaseReg r s])

theorem dequantStart_end (r : Fin 4) (s : Fin 8) :
    dequantStart r s + (if s.val = 0 then 14 else 15) = (Site.store r s).pc := by
  fin_cases r <;> fin_cases s <;> rfl

/-- One local segment converts eight e4m3 bytes to the exact packed bf16 store value. -/
theorem run_chunkCompute {s : Fin 8} {t : TState} {F : List (Nat × Value)} {word lo hi base : Nat}
    {pick : Bool} (h : At t (dequantStart r s) F) (hp : t.regs 134 = some (.pred pick))
    (hhi : t.regs (368 + 24 * r.val - 2 * s.val) = some (bits16 hi))
    (hlo : t.regs (367 + 24 * r.val - 2 * s.val) = some (bits16 lo))
    (hs : (if pick then hi else lo) < 255)
    (hraw : ∀ j : Fin 4, (rawPairReg r s j, bits16 (word / 2 ^ (16 * j.val) % 2 ^ 16)) ∈ F)
    (hword : RawWordOk word) (hbase : (2472, b32 base) ∈ F)
    (hbase0 : s.val = 0 → (storeBaseReg r s, b32 (base + tileChunkDelta r s)) ∈ F)
    (hfit : base + tileChunkDelta r s < 2 ^ 32) (hframe : ∀ p ∈ F, p.1 ∉ chunkWrites r s) :
    ∃ u, run kernel asms L g (if s.val = 0 then 14 else 15) t = some u ∧
      At u (Site.store r s).pc
        ((chunkPackReg r s, dequantChunk word (if pick then hi else lo)) ::
          (storeBaseReg r s, b32 (base + tileChunkDelta r s)) :: F) := by
  let scale := if pick then hi else lo
  have hkeep p (hm : p ∈ F) := hframe p hm
  have hf0 : ∀ p ∈ F, p.1 ≠ scaleSelectReg r s ∧
      p.1 ≠ scaleDupReg r s ∧ p.1 ≠ scaleWideReg r s := by
    intro p hm
    have he := hkeep p hm
    simp only [chunkWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at he
    exact ⟨he.1.1, he.1.2.1, he.1.2.2.1⟩
  obtain ⟨u1, hr1, h1⟩ := run_chunkScale h hp hhi hlo hs hf0
  let sc := (scaleWideReg r s, Assumptions.bf16Pair (ue8m0Val scale) (ue8m0Val scale))
  have hf1 : ∀ p ∈ sc :: F, ∀ j : Fin 4, p.1 ≠ rawWideReg r s j ∧
      p.1 ≠ pairProductReg r s j := by
    intro p hm j
    rcases List.mem_cons.mp hm with rfl | hm
    · change scaleWideReg r s ≠ rawWideReg r s j ∧ scaleWideReg r s ≠ pairProductReg r s j
      unfold scaleWideReg rawWideReg pairProductReg
      simp only [rawWideReg]
      split_ifs <;> omega
    · have ht := hkeep p hm
      have hin : p.1 ∉ (List.finRange 4).flatMap
          (fun j => [rawWideReg r s j, pairProductReg r s j]) :=
        fun hmem => ht (by simp only [chunkWrites, List.mem_append]; exact Or.inr (Or.inl hmem))
      have hx (reg : Nat) (hr : reg ∈ [rawWideReg r s j, pairProductReg r s j]) :
          p.1 ≠ reg := fun he =>
        hin (List.mem_flatMap.mpr ⟨j, by simp, he.symm ▸ hr⟩)
      exact ⟨hx _ (by simp), hx _ (by simp)⟩
  obtain ⟨u2, hr2, h2⟩ := run_chunkPairs 4 (by decide) h1
    (fun j => List.mem_cons_of_mem _ (hraw j)) (List.mem_cons_self ..) hword.2 hf1
  have hlo' := hiPackReg_gt r s
  have hsc : scaleWideReg r s < 2800 := by unfold scaleWideReg chunkIndex; omega
  have hf2 : ∀ p ∈ sc :: F, p.1 ≠ hiPackReg r s ∧ p.1 ≠ loPackReg r s := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change scaleWideReg r s ≠ hiPackReg r s ∧ scaleWideReg r s ≠ loPackReg r s
      unfold loPackReg
      constructor <;> omega
    · have he := hkeep p hm
      simp only [chunkWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at he
      exact ⟨he.1.2.2.2.1, he.1.2.2.2.2.1⟩
  obtain ⟨u3, hr3, h3⟩ := run_chunkHalfPacks h2 hf2
  have hf3 : ∀ p ∈ sc :: F, p.1 ≠ chunkPackReg r s ∧
      (s.val ≠ 0 → p.1 ≠ storeBaseReg r s) := by
    intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · change scaleWideReg r s ≠ chunkPackReg r s ∧ (s.val ≠ 0 → scaleWideReg r s ≠ storeBaseReg r s)
      unfold scaleWideReg chunkPackReg storeBaseReg
      omega
    · have he := hkeep p hm
      simp only [chunkWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at he
      exact ⟨he.1.2.2.2.2.2, fun hs0 => by simpa [hs0] using he.2.2⟩
  obtain ⟨u4, hr4, h4⟩ := run_chunkFinish h3 (List.mem_cons_of_mem _ hbase)
    (fun hs0 => List.mem_cons_of_mem _ (hbase0 hs0)) hfit hf3
  have hlen : 3 + 2 * 4 + 2 + (if s.val = 0 then 1 else 2) =
      (if s.val = 0 then 14 else 15) := by split <;> rfl
  have hpc := dequantStart_end r s ▸ h4
  exact ⟨u4, hlen ▸ run_comp (run_comp (run_comp hr1 hr2) hr3) hr4,
    hpc.mono ⟨hpc.2.2.2.2.1, hpc.2.2.2.2.2.1, hpc.2.2.2.2.2.2.2⟩⟩
end

def tileStore (r : Fin 4) (s : Fin 8) : MemAccess where
  kind := .store
  space := some (.shared .cta)
  sem := .weak
  elem := .int .b 128
  addr := ⟨.reg (storeBaseReg r s) 32, 0⟩
  srcs := [.reg (chunkPackReg r s)]

theorem tileStore_code (r : Fin 4) (s : Fin 8) :
    kernel.code[(Site.store r s).pc]? = some ⟨none, .mem (tileStore r s)⟩ := by
  fin_cases r <;> fin_cases s <;> wg2_code

theorem sharedTile_lt {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {d : D}
    (hpre : Pre P L mem0) (hinv : Inv P L g d) (r : Fin 4) (s : Fin 8) :
    L.sharedBase + tileBase d.buf + tileOff L g r.val s.val < 2 ^ 32 := by
  have h := tile_fit (L := L) (g := g) r.isLt s.isLt
  have hb := hinv.bufLt
  have hshared := sharedBase_lt hpre
  simp only [tileBase, dequantBytes] at h ⊢
  omega

theorem sharedTile_align {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (g buf : Nat) (r : Fin 4) (s : Fin 8) :
    (L.sharedBase + tileBase buf + tileOff L g r.val s.val) % 16 = 0 := by
  have hbase : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  simp only [tileBase, dequantBytes, tileOff, dstOff, numGroups, topkBlock]
  omega

variable {P : Params} {L : Launch} {g : Nat}

/-- A tile store writes all sixteen bytes of the packed bf16 value in byte order. -/
theorem tileStore_template {mem0 : Mem0} {d : D} {r : Fin 4} {s : Fin 8} {t : TState} {v : Value}
    (hpre : Pre P L mem0) (hd : d.site = .store r s) (hat : AtD P L g d t) (hinv : Inv P L g d)
    (ha : t.regs (storeBaseReg r s) = some (sb L (tileBase d.buf + tileOff L g r.val s.val)))
    (hv : t.regs (chunkPackReg r s) = some v) (hv16 : v.bytes = 16) :
    eventTmpl asms L g t (.mem (tileStore r s)) =
      .write { loc := ⟨.shared, ctaOf L g,
        L.sharedBase + tileBase d.buf + tileOff L g r.val s.val⟩, size := 16 }
        v.toBytes (PTX.next t) := by
  have hsub : t.sub = 0 := by rw [hat.2.1, hd]; rfl
  have hra : t.regs (storeBaseReg r s) = some (b32
      (L.sharedBase + tileBase d.buf + tileOff L g r.val s.val)) := by
    simpa [sb, Nat.add_assoc] using ha
  let addr := L.sharedBase + tileBase d.buf + tileOff L g r.val s.val
  have hFit : addr + 0 < 2 ^ 32 := by simpa [addr] using sharedTile_lt hpre hinv r s
  have hAlign : addr % 16 = 0 := sharedTile_align hpre g d.buf r s
  have hAddr : effAddr L g t .shared (storeBaseReg r s) 0 =
      .ok ⟨.shared, g / L.block, addr⟩ := by
    simpa only [Nat.cast_zero, Nat.add_zero] using
      (effAddr_b32_off (L := L) (g := g) (off := 0) hra hFit)
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := storeBaseReg r s) (w := 32)
    rfl rfl rfl rfl (by simp [tileStore])]
  change storeTmpl L g t .shared 128 (storeBaseReg r s) 0 [.reg (chunkPackReg r s)] = _
  simp only [storeTmpl, hAddr, bind, Except.bind, hsub]
  rw [elemAcc_ok (by decide) (by simpa [addr] using hAlign)]
  simp only [pure, Except.pure, List.getElem?_singleton, readValue, readReg, ite_true, hv]
  rw [storeValue_of_bytes (w := 128) (v := v) (by omega)]
  simp [PTX.afterStore, hsub, Loc.at, PTX.next, addr, ctaOf]

/-- A load past the first word prefetches one step while the previous word is computed. -/
def rawPrevStep (s : Fin 8) : Fin 8 := ⟨s.val - 1, by omega⟩

theorem rawBeforeStore_pc (r : Fin 4) (s : Fin 8) (hs : s.val ≠ 0) :
    (Site.raw r s).pc + 1 = dequantStart r (rawPrevStep s) := by
  fin_cases r <;> fin_cases s <;> first | exact (hs rfl).elim | rfl

def rawFrame (P : Params) (L : Launch) (g : Nat) (d : D) (r : Fin 4) (s : Fin 8) (word : Nat) :
    List (Nat × Value) :=
  (rawLoadReg r s.val, b64 word) :: (scaleByteFacts r d ++
    (rawPairFacts r (rawPrevStep s).val d.raw ++ atFacts P L g d (Site.raw r s).pc))

theorem rawFrame_baseMem {d : D} {r : Fin 4} {s : Fin 8} {word reg : Nat}
    (hm : reg ∈ (Flow.live (Site.raw r s).pc).filter (fun x => tracked.contains x)) :
    (reg, valueOf P L g d reg) ∈ rawFrame P L g d r s word :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ (mem_factsFrom hm)))

theorem rawFrame_scaleMem {d : D} {r : Fin 4} {s : Fin 8} {word : Nat} (i : Fin 16) :
    (353 + 24 * r.val + scaleByteRegIndex i.val, bits16 (byteAt d.sc i.val)) ∈
      rawFrame P L g d r s word := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨scaleByteRegIndex i.val, List.mem_range.mpr (scaleByteRegIndex_lt i.val), ?_⟩
  have he := scaleRegByte_eq d.sc i
  dsimp only at he
  simp only [scaleWord, bits16, he]

theorem rawFrame_pairMem {d : D} {r : Fin 4} {s : Fin 8} {word : Nat} (j : Fin 4) :
    (rawPairReg r (rawPrevStep s) j, bits16 (d.raw / 2 ^ (16 * j.val) % 2 ^ 16)) ∈
      rawFrame P L g d r s word := by
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
  have he : 192 + 40 * r.val + 5 * (rawPrevStep s).val + j.val =
      rawPairReg r (rawPrevStep s) j := by
    unfold rawPairReg scaleDupReg chunkIndex
    omega
  simp [bits16, he]

/-- The raw/scale words and tracked scalar registers are disjoint from a chunk's destinations. -/
theorem rawFrame_preserved {d : D} {r : Fin 4} {s : Fin 8} {word : Nat} (hs : s.val ≠ 0) :
    ∀ p ∈ rawFrame P L g d r s word, p.1 ∉ chunkWrites r (rawPrevStep s) := by
  let keys := rawLoadReg r s.val :: ((List.range 16).map (fun j => 353 + 24 * r.val + j) ++
    ((List.range 4).map (fun j => 192 + 40 * r.val + 5 * (rawPrevStep s).val + j) ++ tracked))
  have hkeys : keys.all (fun k => !(chunkWrites r (rawPrevStep s)).contains k) = true := by
    fin_cases r <;> fin_cases s <;> first | exact (hs rfl).elim | decide +kernel
  intro p hp
  have hm : p.1 ∈ keys := by
    simp only [rawFrame, List.mem_cons, List.mem_append] at hp
    rcases hp with rfl | hp | hp | hp
    · exact List.mem_cons_self ..
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hj))
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_append_left _ (List.mem_map_of_mem hj)))
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      have ht := (List.mem_filter.mp hk).2
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_append_right _ (List.contains_iff_mem.mp ht)))
  simpa using List.all_eq_true.mp hkeys p.1 hm

theorem rawCompute_live (r : Fin 4) (s : Fin 8) (hs : s.val ≠ 0) :
    let regs := (Flow.live (Site.raw r s).pc).filter (fun x => tracked.contains x)
    134 ∈ regs ∧ 2472 ∈ regs ∧ (s.val = 1 → storeBaseReg r 0 ∈ regs) := by
  fin_cases r <;> fin_cases s <;> first | exact (hs rfl).elim | decide +kernel

theorem scaleReg_ids (r : Fin 4) (s : Fin 8) :
    353 + 24 * r.val + scaleByteRegIndex (2 * s.val) = 367 + 24 * r.val - 2 * s.val ∧
    353 + 24 * r.val + scaleByteRegIndex (2 * s.val + 1) = 368 + 24 * r.val - 2 * s.val := by
  fin_cases s <;> simp [scaleByteRegIndex] <;> omega

/-- A scalar raw load updates only the prefetch register. -/
theorem afterLoad_raw_later {d : D} {r : Fin 4} {s : Fin 8} {t : TState} {bs : List (Option Byte)}
    (hs : s.val ≠ 0) (hd : d.site = .raw r s) (hat : AtD P L g d t)
    (hv : rebuild 3 bs = .ok (b64 (rawBits bs))) :
    At (afterLoad t (rawLoad r s).regs bs) (dequantStart r (rawPrevStep s))
      (rawFrame P L g d r s (rawBits bs)) := by
  have hsub : t.sub = 0 := by rw [hat.2.1, hd]; rfl
  have hacc : t.acc = [] := by rw [hat.2.2.1, accAt, hd]
  have hbase := hat.baseRegs
  rw [baseFacts, hd] at hbase
  have hpayload : Holds t.regs (scaleByteFacts r d ++ rawPairFacts r (s.val - 1) d.raw) := by
    simpa [payloadFacts, hd, hs] using hat.payloadRegs
  have he : afterLoad t (rawLoad r s).regs bs =
      PTX.next (setReg t (rawLoadReg r s.val) (b64 (rawBits bs))) := by
    rw [afterLoad, hv, hsub, hacc]
    simp [rawLoad, MemAccess.regs, setRegs, hsub, hacc, PTX.next, setReg]
  let F := scaleByteFacts r d ++
    (rawPairFacts r (rawPrevStep s).val d.raw ++ atFacts P L g d (Site.raw r s).pc)
  have ha : At t (Site.raw r s).pc F := by
    refine ⟨hat.1.trans (congrArg Site.pc hd), hsub, hacc, hat.2.2.2.1, ?_⟩
    dsimp [F, rawPrevStep]
    exact (holds_append _ _ _).mpr
      ⟨(holds_append _ _ _).mp hpayload |>.1, (holds_append _ _ _).mpr
        ⟨(holds_append _ _ _).mp hpayload |>.2, hbase⟩⟩
  have hz : ∀ p ∈ F, p.1 ≠ rawLoadReg r s.val := by
    intro p hp
    simp only [F, List.mem_append] at hp
    rcases hp with hp | hp | hp
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      have hj' := List.mem_range.mp hj
      unfold rawLoadReg
      omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      have hj' := List.mem_range.mp hj
      unfold rawLoadReg rawPrevStep
      omega
    · obtain ⟨reg, hmem, rfl⟩ := List.mem_map.mp hp
      have hf := (List.mem_filter.mp hmem).2
      have hn : tracked.contains (rawLoadReg r s.val) = false := by
        fin_cases r <;> fin_cases s <;> decide +kernel
      intro heq
      change reg = rawLoadReg r s.val at heq
      rw [heq, hn] at hf
      cases hf
  rw [he, ← rawBeforeStore_pc r s hs]
  exact ha.set hz

/-- Prefetched bits are kept through the preceding chunk's numerical instructions. -/
def rawStoreState (d : D) (r : Fin 4) (s : Fin 8) (word : Nat) : D :=
  { d with site := .store r (rawPrevStep s), nxt := word }

theorem rawToStore_live (r : Fin 4) (s : Fin 8) (hs : s.val ≠ 0) :
    ∀ reg ∈ (Flow.live (Site.store r (rawPrevStep s)).pc).filter tracked.contains,
      reg ∈ (Flow.live (Site.raw r s).pc).filter tracked.contains := by
  have hc : ((Flow.live (Site.store r (rawPrevStep s)).pc).filter tracked.contains).all
      (fun reg => ((Flow.live (Site.raw r s).pc).filter tracked.contains).contains reg) = true := by
    fin_cases r <;> fin_cases s <;> first | exact (hs rfl).elim | decide +kernel
  simpa using List.all_eq_true.mp hc

theorem run_rawCompute {mem0 : Mem0} {d : D} {r : Fin 4} {s : Fin 8} {t : TState} {word : Nat}
    (hpre : Pre P L mem0) (hs : s.val ≠ 0) (hd : d.site = .raw r s) (hinv : Inv P L g d)
    (h : At t (dequantStart r (rawPrevStep s)) (rawFrame P L g d r s word)) :
    let d' := rawStoreState d r s word
    ∃ u, run kernel asms L g (if (rawPrevStep s).val = 0 then 14 else 15) t = some u ∧
      At u d'.site.pc (storePayload L g r (rawPrevStep s) d' ++ atFacts P L g d' d'.site.pc) := by
  let col := rawPrevStep s
  let d' := rawStoreState d r s word
  let F := rawFrame P L g d r s word
  let pick := decide (groupSize / 2 ≤ idxInGroup L g)
  let i0 : Fin 16 := ⟨2 * col.val, by have := col.isLt; omega⟩
  let i1 : Fin 16 := ⟨2 * col.val + 1, by have := col.isLt; omega⟩
  let base := L.sharedBase + (tileBase d.buf + dstOff L g)
  have hp : t.regs 134 = some (.pred pick) := by
    have hm := holds_mem h.2.2.2.2 (rawFrame_baseMem (rawCompute_live r s hs).1)
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, pick] using hm
  have h0 : t.regs (367 + 24 * r.val - 2 * col.val) = some (bits16 (byteAt d.sc i0.val)) := by
    have hm := holds_mem h.2.2.2.2 (rawFrame_scaleMem i0)
    dsimp only [i0] at hm
    rw [(scaleReg_ids r col).1] at hm
    exact hm
  have h1 : t.regs (368 + 24 * r.val - 2 * col.val) = some (bits16 (byteAt d.sc i1.val)) := by
    have hm := holds_mem h.2.2.2.2 (rawFrame_scaleMem i1)
    dsimp only [i1] at hm
    rw [(scaleReg_ids r col).2] at hm
    exact hm
  have hselect : (if pick then byteAt d.sc i1.val else byteAt d.sc i0.val) =
      byteAt d.sc (scaleIdx L g col.val) := by
    by_cases hpick : groupSize / 2 ≤ idxInGroup L g <;>
      simp [pick, scaleIdx, hpick, i0, i1]
  have hfinite := hinv.payloadOk
  rw [PayloadOk, hd] at hfinite
  have hscale : (if pick then byteAt d.sc i1.val else byteAt d.sc i0.val) < 255 := by
    rw [hselect]
    exact hfinite.1 ⟨scaleIdx L g col.val, scaleIdx_lt (by exact col.isLt)⟩
  have hbase : (2472, b32 base) ∈ F := by
    have hm := rawFrame_baseMem (P := P) (L := L) (g := g) (d := d) (word := word)
      (rawCompute_live r s hs).2.1
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, F, sb, base] using hm
  have haeq : base + tileChunkDelta r col =
      L.sharedBase + (tileBase d.buf + tileOff L g r.val col.val) := by
    simp [base, tileChunkDelta, tileOff, numGroups, topkBlock, Nat.add_assoc]
  have hbase0 : col.val = 0 → (storeBaseReg r col, b32 (base + tileChunkDelta r col)) ∈ F := by
    intro hcol
    have hs1 : s.val = 1 := by dsimp [col, rawPrevStep] at hcol; omega
    have hc0 : col = 0 := Fin.eq_of_val_eq hcol
    have hbr : storeBaseReg r col ∈ (Flow.live (Site.raw r s).pc).filter tracked.contains := by
      rw [hc0]
      exact (rawCompute_live r s hs).2.2 hs1
    have hm := rawFrame_baseMem (P := P) (L := L) (g := g) (d := d) (word := word) hbr
    have hval : valueOf P L g d (storeBaseReg r col) = b32 (base + tileChunkDelta r col) := by
      rw [haeq, hc0]
      fin_cases r <;> simp [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
        storeBaseReg, chunkIndex, sb, tileOff, numGroups]
    rw [hval] at hm
    exact hm
  have hfit : base + tileChunkDelta r col < 2 ^ 32 := by
    rw [haeq, ← Nat.add_assoc]
    exact sharedTile_lt hpre hinv r col
  obtain ⟨u, hr, hout⟩ := run_chunkCompute h hp h1 h0 hscale rawFrame_pairMem
    (hfinite.2 hs) hbase hbase0 hfit (rawFrame_preserved hs)
  have hout' : At u d'.site.pc
      ((chunkPackReg r col, dequantChunk d'.raw (byteAt d'.sc (scaleIdx L g col.val))) ::
        (storeBaseReg r col, sb L (tileBase d'.buf + tileOff L g r.val col.val)) :: F) := by
    rw [hselect, haeq] at hout
    exact hout
  have hF : Holds u.regs F := hout'.2.2.2.2.2.2
  have hval : valueOf P L g d' = valueOf P L g d := by
    funext reg
    simp [valueOf, table, d', rawStoreState, hd]
  have hfinal : Holds u.regs (atFacts P L g d' d'.site.pc) := by
    rw [atFacts, hval]
    apply holds_of_pointwise
    intro reg hmem
    exact holds_mem hF (rawFrame_baseMem (rawToStore_live r s hs reg hmem))
  have hsucc : (rawPrevStep s).val + 1 = s.val := by dsimp [rawPrevStep]; omega
  have hsc : Holds u.regs (scaleByteFacts r d') := by
    change Holds u.regs (scaleByteFacts r d)
    exact ((holds_append _ _ _).mp hF.2).1
  have htail : Holds u.regs ([(rawLoadReg r s.val, b64 word)] ++ scaleByteFacts r d' ++
      atFacts P L g d' d'.site.pc) :=
    (holds_append _ _ _).mpr
      ⟨(holds_append _ _ _).mpr ⟨⟨hF.1, trivial⟩, hsc⟩, hfinal⟩
  refine ⟨u, hr, hout'.mono ?_⟩
  simp only [storePayload, hsucc, ite_eq_left s.isLt, List.cons_append, List.nil_append]
  exact ⟨hout'.2.2.2.2.1, hout'.2.2.2.2.2.1, htail⟩

/-- Every noninitial raw load runs the preceding chunk's numerical instructions before its store. -/
theorem stepAt_raw_later {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4} {s : Fin 8}
    (hd : d.site = .raw r s) (hs : s.val ≠ 0) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (rawLoad r s)⟩ := by
      rw [hd]
      exact rawLoad_code r s
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, bs, he, ha, hsize, hu⟩ := fires_raw hpre hd hat hinv hf
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b64 (rawBits bs)) ∧ RawWordOk (rawBits bs)
    · let d' := rawStoreState d r s (rawBits bs)
      have hstart := afterLoad_raw_later hs hd hat hv.1
      rw [← hu] at hstart
      obtain ⟨t', hr, ht⟩ := run_rawCompute hpre hs hd hinv hstart
      have hfin := hinv.payloadOk
      rw [PayloadOk, hd] at hfin
      have hnew : Inv P L g d' :=
        ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
          hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
          (by intro heq; cases heq), hinv.lenLt, hinv.batch, ⟨hfin.1, hfin.2 hs, fun _ => hv.2⟩⟩
      refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, ?_⟩)
      · simp [next, nextSite, hd, ha, hsize, rawBytesPerThread, hv.1, hv.2, hs, d',
          rawStoreState, afterRaw, rawPrevStep]
      · change AtD P L g d' t' ∧ Inv P L g d'
        exact ⟨AtD.of_all_facts (d := d') rfl rfl rfl ht, hnew⟩
    · exact Or.inl (Or.inl (by simp [next, nextSite, hd, ha, hsize, rawBytesPerThread, hv]))

theorem stepAt_raw {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4} {s : Fin 8}
    (hd : d.site = .raw r s) :
    (code P L g).StepAt d := by
  by_cases hs : s.val = 0
  · have he : s = 0 := Fin.eq_of_val_eq hs
    exact stepAt_raw_first hpre d (he ▸ hd)
  · exact stepAt_raw_later hpre d hd hs

/-- The store template is determined by the held address and BF16 pack. -/
theorem tileStore_payload_template {mem0 : Mem0} {d : D} {r : Fin 4} {s : Fin 8} {t : TState}
    (hpre : Pre P L mem0) (hd : d.site = .store r s) (hat : AtD P L g d t) (hinv : Inv P L g d) :
    eventTmpl asms L g t (.mem (tileStore r s)) =
      .write { loc := ⟨.shared, ctaOf L g,
        L.sharedBase + tileBase d.buf + tileOff L g r.val s.val⟩, size := 16 }
        (dequantChunk d.raw (byteAt d.sc (scaleIdx L g s.val))).toBytes (PTX.next t) := by
  have hp : Holds t.regs (storePayload L g r s d) := by
    simpa [payloadFacts, hd] using hat.payloadRegs
  exact tileStore_template hpre hd hat hinv hp.2.1 hp.1 (dequantChunk_width _ _)

/-- A fired store exposes the exact eight values of the current dequantized chunk. -/
theorem fires_tileStore_payload {mem0 : Mem0} {d : D} {r : Fin 4} {s : Fin 8} {t u : TState}
    {e : Event} (hpre : Pre P L mem0) (hd : d.site = .store r s) (hat : AtD P L g d t)
    (hinv : Inv P L g d)
    (hf : Fires d.site.pc (eventTmpl asms L g t (.mem (tileStore r s))) e (some u)) :
    ∃ ac, e = ⟨d.site.pc, .wr ac (dequantChunk d.raw (byteAt d.sc (scaleIdx L g s.val))).toBytes⟩ ∧
      ac.loc = ⟨.shared, ctaOf L g, L.sharedBase + tileBase d.buf + tileOff L g r.val s.val⟩ ∧
      ac.size = 16 ∧ u = PTX.next t := by
  rw [tileStore_payload_template hpre hd hat hinv] at hf
  obtain ⟨rfl, hu⟩ := hf
  exact ⟨_, rfl, rfl, rfl, Option.some.inj hu⟩

theorem lastStore_next_pc (r : Fin 4) :
    (Site.store r 7).pc + 1 = (afterStore r 7).pc := by
  fin_cases r <;> rfl

theorem lastStore_live (r : Fin 4) :
    ∀ reg ∈ (Flow.live (afterStore r 7).pc).filter tracked.contains,
      reg ∈ (Flow.live (Site.store r 7).pc).filter tracked.contains := by
  have hc : ((Flow.live (afterStore r 7).pc).filter tracked.contains).all
      (fun reg => ((Flow.live (Site.store r 7).pc).filter tracked.contains).contains reg) =
        true := by
    fin_cases r <;> decide +kernel
  simpa using List.all_eq_true.mp hc

/-- The last store of a row falls straight through to the next row's scales or the proxy fence. -/
theorem stepAt_store_last {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4}
    (hd : d.site = .store r 7) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (tileStore r 7)⟩ := by
      rw [hd]
      exact tileStore_code r 7
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, he, ha, hsize, rfl⟩ := fires_tileStore_payload hpre hd hat hinv hf
    rw [he]
    let d' := { d with site := afterStore r 7, raw := 0, nxt := 0 }
    have hq : d'.site ≠ .qUtccp := by
      change afterStore r 7 ≠ .qUtccp
      fin_cases r <;> decide +kernel
    have hpayload : PayloadOk d' := by fin_cases r <;> trivial
    have hnew : Inv P L g d' :=
      ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
        hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
        fun h => absurd h hq, hinv.lenLt, hinv.batch, hpayload⟩
    have hnoth : ∀ r' j, d.site ≠ .scale r' j := by
      intro r' j heq
      rw [hd] at heq
      cases heq
    have ht := (at_of_atD hat hnoth).next
    have hval : valueOf P L g d' = valueOf P L g d := by
      funext reg
      fin_cases r <;> simp [d', afterStore, valueOf, table, hd]
    have hregs : Holds (PTX.next t).regs (atFacts P L g d' d'.site.pc) := by
      apply holds_of_pointwise
      intro reg hmem
      rw [hval]
      apply holds_mem ht.2.2.2.2
      rw [baseFacts, hd]
      exact mem_factsFrom (lastStore_live r reg hmem)
    have hpc : d.site.pc + 1 = d'.site.pc := by rw [hd, lastStore_next_pc]
    have hready : At (PTX.next t) d'.site.pc (atFacts P L g d' d'.site.pc) :=
      (hpc ▸ ht).mono hregs
    refine Or.inl (Or.inr ⟨d', PTX.next t, ?_, .refl, ?_⟩)
    · simp [next, nextSite, hd, ha, hsize, d']
    · change AtD P L g d' (PTX.next t) ∧ Inv P L g d'
      exact ⟨AtD.of_facts (d := d') rfl
        (by fin_cases r <;> rfl) (by fin_cases r <;> rfl) hready (by fin_cases r <;> rfl), hnew⟩

/-- A word prefetched before the store becomes the next chunk's current word. -/
def storeLoopState (d : D) (r : Fin 4) (s : Fin 8) : D :=
  { d with site := afterStore r s, raw := d.nxt }

def storeUnpackFacts (P : Params) (L : Launch) (g : Nat) (d : D) (r : Fin 4) (s : Fin 8) :
    List (Nat × Value) :=
  (rawLoadReg r (s.val + 1), b64 d.raw) ::
    (scaleByteFacts r d ++ atFacts P L g d (Site.store r s).pc)

theorem afterStore_facts {d : D} {r : Fin 4} {s : Fin 8} {t : TState} (hs : s.val + 1 < 8)
    (hd : d.site = .store r s) (hat : AtD P L g d t) :
    At (PTX.next t) ((Site.store r s).pc + 1)
      (storeUnpackFacts P L g (storeLoopState d r s) r s) := by
  let d' := storeLoopState d r s
  have hpayload : Holds t.regs (storePayload L g r s d) := by
    simpa [payloadFacts, hd] using hat.payloadRegs
  have hsc : Holds t.regs ((rawLoadReg r (s.val + 1), b64 d.nxt) :: scaleByteFacts r d) := by
    rw [storePayload, ite_eq_left hs] at hpayload
    exact hpayload.2.2
  have hent : At t (Site.store r s).pc (baseFacts P L g d) := by
    have hns : ∀ r' j, d.site ≠ .scale r' j := by
      intro r' j he
      rw [hd] at he
      cases he
    simpa only [hd] using at_of_atD hat hns
  have hv : valueOf P L g d' = valueOf P L g d := by
    funext reg
    unfold d' storeLoopState afterStore
    split_ifs <;> simp [valueOf, table, hd]
  have hb : Holds t.regs (atFacts P L g d' (Site.store r s).pc) := by
    rw [atFacts, hv]
    simpa only [baseFacts, hd] using hat.baseRegs
  refine hent.next.mono ?_
  change Holds t.regs ((rawLoadReg r (s.val + 1), b64 d.nxt) ::
    (scaleByteFacts r d ++ atFacts P L g d' (Site.store r s).pc))
  exact ⟨hsc.1, (holds_append _ _ _).mpr ⟨hsc.2, hb⟩⟩

theorem afterStore_raw {r : Fin 4} {s : Fin 8} (hs : s.val + 2 < 8) :
    afterStore r s = .raw r ⟨s.val + 2, hs⟩ := by simp [afterStore, hs]

set_option maxHeartbeats 1500000 in
/-- Between a shared store and the following raw load, split the prefetched input word. -/
theorem storeUnpackToRaw {d : D} (r : Fin 4) (s : Fin 8) (hs : s.val + 2 < 8) (hw : d.raw < 2 ^ 64)
    :
    Seg kernel asms L g 7 ((Site.store r s).pc + 1) (storeUnpackFacts P L g d r s)
      (afterStore r s).pc
      (scaleByteFacts r d ++ rawPairFacts r (s.val + 1) d.raw ++
        atFacts P L g d (afterStore r s).pc) := by
  intro u h
  fin_cases r <;> fin_cases s
  all_goals norm_num at hs
  all_goals simp only [storeUnpackFacts] at h
  all_goals raw_pair_facts h
  all_goals seg_fp h using norm_bits [hw]

/-- Each nonfinal store with a subsequent raw load continues after unpacking its prefetched word. -/
theorem stepAt_store_mid {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4} {s : Fin 8}
    (hd : d.site = .store r s) (hs : s.val + 2 < 8) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (tileStore r s)⟩ := by
      rw [hd]
      exact tileStore_code r s
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, he, ha, hsize, rfl⟩ := fires_tileStore_payload hpre hd hat hinv hf
    rw [he]
    let d' := storeLoopState d r s
    have h1 : s.val + 1 < 8 := by omega
    have hpref := hinv.payloadOk
    rw [PayloadOk, hd] at hpref
    have hw : RawWordOk d'.raw := hpref.2.2 h1
    have hstart := afterStore_facts h1 hd hat
    obtain ⟨t', hr, ht⟩ := storeUnpackToRaw r s hs hw.1 _ hstart
    have hsite : d'.site = .raw r ⟨s.val + 2, hs⟩ := afterStore_raw hs
    have hq : d'.site ≠ .qUtccp := by rw [hsite]; intro he; cases he
    have hpayload : PayloadOk d' := by
      rw [PayloadOk, hsite]
      exact ⟨hpref.1, fun _ => hw⟩
    have hnew : Inv P L g d' :=
      ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
        hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
        fun h => absurd h hq, hinv.lenLt, hinv.batch, hpayload⟩
    have hfin : At t' d'.site.pc (payloadFacts L g d' ++ atFacts P L g d' d'.site.pc) := by
      change At t' d'.site.pc
        (scaleByteFacts r d' ++ rawPairFacts r (s.val + 1) d'.raw ++
          atFacts P L g d' d'.site.pc) at ht
      have he : s.val + 2 - 1 = s.val + 1 := by omega
      have hn : s.val + 2 ≠ 0 := by omega
      simpa only [payloadFacts, hsite, Fin.val_mk, ite_eq_right hn, he] using ht
    refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, ?_⟩)
    · simp [next, nextSite, hd, ha, hsize, h1, d', storeLoopState]
    · change AtD P L g d' t' ∧ Inv P L g d'
      exact ⟨AtD.of_all_facts (d := d') rfl (by rw [hsite]; rfl)
        (by rw [accAt, hsite]) hfin, hnew⟩

def lastComputeFacts (P : Params) (L : Launch) (g : Nat) (d : D) (r : Fin 4) :
    List (Nat × Value) :=
  scaleByteFacts r d ++ (rawPairFacts r 7 d.raw ++ atFacts P L g d (Site.store r 6).pc)

/-- The penultimate store is followed by a seven-instruction unpack of its prefetched word. -/
theorem storeUnpackLast {d : D} (r : Fin 4) (hw : d.raw < 2 ^ 64) :
    Seg kernel asms L g 7 ((Site.store r 6).pc + 1) (storeUnpackFacts P L g d r 6)
      (dequantStart r 7) (lastComputeFacts P L g d r) := by
  intro t h
  fin_cases r
  all_goals simp only [storeUnpackFacts] at h
  all_goals simp only [lastComputeFacts]
  all_goals raw_pair_facts h
  all_goals seg_fp h using norm_bits [hw]

theorem storeLastCompute_live (r : Fin 4) :
    let regs := (Flow.live (Site.store r 6).pc).filter tracked.contains
    134 ∈ regs ∧ 2472 ∈ regs := by
  fin_cases r <;> decide +kernel

theorem storeLast_remaining_live (r : Fin 4) :
    ∀ reg ∈ (Flow.live (Site.store r 7).pc).filter tracked.contains,
      reg ∈ (Flow.live (Site.store r 6).pc).filter tracked.contains := by
  have hc : ((Flow.live (Site.store r 7).pc).filter tracked.contains).all
      (fun reg => ((Flow.live (Site.store r 6).pc).filter tracked.contains).contains reg) =
        true := by
    fin_cases r <;> decide +kernel
  simpa using List.all_eq_true.mp hc

theorem lastComputeFacts_mem {d : D} {r : Fin 4} {reg : Nat}
    (h : reg ∈ (Flow.live (Site.store r 6).pc).filter tracked.contains) :
    (reg, valueOf P L g d reg) ∈ lastComputeFacts P L g d r :=
  List.mem_append_right _ (List.mem_append_right _ (mem_factsFrom h))

theorem lastComputeFacts_preserved {d : D} (r : Fin 4) :
    ∀ p ∈ lastComputeFacts P L g d r, p.1 ∉ chunkWrites r 7 := by
  let keys := (List.range 16).map (fun j => 353 + 24 * r.val + j) ++
    ((List.range 4).map (fun j => 192 + 40 * r.val + 35 + j) ++ tracked)
  have hk : keys.all (fun k => !(chunkWrites r 7).contains k) = true := by
    fin_cases r <;> decide +kernel
  intro p hp
  have he : p.1 ∈ keys := by
    simp only [lastComputeFacts, List.mem_append] at hp
    rcases hp with hp | hp | hp
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      exact List.mem_append_left _ (List.mem_map_of_mem hj)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hj))
    · obtain ⟨k, h, rfl⟩ := List.mem_map.mp hp
      exact List.mem_append_right _ (List.mem_append_right _
        (List.contains_iff_mem.mp (List.mem_filter.mp h).2))
  simpa using List.all_eq_true.mp hk p.1 he

theorem lastCompute_scaleMem {d : D} {r : Fin 4} (i : Fin 16) :
    (353 + 24 * r.val + scaleByteRegIndex i.val, bits16 (byteAt d.sc i.val)) ∈
      lastComputeFacts P L g d r := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨scaleByteRegIndex i.val, List.mem_range.mpr (scaleByteRegIndex_lt i.val), ?_⟩
  have he := scaleRegByte_eq d.sc i
  dsimp only at he
  simp only [scaleWord, bits16, he]

theorem lastCompute_pairMem {d : D} {r : Fin 4} (j : Fin 4) :
    (rawPairReg r 7 j, bits16 (d.raw / 2 ^ (16 * j.val) % 2 ^ 16)) ∈
      lastComputeFacts P L g d r := by
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
  have he : 192 + 40 * r.val + 5 * (7 : Nat) + j.val = rawPairReg r 7 j := by
    unfold rawPairReg scaleDupReg chunkIndex
    omega
  simp [bits16, he]

/-- The last computation starts from the previously loaded word, so it needs no new raw read. -/
theorem run_storeLastCompute {mem0 : Mem0} {d : D} {r : Fin 4} {t : TState} (hpre : Pre P L mem0)
    (hinv : Inv P L g d) (hw : RawWordOk d.nxt) (hsc : ScaleWordOk d.sc)
    (h : At t (dequantStart r 7) (lastComputeFacts P L g (storeLoopState d r 6) r)) :
    let d' := storeLoopState d r 6
    ∃ u, run kernel asms L g 15 t = some u ∧
      At u (Site.store r 7).pc
        (storePayload L g r 7 d' ++ atFacts P L g d' (Site.store r 7).pc) := by
  let d' := storeLoopState d r 6
  let F := lastComputeFacts P L g d' r
  let pick := decide (groupSize / 2 ≤ idxInGroup L g)
  let base := L.sharedBase + (tileBase d.buf + dstOff L g)
  have hp : t.regs 134 = some (.pred pick) := by
    have hm := holds_mem h.2.2.2.2 (lastComputeFacts_mem (storeLastCompute_live r).1)
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, pick] using hm
  have h0 : t.regs (367 + 24 * r.val - 2 * (7 : Fin 8).val) =
      some (bits16 (byteAt d'.sc 14)) := by
    have hm := holds_mem h.2.2.2.2 (lastCompute_scaleMem 14)
    change t.regs (353 + 24 * r.val + scaleByteRegIndex (2 * (7 : Fin 8).val)) =
      some (bits16 (byteAt d'.sc 14)) at hm
    rwa [(scaleReg_ids r 7).1] at hm
  have h1 : t.regs (368 + 24 * r.val - 2 * (7 : Fin 8).val) =
      some (bits16 (byteAt d'.sc 15)) := by
    have hm := holds_mem h.2.2.2.2 (lastCompute_scaleMem 15)
    change t.regs (353 + 24 * r.val + scaleByteRegIndex (2 * (7 : Fin 8).val + 1)) =
      some (bits16 (byteAt d'.sc 15)) at hm
    rwa [(scaleReg_ids r 7).2] at hm
  have hselect : (if pick then byteAt d'.sc 15 else byteAt d'.sc 14) =
      byteAt d'.sc (scaleIdx L g 7) := by
    by_cases hpick : groupSize / 2 ≤ idxInGroup L g <;> simp [pick, scaleIdx, hpick]
  have hscale : (if pick then byteAt d'.sc 15 else byteAt d'.sc 14) < 255 := by
    rw [hselect]
    exact hsc ⟨scaleIdx L g 7, scaleIdx_lt (by decide)⟩
  have hbase : (2472, b32 base) ∈ F := by
    have hm := lastComputeFacts_mem (P := P) (L := L) (g := g) (d := d')
      (storeLastCompute_live r).2
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, F, sb, base, d', storeLoopState]
      using hm
  have haeq : base + tileChunkDelta r 7 =
      L.sharedBase + (tileBase d.buf + tileOff L g r.val 7) := by
    simp [base, tileChunkDelta, tileOff, numGroups, topkBlock, Nat.add_assoc]
  have hfit : base + tileChunkDelta r 7 < 2 ^ 32 := by
    rw [haeq, ← Nat.add_assoc]
    exact sharedTile_lt hpre hinv r 7
  obtain ⟨u, hrun, hout⟩ := run_chunkCompute h hp h1 h0 hscale lastCompute_pairMem hw hbase
    (fun he => by cases he) hfit (lastComputeFacts_preserved r)
  rw [hselect, haeq] at hout
  refine ⟨u, hrun, hout.mono ?_⟩
  have hF : Holds u.regs F := hout.2.2.2.2.2.2
  have hregs : Holds u.regs (atFacts P L g d' (Site.store r 7).pc) := by
    apply holds_of_pointwise
    intro reg hmem
    exact holds_mem hF (lastComputeFacts_mem (storeLast_remaining_live r reg hmem))
  have hs : Holds u.regs (scaleByteFacts r d') := ((holds_append _ _ _).mp hF).1
  refine ⟨hout.2.2.2.2.1, hout.2.2.2.2.2.1, ?_⟩
  exact (holds_append _ _ _).mpr ⟨hs, hregs⟩

/-- Store six unpacks the prefetched last word and computes the final store of its row. -/
theorem stepAt_store_penultimate {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4}
    (hd : d.site = .store r 6) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (tileStore r 6)⟩ := by
      rw [hd]
      exact tileStore_code r 6
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨ac, he, ha, hsize, rfl⟩ := fires_tileStore_payload hpre hd hat hinv hf
    rw [he]
    let d' := storeLoopState d r 6
    have hpay := hinv.payloadOk
    rw [PayloadOk, hd] at hpay
    have hw : RawWordOk d.nxt := hpay.2.2 (by decide)
    have start := afterStore_facts (by decide) hd hat
    obtain ⟨u1, hr1, h1⟩ := storeUnpackLast (d := d') r hw.1 _ start
    obtain ⟨u2, hr2, h2⟩ := run_storeLastCompute hpre hinv hw hpay.1 h1
    have hnew : Inv P L g d' :=
      ⟨hinv.bufLt, hinv.parLt, hinv.bufBlock, hinv.parBlock, hinv.len0, hinv.len1, hinv.block,
        hinv.extra, hinv.groupLt, hinv.idxLt, hinv.rawFit, hinv.scaleFit, hinv.tileFit,
        (by intro h; cases h), hinv.lenLt, hinv.batch, ⟨hpay.1, hw, by simp⟩⟩
    refine Or.inl (Or.inr ⟨d', u2, ?_, run_rtg (run_comp hr1 hr2), ?_⟩)
    · simp [next, nextSite, hd, ha, hsize, d', storeLoopState]
    · change AtD P L g d' u2 ∧ Inv P L g d'
      exact ⟨AtD.of_all_facts (d := d') rfl rfl rfl h2, hnew⟩

theorem stepAt_store {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {r : Fin 4} {s : Fin 8}
    (hd : d.site = .store r s) :
    (code P L g).StepAt d := by
  by_cases hs : s.val + 2 < 8
  · exact stepAt_store_mid hpre d hd hs
  · have he : s = 6 ∨ s = 7 := by
      have hl := s.isLt
      rcases show s.val = 6 ∨ s.val = 7 by omega with h | h
      · exact Or.inl (Fin.eq_of_val_eq h)
      · exact Or.inr (Fin.eq_of_val_eq h)
    rcases he with he | he
    · exact stepAt_store_penultimate hpre d (he ▸ hd)
    · exact stepAt_store_last hpre d (he ▸ hd)

end

/-- The two ring bases at the two slots, at their concrete byte offsets. -/
theorem rawBase_zero : rawBase 0 = 131072 := rfl

theorem rawBase_one : rawBase 1 = 167936 := rfl

theorem tileBase_zero : tileBase 0 = 0 := rfl

theorem tileBase_one : tileBase 1 = 65536 := rfl

/-- The group's first raw row starts at `576 * group_idx` bytes. -/
theorem rawRowOff_zero (L : Launch) (g : Nat) :
    rawRowOff L g 0 = 576 * groupIdx L g := by
  show rawRowStride * rawRow L g 0 = 576 * groupIdx L g
  unfold rawRowStride rawRow numGroups
  rw [Nat.zero_mul, Nat.zero_add]

/-- The selected raw base word of a `buf = 0` state: the `selp` of pcs 2689-2690. -/
theorem addr_sel_zero {L : Launch} {b : Nat} (hb : b = 0)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)) +
      truncBits 32 (BitVec.ofInt 64 131072))) = sb L (rawBase b) := by
  subst hb
  exact addr_eq (x := L.sharedBase) (c := 131072) (off := L.sharedBase + rawBase 0)
    (by rfl) (by omega) (by omega)

/-- The selected raw base word of a `buf = 1` state. -/
theorem addr_sel_one {L : Launch} {b : Nat} (hb : b = 1)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)) +
      truncBits 32 (BitVec.ofInt 64 167936))) = sb L (rawBase b) := by
  subst hb
  exact addr_eq (x := L.sharedBase) (c := 167936) (off := L.sharedBase + rawBase 1)
    (by rfl) (by omega) (by omega)

/-- The second tile base word: the `add.s32` of pc 2691. -/
theorem addr_tileBase_one {L : Launch} {b : Nat} (hb : b = 1)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)) +
      truncBits 32 (BitVec.ofInt 64 65536))) = sb L (tileBase b) := by
  subst hb
  exact addr_eq (x := L.sharedBase) (c := 65536) (off := L.sharedBase + tileBase 1)
    (by rfl) (by omega) (by omega)

/-- The first raw base word: the `add.s32` of pc 2688. -/
theorem addr_rawBase_one {L : Launch} {b : Nat} (hb : b = 1)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)) +
      truncBits 32 (BitVec.ofInt 64 167936))) = sb L (rawBase b) :=
  addr_sel_one hb hsb

/-- The second raw base word: the `add.s32` of pc 2689. -/
theorem addr_rawBase_zero {L : Launch} {b : Nat} (hb : b = 0)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)) +
      truncBits 32 (BitVec.ofInt 64 131072))) = sb L (rawBase b) :=
  addr_sel_zero hb hsb

/-- The tile chunk address word of a `buf = 0` state. -/
theorem addr_tile_zero {L : Launch} {b x : Nat} (hb : b = 0)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) (hx : x < 65536) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) +
      truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 0)))) =
      sb L (tileBase b + x) := by
  subst hb
  rw [tileBase_zero, Nat.zero_add, show L.sharedBase + 0 = L.sharedBase from rfl]
  rw [trunc32_add_word (a := x) (b := L.sharedBase) (by omega) (by omega)]
  show Value.bits 32 (BitVec.ofNat 64 (x + L.sharedBase)) =
    Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + x))
  rw [Nat.add_comm]

/-- The tile chunk address word of a `buf = 1` state. -/
theorem addr_tile_one {L : Launch} {b x : Nat} (hb : b = 1)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) (hx : x < 65536) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) +
      truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 65536)))) =
      sb L (tileBase b + x) := by
  subst hb
  rw [tileBase_one]
  rw [trunc32_add_word (a := x) (b := L.sharedBase + 65536)
    (by omega) (by rw [← Nat.add_assoc]; omega)]
  show Value.bits 32 (BitVec.ofNat 64 (x + (L.sharedBase + 65536))) =
    Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + (65536 + x)))
  rw [show x + (L.sharedBase + 65536) = L.sharedBase + (65536 + x) by ac_rfl]

/-- The raw-row address word of a `buf = 0` state. -/
theorem addr_raw_zero {L : Launch} {g b : Nat} (hb : b = 0)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) (hg : groupIdx L g < numGroups) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 131072)) +
      truncBits 32 (BitVec.ofNat 64 (groupIdx L g * rawRowStride)))) =
      sb L (rawBase b + rawRowOff L g 0) := by
  subst hb
  rw [rawBase_zero, rawRowOff_zero]
  rw [trunc32_add_word (a := L.sharedBase + 131072) (b := groupIdx L g * rawRowStride)
    (by unfold rawRowStride numGroups at *; omega)
    (by unfold rawRowStride numGroups at *; omega)]
  show Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + 131072 +
      groupIdx L g * rawRowStride)) =
    Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + (131072 + 576 * groupIdx L g)))
  rw [show L.sharedBase + 131072 + groupIdx L g * rawRowStride =
    L.sharedBase + (131072 + 576 * groupIdx L g) by
    have h : groupIdx L g * rawRowStride = 576 * groupIdx L g := by
      unfold rawRowStride; rw [Nat.mul_comm]
    omega]

/-- The raw-row address word of a `buf = 1` state. -/
theorem addr_raw_one {L : Launch} {g b : Nat} (hb : b = 1)
    (hsb : L.sharedBase + 222952 < 2 ^ 32) (hg : groupIdx L g < numGroups) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (L.sharedBase + 167936)) +
      truncBits 32 (BitVec.ofNat 64 (groupIdx L g * rawRowStride)))) =
      sb L (rawBase b + rawRowOff L g 0) := by
  subst hb
  rw [rawBase_one, rawRowOff_zero]
  rw [trunc32_add_word (a := L.sharedBase + 167936) (b := groupIdx L g * rawRowStride)
    (by unfold rawRowStride numGroups at *; omega)
    (by unfold rawRowStride numGroups at *; omega)]
  show Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + 167936 +
      groupIdx L g * rawRowStride)) =
    Value.bits 32 (BitVec.ofNat 64 (L.sharedBase + (167936 + 576 * groupIdx L g)))
  rw [show L.sharedBase + 167936 + groupIdx L g * rawRowStride =
    L.sharedBase + (167936 + 576 * groupIdx L g) by
    have h : groupIdx L g * rawRowStride = 576 * groupIdx L g := by
      unfold rawRowStride; rw [Nat.mul_comm]
    omega]

variable {P : Params} {L : Launch} {g : Nat}

/-- **The `bar_raw_ready` wait's step**: the poll of pc 2677 at the ring slot's parity, whose
`true` arm forms the `bar_sv_done` address and parity and reaches the second wait (pc 2684), and
whose `false` arm retries. -/
theorem step_rawReady {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .rawReady)
    {t u : TState} {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 2677 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_14)
  rw [hpc] at hf
  have hbase : t.regs 2458 = some (sb L (rawReadyOff d.buf)) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hpar : t.regs 2459 = some (b32 d.par) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + rawReadyOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    unfold rawReadyOff
    have h2 := hinv.bufLt
    omega
  have hm : mbarLoc L g t 2458 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + rawReadyOff d.buf⟩ :=
    mbarLoc_b32 hbase hb (sharedAddr_align hpre (by unfold rawReadyOff; omega))
  have hq : readBits L g t 32 (.reg 2459) = .ok (BitVec.ofNat 64 d.par) :=
    readBits_b32 hpar (by have := hinv.parLt; omega)
  obtain ⟨ok, acq', sc', he, hu⟩ := fires_wait_at_succ (A := asms) (t := t)
    (p := 4125) (base := 2458) (off := 0) (par := .reg 2459) (acq := true) (sc := .cta)
    (m := ⟨.shared, g / L.block, L.sharedBase + rawReadyOff d.buf⟩)
    (q := BitVec.ofNat 64 d.par) (pc := 2677) (e := e) (u := u) hm hq hf
  have hok : ok = false ∨ ok = true := by
    rcases Bool.eq_false_or_eq_true ok with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hok with hok | hok
  · rw [hok] at he hu
    have h0 : At u 2678 ((4125, .pred false) ::
        factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4125) (pc := 2677) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2677 (factsFrom ((Flow.live 2677).filter (fun r =>
          tracked.contains r)) (valueOf P L g d)) := by
      seg_fp h0 using
        try wg2_values
        all_goals wg2_close []
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr,
      (AtD.of_facts (d := d) (pc := 2677) (hpc := by rw [hd]; rfl) (hsub := by simp [Site.sub, hd])
          (hacc := by simp [accAt, hd]) ht (by simp [payloadFacts, hd])), hinv⟩)
    rw [next, he, hd]
    rfl
  · rw [hok] at he hu
    have h0 : At u 2678 ((4125, .pred true) ::
        factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4125) (pc := 2677) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    have hw : Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64
        (L.sharedBase + 8 * d.buf)) + truncBits 32 (BitVec.ofInt 64 222936))) =
        sb L (svDoneOff d.buf) := by
      show Value.bits 32 _ = b32 (L.sharedBase + svDoneOff d.buf)
      exact addr_eq (by simp only [svDoneOff]; omega) (by omega) (by
        have h2 : d.buf < 2 := hinv.bufLt
        have hb8 : 8 * d.buf ≤ 8 := by
          have h := Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ h2)
          simpa using h
        have hsum : L.sharedBase + 8 * d.buf + 222936 ≤ L.sharedBase + 222952 := by
          omega
        exact lt_of_le_of_lt hsum (sharedBase_lt hpre))
    have hp2 : d.par = 0 ∨ d.par = 1 := by have := hinv.parLt; omega
    rcases hp2 with hp | hp
    · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 5 u = some t' ∧
          At t' 2684 (factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
            (valueOf P L g { d with site := .svDone })) := by
        seg_fp h0 using
          try wg2_values
          all_goals first | wg2_close [hp] | exact hw
      refine Or.inl (Or.inr ⟨{ d with site := .svDone }, t', ?_, run_rtg hr,
        (AtD.of_facts (d := { d with site := .svDone }) (pc := 2684) rfl rfl
          (by simp [accAt]) ht),
        inv_setSite hinv .svDone (by decide)⟩)
      rw [next, he, hd]
      rfl
    · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 5 u = some t' ∧
          At t' 2684 (factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
            (valueOf P L g { d with site := .svDone })) := by
        seg_fp h0 using
          try wg2_values
          all_goals first | wg2_close [hp] | exact hw
      refine Or.inl (Or.inr ⟨{ d with site := .svDone }, t', ?_, run_rtg hr,
        (AtD.of_facts (d := { d with site := .svDone }) (pc := 2684) rfl rfl
          (by simp [accAt]) ht),
        inv_setSite hinv .svDone (by decide)⟩)
      rw [next, he, hd]
      rfl

/-! ## The `bar_sv_done` wait's pass

The second wait's `true` arm (pcs 2685-2694) skips the poll's retry branch, tests the ring slot
with `setp.eq` and forms the slot's raw and tile base words with one `add.s32` each plus a
`selp`, then adds the thread's row and chunk offsets. The `setp` and the two `selp`s read
predicate register `%p135`, which the role does not track, and every state below is a state of
one literal ring slot: the pass is stated per slot and carries `(135, .pred …)` as an explicit
fact. Each instruction is its own segment: the value equations of two or more of them together
exceed `seg_fp`'s recursion and heartbeat budgets, and the one-instruction checkpoints keep every
written word a table value. -/

/-- **The `bar_sv_done` pass of a `buf = 0` state**: from the poll's continuation (pc 2685) the
nine local instructions to the first scale load (pc 2695). Slot 0 selects the first raw block
and the first tile, so `%p135` is true and the second `selp` picks `%r2787`, the bare shared
base. -/
theorem seg_svDone_zero {d : D} {u : TState} (hsb : L.sharedBase + 222952 < 2 ^ 32) (hb : d.buf = 0)
    (h0 : At u 2685 ((4126, .pred true) ::
      factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 9 u = some t' ∧
      At t' 2695 (factsFrom ((Flow.live 2695).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })) := by
  rcases d with ⟨dsite, dblock, dbuf, dpar, dextra, dlen0, dlen1, draw, dnxt, dsc⟩
  subst hb
  let d : D := ⟨dsite, dblock, 0, dpar, dextra, dlen0, dlen1, draw, dnxt, dsc⟩
  obtain ⟨t₁, hr₁, h₁⟩ : ∃ t₁, run kernel asms L g 1 u = some t₁ ∧
      At t₁ 2687 (factsFrom ((Flow.live 2687).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h0 using
      try wg2_values
      all_goals wg2_close []
  obtain ⟨t₂, hr₂, h₂⟩ : ∃ t₂, run kernel asms L g 1 t₁ = some t₂ ∧
      At t₂ 2688 ((135, .pred true) ::
        factsFrom ((Flow.live 2688).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₁ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₃, hr₃, h₃⟩ : ∃ t₃, run kernel asms L g 1 t₂ = some t₃ ∧
      At t₃ 2689 ((135, .pred true) ::
        factsFrom ((Flow.live 2689).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₂ using
      try wg2_values
      all_goals first | exact addr_rawBase_one (b := 1) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₄, hr₄, h₄⟩ : ∃ t₄, run kernel asms L g 1 t₃ = some t₄ ∧
      At t₄ 2690 ((135, .pred true) ::
        factsFrom ((Flow.live 2690).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₃ using
      try wg2_values
      all_goals first | exact addr_rawBase_zero (b := 0) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₅, hr₅, h₅⟩ : ∃ t₅, run kernel asms L g 1 t₄ = some t₅ ∧
      At t₅ 2691 ((135, .pred true) ::
        factsFrom ((Flow.live 2691).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₄ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₆, hr₆, h₆⟩ : ∃ t₆, run kernel asms L g 1 t₅ = some t₆ ∧
      At t₆ 2692 ((135, .pred true) ::
        factsFrom ((Flow.live 2692).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₅ using
      try wg2_values
      all_goals first | exact addr_tileBase_one (b := 1) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₇, hr₇, h₇⟩ : ∃ t₇, run kernel asms L g 1 t₆ = some t₇ ∧
      At t₇ 2693 (factsFrom ((Flow.live 2693).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₆ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₈, hr₈, h₈⟩ : ∃ t₈, run kernel asms L g 1 t₇ = some t₈ ∧
      At t₈ 2694 (factsFrom ((Flow.live 2694).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₇ using
      try wg2_values
      all_goals first | exact addr_tile_zero (b := 0) rfl hsb (dstOff_lt L g) | wg2_close []
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 t₈ = some t' ∧
      At t' 2695 (factsFrom ((Flow.live 2695).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })) := by
    seg_fp h₈ using
      try wg2_values
      all_goals first | exact addr_raw_zero (b := 0) rfl hsb (groupLt L g) | wg2_close []
  exact ⟨t', by simpa using run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅) hr₆) hr₇) hr₈) hr, ht⟩

/-- **The `bar_sv_done` pass of a `buf = 1` state**: the same ring arithmetic with slot 1
selecting the second raw block and the second tile, so `%p135` is false and the second `selp`
picks `%r2794`, the second tile's base. -/
theorem seg_svDone_one {d : D} {u : TState} (hsb : L.sharedBase + 222952 < 2 ^ 32) (hb : d.buf = 1)
    (h0 : At u 2685 ((4126, .pred true) ::
      factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 9 u = some t' ∧
      At t' 2695 (factsFrom ((Flow.live 2695).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })) := by
  rcases d with ⟨dsite, dblock, dbuf, dpar, dextra, dlen0, dlen1, draw, dnxt, dsc⟩
  subst hb
  let d : D := ⟨dsite, dblock, 1, dpar, dextra, dlen0, dlen1, draw, dnxt, dsc⟩
  obtain ⟨t₁, hr₁, h₁⟩ : ∃ t₁, run kernel asms L g 1 u = some t₁ ∧
      At t₁ 2687 (factsFrom ((Flow.live 2687).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h0 using
      try wg2_values
      all_goals wg2_close []
  obtain ⟨t₂, hr₂, h₂⟩ : ∃ t₂, run kernel asms L g 1 t₁ = some t₂ ∧
      At t₂ 2688 ((135, .pred false) ::
        factsFrom ((Flow.live 2688).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₁ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₃, hr₃, h₃⟩ : ∃ t₃, run kernel asms L g 1 t₂ = some t₃ ∧
      At t₃ 2689 ((135, .pred false) ::
        factsFrom ((Flow.live 2689).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₂ using
      try wg2_values
      all_goals first | exact addr_rawBase_one (b := 1) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₄, hr₄, h₄⟩ : ∃ t₄, run kernel asms L g 1 t₃ = some t₄ ∧
      At t₄ 2690 ((135, .pred false) ::
        factsFrom ((Flow.live 2690).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₃ using
      try wg2_values
      all_goals first | exact addr_rawBase_zero (b := 0) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₅, hr₅, h₅⟩ : ∃ t₅, run kernel asms L g 1 t₄ = some t₅ ∧
      At t₅ 2691 ((135, .pred false) ::
        factsFrom ((Flow.live 2691).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₄ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₆, hr₆, h₆⟩ : ∃ t₆, run kernel asms L g 1 t₅ = some t₆ ∧
      At t₆ 2692 ((135, .pred false) ::
        factsFrom ((Flow.live 2692).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h₅ using
      try wg2_values
      all_goals first | exact addr_tileBase_one (b := 1) rfl hsb | exact rfl | wg2_close []
  obtain ⟨t₇, hr₇, h₇⟩ : ∃ t₇, run kernel asms L g 1 t₆ = some t₇ ∧
      At t₇ 2693 (factsFrom ((Flow.live 2693).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₆ using
      try wg2_values
      all_goals first | exact rfl | wg2_close []
  obtain ⟨t₈, hr₈, h₈⟩ : ∃ t₈, run kernel asms L g 1 t₇ = some t₈ ∧
      At t₈ 2694 (factsFrom ((Flow.live 2694).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₇ using
      try wg2_values
      all_goals first | exact addr_tile_one (b := 1) rfl hsb (dstOff_lt L g) | wg2_close []
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 1 t₈ = some t' ∧
      At t' 2695 (factsFrom ((Flow.live 2695).filter (fun r => tracked.contains r))
        (valueOf P L g { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })) := by
    seg_fp h₈ using
      try wg2_values
      all_goals first | exact addr_raw_one (b := 1) rfl hsb (groupLt L g) | wg2_close []
  exact ⟨t', by simpa using run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅) hr₆) hr₇) hr₈) hr, ht⟩

/-- **The `bar_sv_done` wait's step**: the poll of pc 2684 at the parity `par ^ 1` (the
`bar_sv_done[buf]` phase opposite to `bar_raw_ready[buf]`'s), whose `true` arm forms the ring's
raw and tile address words and reaches the first scale load (pc 2695) and whose `false` arm
retries the poll. -/
theorem step_svDone {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .svDone)
    {t u : TState} {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 2684 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_15)
  rw [hpc] at hf
  have hbase : t.regs 2461 = some (sb L (svDoneOff d.buf)) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hpar : t.regs 2462 = some (b32 (1 - d.par)) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + svDoneOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    unfold svDoneOff
    have h2 := hinv.bufLt
    omega
  have hm : mbarLoc L g t 2461 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + svDoneOff d.buf⟩ :=
    mbarLoc_b32 hbase hb (sharedAddr_align hpre (by unfold svDoneOff; omega))
  have hq : readBits L g t 32 (.reg 2462) = .ok (BitVec.ofNat 64 (1 - d.par)) :=
    readBits_b32 hpar (by have := hinv.parLt; omega)
  obtain ⟨ok, acq', sc', he, hu⟩ := fires_wait_at_succ (A := asms) (t := t)
    (p := 4126) (base := 2461) (off := 0) (par := .reg 2462) (acq := true) (sc := .cta)
    (m := ⟨.shared, g / L.block, L.sharedBase + svDoneOff d.buf⟩)
    (q := BitVec.ofNat 64 (1 - d.par)) (pc := 2684) (e := e) (u := u) hm hq hf
  have hok : ok = false ∨ ok = true := by
    rcases Bool.eq_false_or_eq_true ok with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hok with hok | hok
  · rw [hok] at he hu
    have h0 : At u 2685 ((4126, .pred false) ::
        factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4126) (pc := 2684) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2684 (factsFrom ((Flow.live 2684).filter (fun r =>
          tracked.contains r)) (valueOf P L g d)) := by
      seg_fp h0 using
        try wg2_values
        all_goals wg2_close []
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr,
      (AtD.of_facts (d := d) (pc := 2684) (hpc := by rw [hd]; rfl) (hsub := by simp [Site.sub, hd])
          (hacc := by simp [accAt, hd]) ht (by simp [payloadFacts, hd])), hinv⟩)
    rw [next, he, hd]
    rfl
  · rw [hok] at he hu
    have h0 : At u 2685 ((4126, .pred true) ::
        factsFrom ((Flow.live 2684).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4126) (pc := 2684) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    have hbp : d.buf = 0 ∨ d.buf = 1 := by have := hinv.bufLt; omega
    have hsb := sharedBase_lt hpre
    rcases hbp with hb0 | hb1
    · obtain ⟨t', hr, ht⟩ := seg_svDone_zero (P := P) (L := L) (g := g) (u := u) hsb hb0 h0
      refine Or.inl (Or.inr ⟨{ d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ }, t', ?_,
        run_rtg hr,
        (AtD.of_facts (d := { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })
          (pc := 2695) rfl rfl (by simp [accAt]) ht),
        inv_setSite hinv _ (by decide)⟩)
      rw [next, he, hd]
      rfl
    · obtain ⟨t', hr, ht⟩ := seg_svDone_one (P := P) (L := L) (g := g) (u := u) hsb hb1 h0
      refine Or.inl (Or.inr ⟨{ d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ }, t', ?_,
        run_rtg hr,
        (AtD.of_facts (d := { d with site := .scale ⟨0, by decide⟩ ⟨0, by decide⟩ })
          (pc := 2695) rfl rfl (by simp [accAt]) ht),
        inv_setSite hinv _ (by decide)⟩)
      rw [next, he, hd]
      rfl

/-! ## The `bar_q_utccp` wait's step

The role's first event is the wait on `bar_q_utccp` (pc 2644), which the main loop's body is
entered behind. Both waits before it are complete (`step_rawReady`, `step_svDone`), so this
step has the same shape: the poll's `false` arm retries at pcs 2645-2646 and its `true` arm
runs the 31 local instructions of pcs 2645-2676 to the first body wait (pc 2677).

The `true` arm is the loop's prologue. Pc 2647 tests the padded block count against 64 and pc
2648 skips the loop when it is smaller; `Inv.qUtccpBlock` fixes the state's block at zero, so
`Inv.block` makes the count positive and the branch falls through. Pcs 2649-2662 then rebuild
the dequantizer's position registers from the two launch reads (`%r512 = group_idx`, `%r513 =
idx_in_group`, `%r2988 = buf`): the swizzle's row in the atom, its XOR with the lane, the
`dstOff` sum, the lane and row byte offsets; pcs 2663-2676 reset the parity and the ring slot
to zero and form the first body wait's address and parity. The signed ceiling of pcs
2650-2654 reads the padded count with the same three shifts and the `-64` mask as the length
sites, this time on `padded`, so its arithmetic is the semantic count only while `padded` fits
31 signed bits; `Pre.noSplit` and the row's two length bounds (`Inv.batch` is the row's, so
`topkLen_le` and `extraTopkLen_le` apply) give `padded ≤ 640 + 640`.

The pass is proved one instruction at a time (`seg_qUtccp`). Two of its registers —
`%p133` (the skip test) and the shadow words `%r2785`/`%r2786` — are live but outside the
role's table, so each is carried as an explicit fact of the state it is needed in; a segment
that ends at a branch states its predicate. -/

/-- The row's main-cache runtime length is at most the launch's sparse budget. -/
theorem topkLen_le {P : Params} {L : Launch} {mem0 : Mem0} {e : Nat}
    (hpre : Pre P L mem0) (h : e < P.b) : P.topkLen e ≤ P.topk := by
  have hp := hpre.paramTopkLen
  cases hb : P.topkLenBase with
  | none => rw [hb] at hp; rw [hp.2 e h]
  | some x => rw [hb] at hp; exact ((hp.2.2 e h) 0 (by omega)).2 e h

/-- The row's extra-cache runtime length is at most the launch's sparse budget. -/
theorem extraTopkLen_le {P : Params} {L : Launch} {mem0 : Mem0} {e : Nat}
    (hpre : Pre P L mem0) (h : e < P.b) : P.extraTopkLen e ≤ P.extra_topk := by
  have hp := hpre.paramExtraTopkLen
  cases hb : P.extraTopkLenBase with
  | none => rw [hb] at hp; rw [hp.2 e h]
  | some x => rw [hb] at hp; exact ((hp.2.2 e h) 0 (by omega)).2 e h

/-- The `and` with the three-bit mask `7`. -/
theorem land7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

/-- An `and` with a mask below `2 ^ n` of a sum whose high part is a multiple of `2 ^ n`. -/
theorem and_add_mul_two_pow {a b n m : Nat} (ha : a < 2 ^ n) (hm : m < 2 ^ n) :
    (a + b * 2 ^ n) &&& m = a &&& m := by
  have h1 : (a + b * 2 ^ n) &&& m < 2 ^ n := Nat.and_lt_two_pow _ hm
  rw [← Nat.mod_eq_of_lt h1, Nat.and_mod_two_pow]
  rw [show a + b * 2 ^ n = a + 2 ^ n * b by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm]

/-- **The swizzle's row mask**: `and.b32 %r2454, %r2453, 896` keeps the group's row in the
atom, `row_in_atom * 128` (the mask `896 = 7 * 128` covers the atom's eight 128-byte rows). -/
theorem land_896 (x : Nat) : (x * 128) &&& 896 = (x % 8) * 128 := by
  have h1 : x % 8 + 8 * (x / 8) = x := Nat.mod_add_div x 8
  have hpow : (8 : Nat) * (x / 8) * 128 = (x / 8) * 2 ^ 10 := by ring
  have hsplit : x * 128 = (x % 8) * 128 + (x / 8) * 2 ^ 10 := by
    rw [← hpow]; nlinarith
  rw [hsplit, and_add_mul_two_pow (n := 10) (by omega) (by decide)]
  have hb : x % 8 < 8 := Nat.mod_lt x (by decide)
  interval_cases x % 8 <;> decide

/-- **The group's atom index**: `and.b32 %r2456, %r2455, 1024` keeps bit 6 of the thread index,
`group_idx / 8 * 1024` (the high three bits are the `(8 * 128)`-byte atom stride). -/
theorem land_1024 (x : Nat) : (x * 16) &&& 1024 = (x % 128 / 8 / 8) * 1024 := by
  have h1 : x % 128 + 128 * (x / 128) = x := Nat.mod_add_div x 128
  have hpow : (128 : Nat) * (x / 128) * 16 = (x / 128) * 2 ^ 11 := by ring
  have hsplit : x * 16 = (x % 128) * 16 + (x / 128) * 2 ^ 11 := by
    rw [← hpow]; nlinarith
  rw [hsplit, and_add_mul_two_pow (n := 11) (by omega) (by decide)]
  have hb : x % 128 < 128 := Nat.mod_lt x (by decide)
  interval_cases x % 128 <;> decide

/-- The two's complement of a value below `2 ^ 31` read as a 32-bit word: the signed shifts
and comparisons of the pass (`shr.s32`, `setp.lt.s32`). -/
theorem toSigned32_ofNat {n : Nat} (h : n < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int) := by
  have h64 : n < 2 ^ 64 := by omega
  have h32 : n < 2 ^ 32 := by omega
  have h1 : (truncBits 32 (BitVec.ofNat 64 n)).toNat = n := by
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]
  show toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int)
  unfold toSigned
  rw [h1]
  simp only [Nat.mod_eq_of_lt h32, h, ↓reduceIte]

/-- **The sign word**: `shr.s32 %r2447, %r515, 31` is zero for a padded count below `2 ^ 31`
(`ku::ceil`'s correction term). -/
theorem shr31_value {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (BitVec.ofInt 64
          (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) /
            2 ^ min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32))) = b32 0 := by
  have hs : min (truncBits 32 (BitVec.ofInt 64 31)).toNat 32 = 31 := by decide +kernel
  rw [toSigned32_ofNat hn, hs]
  have hd : (n : Int) / 2 ^ 31 = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [hd]
  show Value.bits 32 _ = _
  nf_simp [b32]

/-- **The block count**: `shr.s32 %r2450, %r2449, 6` is the padded count's ceiling in blocks,
`padded / 64` (`ku::ceil`'s shift). -/
theorem shr6_value {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32
      (truncBits 32
        (BitVec.ofInt 64
          (toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) /
            2 ^ min (truncBits 32 (BitVec.ofInt 64 6)).toNat 32))) = b32 (n / 64) := by
  have hs : min (truncBits 32 (BitVec.ofInt 64 6)).toNat 32 = 6 := by decide +kernel
  rw [toSigned32_ofNat hn, hs]
  have hd : (n : Int) / 2 ^ 6 = ((n / 64 : Nat) : Int) := by
    rw [Int.natCast_ediv n 64]
    norm_num
  rw [hd]
  show Value.bits 32 _ = _
  nf_simp [b32]
  omega

/-- **The block counter**: `neg.s32 %r2987, %r2450` is the negated block count, the loop
counter the back edge increments to zero. -/
theorem neg_value {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (-truncBits 32 (BitVec.ofNat 64 n))) = b32 (2 ^ 32 - n) := by
  show Value.bits 32 _ = _
  nf_simp [b32]
  omega

/-- **The skip test**: `setp.lt.s32 %p133, %r515, 64` is false for a padded count of at least
64 (`and.b32 %r2446, %r512, 7` is `row_in_atom`). -/
theorem and7_value {x : Nat} :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 x) &&& truncBits 32 (BitVec.ofInt 64 7)) =
      b32 (x % 8) := by
  show Value.bits 32 _ = _
  nf_simp [b32, land7]
  omega

/-- The swizzle's lane XOR: `xor.b32 %r2451, %r2446, %r513`. -/
theorem xor_value {a b : Nat} (ha : a < 8) (hb : b < 8) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 a) ^^^ truncBits 32 (BitVec.ofNat 64 b)) =
      b32 (a ^^^ b) := by
  have h64a : a < 18446744073709551616 := by omega
  have h64b : b < 18446744073709551616 := by omega
  have h32a : a < 4294967296 := by omega
  have h32b : b < 4294967296 := by omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show a % 4294967296 = a from Nat.mod_eq_of_lt h32a,
    show b % 4294967296 = b from Nat.mod_eq_of_lt h32b, nf_xor,
    show a % 18446744073709551616 = a from Nat.mod_eq_of_lt h64a,
    show b % 18446744073709551616 = b from Nat.mod_eq_of_lt h64b]

/-- An `or` of two words below `2 ^ 31`: the `or.b32` of pcs 2661-2662. -/
theorem or_value {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 a) ||| truncBits 32 (BitVec.ofNat 64 b)) =
      b32 (a ||| b) := by
  have h32a : a < 4294967296 := by omega
  have h32b : b < 4294967296 := by omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show a % 4294967296 = a from Nat.mod_eq_of_lt h32a,
    show b % 4294967296 = b from Nat.mod_eq_of_lt h32b]

/-- **The atom-row mask's value**: `and.b32 %r2454, %r2453, 896` is `row_in_atom * 128`. -/
theorem and896_value {x : Nat} (hx : x < 2 ^ 20) :
    Value.bits 32
      (truncBits 32 (BitVec.ofNat 64 (x * 128)) &&& truncBits 32 (BitVec.ofInt 64 896)) =
      b32 ((x % 8) * 128) := by
  have h32 : x * 128 < 4294967296 := by omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show x * 128 % 4294967296 = x * 128 from Nat.mod_eq_of_lt h32, land_896]

/-- **The atom-index mask's value**: `and.b32 %r2456, %r2455, 1024` is
`group_idx / 8 * 1024`. -/
theorem and1024_value {x : Nat} (hx : x < 2 ^ 26) :
    Value.bits 32
      (truncBits 32 (BitVec.ofNat 64 (x * 16)) &&& truncBits 32 (BitVec.ofInt 64 1024)) =
      b32 ((x % 128 / 8 / 8) * 1024) := by
  have h32 : x * 16 < 4294967296 := by omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show x * 16 % 4294967296 = x * 16 from Nat.mod_eq_of_lt h32, land_1024]

/-- **The group's raw-row stride**: `mul.lo.s32 %r518, %r512, 576` is
`group_idx * RAW_TOKEN_SMEM_STRIDE`. -/
theorem mul576_value {a : Nat} (ha : a < 16) :
    Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) * truncBits 32 (BitVec.ofInt 64 576))) =
      b32 (a * 576) := by
  have h32 : a < 4294967296 := by omega
  have hm : a * 576 < 4294967296 := by omega
  have h64 : a * 576 < 18446744073709551616 := by omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show a % 4294967296 = a from Nat.mod_eq_of_lt h32,
    show a * 576 % 4294967296 = a * 576 from Nat.mod_eq_of_lt hm,
    show a * 576 % 18446744073709551616 = a * 576 from Nat.mod_eq_of_lt h64]

/-- The `dstOff` sum's three disjoint bit regions: the atom row (`a * 128`, bits 7-9), the
atom index (`g8 * 1024`, bits 10 and above) and the swizzle's 16-byte lane (`x * 16`, bits
4-6), composed by the two `or.b32` of pcs 2661-2662. -/
theorem dstOff_or {g8 a x : Nat} (ha : a < 8) (hx : x < 8) :
    ((a * 128) ||| (g8 * 1024)) ||| (x * 16) = g8 * 1024 + a * 128 + x * 16 := by
  have hA : a * 128 < 2 ^ 10 := by omega
  have hC : x * 16 < 2 ^ 7 := by omega
  have hAC : a * 128 + x * 16 < 2 ^ 10 := by omega
  rw [Nat.or_assoc, Nat.or_comm (g8 * 1024) (x * 16), ← Nat.or_assoc]
  have e2 : (a * 128) ||| (x * 16) = a * 128 + x * 16 := by
    rw [show a * 128 = (2 : Nat) ^ 7 * a by ring,
      ← Nat.two_pow_add_eq_or_of_lt (i := 7) (b := x * 16) hC]
  rw [e2]
  rw [show g8 * 1024 = (2 : Nat) ^ 10 * g8 by ring, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (i := 10) (b := a * 128 + x * 16) hAC]
  ring

/-- **The chunk's tile offset**: the two `or.b32` of pcs 2661-2662 give `dstOff`. -/
theorem dstOff_value {g8 a i : Nat} (ha : a < 8) (hi : i < 8) (hg8 : g8 < 2 ^ 21) :
    Value.bits 32
      (truncBits 32 (BitVec.ofNat 64 (a * 128 ||| g8 * 1024)) |||
        truncBits 32 (BitVec.ofNat 64 ((a ^^^ i) * 16))) =
      b32 (g8 * 1024 + a * 128 + (i ^^^ a) * 16) := by
  have hx : a ^^^ i < 8 := xor_lt_eight ha hi
  have h32 : (a ^^^ i) * 16 < 4294967296 := by omega
  have hA : a * 128 ||| g8 * 1024 < 4294967296 := by
    have := Nat.or_lt_two_pow (n := 32) (by omega : a * 128 < 2 ^ 32)
      (by omega : g8 * 1024 < 2 ^ 32)
    omega
  show Value.bits 32 _ = _
  nf_simp [b32]
  rw [show (a * 128 ||| g8 * 1024) % 4294967296 = (a * 128 ||| g8 * 1024) from
      Nat.mod_eq_of_lt hA,
    show (a ^^^ i) * 16 % 4294967296 = (a ^^^ i) * 16 from Nat.mod_eq_of_lt h32,
    dstOff_or (g8 := g8) (x := a ^^^ i) ha hx, Nat.xor_comm i a]

/-- **The skip branch**: `setp.lt.s32 %p133, %r515, 64` is false when the padded count is at
least 64. -/
theorem setp_lt64_false {h : Nat} (hge : 64 ≤ h) (hlt : h < 2 ^ 31) :
    compare Cmp.lt IType.s 32 (truncBits 32 (BitVec.ofNat 64 h))
      (truncBits 32 (BitVec.ofInt 64 64)) = false := by
  have h1 : toSigned 32 (truncBits 32 (BitVec.ofNat 64 h)) = (h : Int) := toSigned32_ofNat hlt
  have h2 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 64)) = (64 : Int) := by
    have e : BitVec.ofInt 64 64 = BitVec.ofNat 64 64 := rfl
    rw [e]; exact toSigned32_ofNat (by norm_num)
  unfold compare
  rw [h1, h2]
  simp only [decide_eq_false_iff_not]
  omega

/-- **The scale-select test**: `setp.gt.u32 %p134, %r513, 3` is
`GROUP_SIZE / 2 <= idx_in_group`, the predicate `%r134` the body's scale loads read. -/
theorem setp_gt3_pred {i : Nat} (hi : i < 8) :
    Value.pred (compare Cmp.gt IType.u 32 (truncBits 32 (BitVec.ofNat 64 i))
      (truncBits 32 (BitVec.ofInt 64 3))) = Value.pred (decide (groupSize / 2 ≤ i)) := by
  have e : groupSize / 2 = 4 := by decide
  rw [e]
  show Value.pred _ = _
  rw [Value.pred.injEq]
  have h1 : (truncBits 32 (BitVec.ofNat 64 i)).toNat = i := by
    simp only [truncBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
  have h2 : (truncBits 32 (BitVec.ofInt 64 3)).toNat = 3 := by decide +kernel
  unfold compare
  simp only [h1, h2]
  rw [decide_eq_decide]
  omega

/-- The `not` of a 64-bit word, in the normal form: `not.b32 %r2789, %r2988`. -/
theorem nf_not (a : Nat) : ~~~(BitVec.ofNat 64 a) =
    BitVec.ofNat 64 (18446744073709551615 - a % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h : 18446744073709551615 - a % 18446744073709551616 < 18446744073709551616 := by
    have := Nat.mod_lt a (by decide : 0 < 18446744073709551616); omega
  rw [Nat.mod_eq_of_lt h]

/-- **The `bar_q_utccp` wait's pass**: from the poll's continuation (pc 2645) the 31 local
instructions to the first body wait (pc 2677). The state is the wait's, so `qUtccpBlock`
fixes its block at zero and the ring slot and parity are zero. -/
theorem seg_qUtccp {d : D} {u : TState} (hsb : L.sharedBase + 222952 < 2 ^ 32) (hblk : d.block = 0)
    (hbuf : d.buf = 0) (hpar : d.par = 0) (hixLt : idxInGroup L g < 8) (hgpLt : groupIdx L g < 16)
    (htLt : tidOf L g < 384)
    (hpadded : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31)
    (hp64 : 64 ≤ origPadded d.len0 + ceilToMultiple d.len1 topkBlock)
    (htotPos : 0 < totalBlocks d.len0 d.len1) (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32)
    (h0 : At u 2645 ((4124, .pred true) ::
      factsFrom ((Flow.live 2644).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 31 u = some t' ∧
      At t' 2677 (factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  have hraLt : rowInAtom L g < 8 := rowInAtom_lt L g
  have hxorLt : rowInAtom L g ^^^ idxInGroup L g < 8 := xor_lt_eight hraLt hixLt
  have hshared : L.sharedBase < 2 ^ 32 := by omega
  have hb8 : L.sharedBase + 8 * d.buf < 2 ^ 32 := by omega
  have hb58 : L.sharedBase + 8 * d.buf + 222808 < 2 ^ 32 := by
    have : 8 * d.buf ≤ 8 := by omega
    omega
  obtain ⟨t₁, hr1, h1⟩ : ∃ t₁, run kernel asms L g 1 u = some t₁ ∧
      At t₁ 2647 (factsFrom ((Flow.live 2647).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h0 using
      try wg2_values
      all_goals wg2_close []
  obtain ⟨t₂, hr2, h2⟩ : ∃ t₂, run kernel asms L g 1 t₁ = some t₂ ∧
      At t₂ 2648 ((133, .pred false) ::
        factsFrom ((Flow.live 2648).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h1 using
      try wg2_values
      all_goals
        first
          | rw [setp_lt64_false hp64 hpadded]
          | wg2_close []
  obtain ⟨t₃, hr3, h3⟩ : ∃ t₃, run kernel asms L g 1 t₂ = some t₃ ∧
      At t₃ 2649 (factsFrom ((Flow.live 2649).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h2 using
      try wg2_values
      all_goals wg2_close []
  obtain ⟨t₄, hr4, h4⟩ : ∃ t₄, run kernel asms L g 1 t₃ = some t₄ ∧
      At t₄ 2650 (factsFrom ((Flow.live 2650).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h3 using
      try wg2_values
      all_goals
        first
          | exact and7_value (x := groupIdx L g)
          | wg2_close []
  obtain ⟨t₅, hr5, h5⟩ : ∃ t₅, run kernel asms L g 1 t₄ = some t₅ ∧
      At t₅ 2651 (factsFrom ((Flow.live 2651).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h4 using
      try wg2_values
      all_goals
        first
          | exact shr31_value hpadded
          | wg2_close []
  obtain ⟨t₆, hr6, h6⟩ : ∃ t₆, run kernel asms L g 2 t₅ = some t₆ ∧
      At t₆ 2653 (factsFrom ((Flow.live 2653).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h5 using
      try wg2_values
      all_goals wg2_close [hpadded]
  obtain ⟨t₇, hr7, h7⟩ : ∃ t₇, run kernel asms L g 1 t₆ = some t₇ ∧
      At t₇ 2654 (factsFrom ((Flow.live 2654).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h6 using
      try wg2_values
      all_goals
        first
          | exact shr6_value hpadded
          | wg2_close []
  obtain ⟨t₈, hr8, h8⟩ : ∃ t₈, run kernel asms L g 1 t₇ = some t₈ ∧
      At t₈ 2655 (factsFrom ((Flow.live 2655).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h7 using
      try wg2_values
      all_goals
        first
          | (rw [hblk, Nat.zero_add]; exact neg_value htotPos htotLt)
          | wg2_close []
  obtain ⟨t₉, hr9, h9⟩ : ∃ t₉, run kernel asms L g 1 t₈ = some t₉ ∧
      At t₉ 2656 (factsFrom ((Flow.live 2656).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h8 using
      try wg2_values
      all_goals
        first
          | exact xor_value (rowInAtom_lt L g) hixLt
          | wg2_close []
  obtain ⟨t₁₀, hr10, h10⟩ : ∃ t₁₀, run kernel asms L g 1 t₉ = some t₁₀ ∧
      At t₁₀ 2657 (factsFrom ((Flow.live 2657).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h9 using
      try wg2_values
      all_goals
        first
          | wg2_close [hxorLt]
          | wg2_close []
  obtain ⟨t₁₁, hr11, h11⟩ : ∃ t₁₁, run kernel asms L g 1 t₁₀ = some t₁₁ ∧
      At t₁₁ 2658 (factsFrom ((Flow.live 2658).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h10 using
      try wg2_values
      all_goals wg2_close [hgpLt]
  obtain ⟨t₁₂, hr12, h12⟩ : ∃ t₁₂, run kernel asms L g 1 t₁₁ = some t₁₂ ∧
      At t₁₂ 2659 (factsFrom ((Flow.live 2659).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h11 using
      try wg2_values
      all_goals
        first
          | exact and896_value (by omega : groupIdx L g < 2 ^ 20)
          | wg2_close [hgpLt]
  obtain ⟨t₁₃, hr13, h13⟩ : ∃ t₁₃, run kernel asms L g 1 t₁₂ = some t₁₃ ∧
      At t₁₃ 2660 (factsFrom ((Flow.live 2660).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h12 using
      try wg2_values
      all_goals wg2_close [htLt]
  obtain ⟨t₁₄, hr14, h14⟩ : ∃ t₁₄, run kernel asms L g 1 t₁₃ = some t₁₄ ∧
      At t₁₄ 2661 (factsFrom ((Flow.live 2661).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h13 using
      try wg2_values
      all_goals
        first
          | exact and1024_value (by omega : tidOf L g < 2 ^ 26)
          | wg2_close [htLt]
  obtain ⟨t₁₅, hr15, h15⟩ : ∃ t₁₅, run kernel asms L g 1 t₁₄ = some t₁₅ ∧
      At t₁₅ 2662 (factsFrom ((Flow.live 2662).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h14 using
      try wg2_values
      all_goals
        first
          | exact or_value (by omega : rowInAtom L g * 128 < 2 ^ 31)
              (by omega : groupIdx L g / 8 * 1024 < 2 ^ 31)
          | wg2_close []
  obtain ⟨t₁₆, hr16, h16⟩ : ∃ t₁₆, run kernel asms L g 1 t₁₅ = some t₁₆ ∧
      At t₁₆ 2663 (factsFrom ((Flow.live 2663).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h15 using
      try wg2_values
      all_goals
        first
          | exact dstOff_value (rowInAtom_lt L g) hixLt (by omega : groupIdx L g / 8 < 2 ^ 21)
          | wg2_close []
  obtain ⟨t₁₇, hr17, h17⟩ : ∃ t₁₇, run kernel asms L g 2 t₁₆ = some t₁₇ ∧
      At t₁₇ 2665 (factsFrom ((Flow.live 2665).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h16 using
      try wg2_values
      all_goals
        first
          | wg2_close [hixLt, rawBytesPerThread]
          | exact mul576_value hgpLt
          | wg2_close []
  obtain ⟨t₁₈, hr18, h18⟩ : ∃ t₁₈, run kernel asms L g 2 t₁₇ = some t₁₈ ∧
      At t₁₈ 2667 (factsFrom ((Flow.live 2667).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h17 using
      try wg2_values
      all_goals
        first
          | wg2_close [hpar]
          | wg2_close [hbuf]
  obtain ⟨t₁₉, hr19, h19⟩ : ∃ t₁₉, run kernel asms L g 2 t₁₈ = some t₁₉ ∧
      At t₁₉ 2669 (factsFrom ((Flow.live 2669).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h18 using
      try wg2_values
      all_goals
        first
          | exact setp_gt3_pred hixLt
          | wg2_close [hpar]
  obtain ⟨t₂₀, hr20, h20⟩ : ∃ t₂₀, run kernel asms L g 2 t₁₉ = some t₂₀ ∧
      At t₂₀ 2671 (factsFrom ((Flow.live 2671).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h19 using
      try wg2_values
      all_goals wg2_close [hpar]
  obtain ⟨t₂₁, hr21, h21⟩ : ∃ t₂₁, run kernel asms L g 3 t₂₀ = some t₂₁ ∧
      At t₂₁ 2674 (factsFrom ((Flow.live 2674).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h20 using
      try wg2_values
      all_goals
        first
          | wg2_close [hshared, sb, b32]
          | wg2_close [hb8, sb, b32]
  obtain ⟨t₂₂, hr22, h22⟩ : ∃ t₂₂, run kernel asms L g 3 t₂₁ = some t₂₂ ∧
      At t₂₂ 2677 (factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
    seg_fp h21 using
      try wg2_values
      all_goals
        first
          | wg2_close [nf_not]
          | wg2_close [hb58, sb, b32, rawReadyOff]
          | wg2_close []
  exact ⟨t₂₂, by
    simpa using
      run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
        (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
        (run_comp (run_comp (run_comp (run_comp (run_comp hr1 hr2) hr3) hr4) hr5) hr6) hr7)
        hr8) hr9) hr10) hr11) hr12) hr13) hr14) hr15) hr16) hr17) hr18) hr19) hr20) hr21)
        hr22, h22⟩

/-- **The `bar_q_utccp` wait's step**: the poll of pc 2644 at the state's parity, whose `true`
arm passes the block-skip test of pc 2648 and runs the block-count and swizzle arithmetic of
pcs 2649-2676 to the first body wait (pc 2677), and whose `false` arm retries the poll. -/
theorem step_qUtccp {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .qUtccp)
    {t u : TState} {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 2644 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_13)
  rw [hpc] at hf
  have hbase : t.regs 2434 = some (sb L qUtccpOff) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hpar : t.regs 2435 = some (b32 d.par) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + qUtccpOff < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    unfold qUtccpOff
    omega
  have hm : mbarLoc L g t 2434 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + qUtccpOff⟩ :=
    mbarLoc_b32 hbase hb (sharedAddr_align hpre (by unfold qUtccpOff; omega))
  have hq : readBits L g t 32 (.reg 2435) = .ok (BitVec.ofNat 64 d.par) :=
    readBits_b32 hpar (by have := hinv.parLt; omega)
  obtain ⟨ok, acq', sc', he, hu⟩ := fires_wait_at_succ (A := asms) (t := t)
    (p := 4124) (base := 2434) (off := 0) (par := .reg 2435) (acq := true) (sc := .cta)
    (m := ⟨.shared, g / L.block, L.sharedBase + qUtccpOff⟩)
    (q := BitVec.ofNat 64 d.par) (pc := 2644) (e := e) (u := u) hm hq hf
  have hok : ok = false ∨ ok = true := by
    rcases Bool.eq_false_or_eq_true ok with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hok with hok | hok
  · rw [hok] at he hu
    have h0 : At u 2645 ((4124, .pred false) ::
        factsFrom ((Flow.live 2644).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4124) (pc := 2644) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2644 (factsFrom ((Flow.live 2644).filter (fun r =>
          tracked.contains r)) (valueOf P L g d)) := by
      seg_fp h0 using
        try wg2_values
        all_goals wg2_close []
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr,
      (AtD.of_facts (d := d) (pc := 2644) (hpc := by rw [hd]; rfl) (hsub := by simp [Site.sub, hd])
          (hacc := by simp [accAt, hd]) ht (by simp [payloadFacts, hd])), hinv⟩)
    rw [next, he, hd]
    rfl
  · rw [hok] at he hu
    have h0 : At u 2645 ((4124, .pred true) ::
        factsFrom ((Flow.live 2644).filter (fun r => tracked.contains r))
          (valueOf P L g d)) :=
      at_afterWait hat hpc hu (p := 4124) (pc := 2644) (by decide +kernel)
        (by rw [hd]; intro r j h; nomatch h)
    have hblk : d.block = 0 := hinv.qUtccpBlock hd
    have hbuf : d.buf = 0 := by rw [hinv.bufBlock, hblk]
    have hpar0 : d.par = 0 := by rw [hinv.parBlock, hblk]
    have hixLt : idxInGroup L g < 8 := by
      have := hinv.idxLt; simpa [groupSize] using this
    have hgpLt : groupIdx L g < 16 := by
      have := hinv.groupLt; simpa [numGroups] using this
    have htLt : tidOf L g < 384 := by rw [tidOf_eq hpre]; omega
    have hpadded : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31 := by
      rw [hinv.len0, hinv.len1]
      exact hpre.paddedRange _ hinv.batch
    have hp64 : 64 ≤ origPadded d.len0 + ceilToMultiple d.len1 topkBlock := by
      have hhb := hinv.block
      rw [hblk] at hhb
      unfold totalBlocks at hhb
      have hq0 : 0 < (origPadded d.len0 + ceilToMultiple d.len1 topkBlock) / 64 := hhb
      have hm0 := Nat.mod_add_div (origPadded d.len0 + ceilToMultiple d.len1 topkBlock) 64
      omega
    have htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32 :=
      totalBlocks_lt hinv.lenLt.1 hinv.lenLt.2
    have htotPos : 0 < totalBlocks d.len0 d.len1 := by
      have := hinv.block; rw [hblk] at this; exact this
    obtain ⟨t', hr, ht⟩ := seg_qUtccp (sharedBase_lt hpre) hblk hbuf hpar0 hixLt
      hgpLt htLt hpadded hp64 htotPos htotLt h0
    refine Or.inl (Or.inr ⟨{ d with site := .rawReady }, t', ?_, run_rtg hr,
      (AtD.of_facts (d := { d with site := .rawReady }) (pc := 2677) rfl rfl
        (by simp [accAt]) ht),
      inv_setSite hinv .rawReady (by decide)⟩)
    rw [next, he, hd]
    rfl

/-! ## The second arrival's step

The role's `.free` event is the arrival on `bar_raw_free[buf]` (pc 3599), the release the raw
producer waits for. After it the loop's bookkeeping runs (pcs 3600-3607): the slot is
narrowed to a byte (`cvt.u16.u32`, `and.b16`) and compared with the parity's 16-bit shadow
(`setp.ne.b16 %p136, %r351, %r450`, i.e. `par != buf`), `selp.b16` picks the next block's
parity, `and.b32 %r2988, %r2789, 1` flips the slot (`%r2789 = ~buf`), the counter steps and
`setp.ne %p137, %r2987, 0` tests it. The
back edge (pc 3607) jumps to the body's head (pc 2667) with the next block's state when the
counter is nonzero and otherwise falls through to the named barrier's pcs 3608-3610.

The step is the same shape as the two body waits': the arrival, then the local segment to the
successor. The segment splits where the state's parity decides `%p136` (pcs 3600-3602), at
the test's branch (pcs 3603-3606), and at the back edge itself (pc 3607, one segment per
branch); the successor's table is `afterFree`'s, whose parity is `par != buf ? 1 : 0` and whose
counter entry of the last block is zero — a value the table cannot state, so the last block's
segment carries `%r2987` as an explicit fact. -/

theorem setp_ne_par {p b : Nat} (hp : p < 2) (hb : b < 2) :
    Value.pred (compare Cmp.ne IType.b 16 (truncBits 16 (BitVec.ofNat 64 p))
      (truncBits 16 (truncBits 16 (truncBits 16 (truncBits 32 (BitVec.ofNat 64 b))) &&&
        truncBits 16 (BitVec.ofInt 64 255)))) = Value.pred (decide (p ≠ b)) := by
  interval_cases p <;> interval_cases b <;> decide +kernel

theorem setp_ne_counter {x : Nat} (hx : x < 2 ^ 32) :
    compare Cmp.ne IType.b 32 (truncBits 32 (BitVec.ofNat 64 x))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (x ≠ 0) := by
  have h1 : (truncBits 32 (BitVec.ofNat 64 x)).toNat = x := by
    have e : (BitVec.ofNat 64 x).toNat = x := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
    show (BitVec.ofNat 64 x).toNat % 2 ^ 32 % 2 ^ 64 = x
    rw [e, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  have h2 : (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 := by decide +kernel
  simp only [compare, h1, h2]
  norm_num

theorem add_counter {x : Nat} :
    Value.bits 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 x) + truncBits 32 (BitVec.ofInt 64 1))) =
      b32 ((x + 1) % 2 ^ 32) := by
  show Value.bits 32 _ = _
  nf_simp [b32]
  omega

theorem land1_of_lt {b : Nat} (hb : b < 2) :
    Value.bits 32
      (truncBits 32 (BitVec.ofNat 64 (4294967295 - b)) &&& truncBits 32 (BitVec.ofInt 64 1)) =
      b32 (1 - b) := by
  show Value.bits 32 _ = _
  nf_simp [b32, land1]
  omega

/-- **The body's head**: pcs 2667-2676, the ten instructions that rebuild the scale-select
test, the parity's 16-bit shadow and the next block's slot-dependent addresses from the ring
slot and parity the back edge left. Both the pre-loop pass and the back edge run it. -/
theorem seg_backBody {d : D} {u : TState} (hshared : L.sharedBase + 222952 < 2 ^ 32)
    (hixLt : idxInGroup L g < 8) (hparLt : d.par < 2) (hbufLt : d.buf < 2)
    (h0 : At u 2667 (factsFrom ((Flow.live 2667).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 10 u = some t' ∧
      At t' 2677 (factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  have hb8 : L.sharedBase + 8 * d.buf < 2 ^ 32 := by omega
  have hb58 : L.sharedBase + 8 * d.buf + 222808 < 2 ^ 32 := by
    have : 8 * d.buf ≤ 8 := by omega
    omega
  obtain ⟨t₁, hr₁, h₁⟩ : ∃ t₁, run kernel asms L g 2 u = some t₁ ∧
      At t₁ 2669 (factsFrom ((Flow.live 2669).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h0 using
      try wg2_values
      all_goals first | exact setp_gt3_pred hixLt | wg2_close [hparLt]
  obtain ⟨t₂, hr₂, h₂⟩ : ∃ t₂, run kernel asms L g 2 t₁ = some t₂ ∧
      At t₂ 2671 (factsFrom ((Flow.live 2671).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₁ using
      try wg2_values
      all_goals wg2_close [hparLt]
  obtain ⟨t₃, hr₃, h₃⟩ : ∃ t₃, run kernel asms L g 3 t₂ = some t₃ ∧
      At t₃ 2674 (factsFrom ((Flow.live 2674).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₂ using
      try wg2_values
      all_goals first | wg2_close [hshared, sb, b32] | wg2_close [hb8, sb, b32]
  obtain ⟨t₄, hr₄, h₄⟩ : ∃ t₄, run kernel asms L g 3 t₃ = some t₄ ∧
      At t₄ 2677 (factsFrom ((Flow.live 2677).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp h₃ using
      try wg2_values
      all_goals first
        | wg2_close [nf_not]
        | wg2_close [hb58, sb, b32, rawReadyOff]
        | wg2_close []
  exact ⟨t₄, by simpa using run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄, h₄⟩

/-- The poll's continuation to the skip test's state: pcs 3600-3602. -/
theorem seg_free_a0 {d : D} {u : TState} (hpb : d.par = d.buf) (hparLt : d.par < 2)
    (hbufLt : d.buf < 2)
    (h0 : At u 3600 (factsFrom ((Flow.live 3599).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3603 ((136, .pred false) ::
        factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
  seg_fp h0 using
    try wg2_values
    all_goals first | (rw [setp_ne_par hparLt hbufLt]; simp [hpb]) | wg2_close []

theorem seg_free_a1 {d : D} {u : TState} (hne : ¬ d.par = d.buf) (hparLt : d.par < 2)
    (hbufLt : d.buf < 2)
    (h0 : At u 3600 (factsFrom ((Flow.live 3599).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3603 ((136, .pred true) ::
        factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
  seg_fp h0 using
    try wg2_values
    all_goals first | (rw [setp_ne_par hparLt hbufLt]; simp [hne]) | wg2_close []

/-- The parity flip and the counter's increment, pcs 3603-3606. -/
theorem seg_free_b0 {d d' : D} {u : TState} (hpar : d'.par = 0) (hbuf : d'.buf = 1 - d.buf)
    (hblk : d'.block = d.block + 1) (hlen0 : d'.len0 = d.len0) (hlen1 : d'.len1 = d.len1)
    (hbufLt : d.buf < 2) (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32)
    (hlt : d.block + 1 < totalBlocks d.len0 d.len1)
    (h0 : At u 3603 ((136, .pred false) ::
      factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3606 (factsFrom ((Flow.live 3606).filter (fun r => tracked.contains r))
        (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [hpar]; wg2_close [])
        | (rw [hbuf]; exact land1_of_lt hbufLt)
        | (rw [hblk, hlen0, hlen1, add_counter]
           show Value.bits 32 _ = _
           nf_simp [b32]
           omega)

theorem seg_free_b1 {d d' : D} {u : TState} (hpar : d'.par = 1) (hbuf : d'.buf = 1 - d.buf)
    (hblk : d'.block = d.block + 1) (hlen0 : d'.len0 = d.len0) (hlen1 : d'.len1 = d.len1)
    (hbufLt : d.buf < 2) (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32)
    (hlt : d.block + 1 < totalBlocks d.len0 d.len1)
    (h0 : At u 3603 ((136, .pred true) ::
      factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3606 (factsFrom ((Flow.live 3606).filter (fun r => tracked.contains r))
        (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [hpar]; wg2_close [])
        | (rw [hbuf]; exact land1_of_lt hbufLt)
        | (rw [hblk, hlen0, hlen1, add_counter]
           show Value.bits 32 _ = _
           nf_simp [b32]
           omega)

/-- The back edge's test, pc 3606: the counter is nonzero after the block advanced. -/
theorem seg_free_c {d d' : D} {u : TState} (hblk : d'.block = d.block + 1)
    (hlen0 : d'.len0 = d.len0) (hlen1 : d'.len1 = d.len1)
    (hblkLt : d.block < totalBlocks d.len0 d.len1) (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32)
    (hlt : d.block + 1 < totalBlocks d.len0 d.len1)
    (h0 : At u 3606 (factsFrom ((Flow.live 3606).filter (fun r => tracked.contains r))
        (valueOf P L g d'))) :
    ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3607 ((137, .pred true) ::
        factsFrom ((Flow.live 3607).filter (fun r => tracked.contains r))
          (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [Value.pred.injEq, hblk, hlen0, hlen1,
            setp_ne_counter (by have hl := hblkLt; omega), decide_eq_true_eq]
           exact show d.block + 1 + (2 ^ 32 - totalBlocks d.len0 d.len1) ≠ 0 by
             have hl := hblkLt; omega)
        | wg2_close []

/-- The parity flip and the counter's increment at the last block, pcs 3603-3606: the
counter reaches zero, which the state's table cannot state (its `2987` entry is the negative
block count), so the segment carries it as an explicit fact. -/
theorem seg_free_b0' {d d' : D} {u : TState} (hpar : d'.par = 0) (hbuf : d'.buf = 1 - d.buf)
    (hbufLt : d.buf < 2) (hblkLt : d.block < totalBlocks d.len0 d.len1)
    (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32) (hnlt : ¬ d.block + 1 < totalBlocks d.len0 d.len1)
    (h0 : At u 3603 ((136, .pred false) ::
      factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3606 ((2987, b32 0) ::
        factsFrom ((Flow.live 3606).filter (fun r =>
          r ≠ 2987 && tracked.contains r))
          (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [hpar]; wg2_close [])
        | (rw [hbuf]; exact land1_of_lt hbufLt)
        | (rw [add_counter]; show Value.bits 32 _ = _; nf_simp [b32]; omega)

theorem seg_free_b1' {d d' : D} {u : TState} (hpar : d'.par = 1) (hbuf : d'.buf = 1 - d.buf)
    (hbufLt : d.buf < 2) (hblkLt : d.block < totalBlocks d.len0 d.len1)
    (htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32) (hnlt : ¬ d.block + 1 < totalBlocks d.len0 d.len1)
    (h0 : At u 3603 ((136, .pred true) ::
      factsFrom ((Flow.live 3603).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 3 u = some t' ∧
      At t' 3606 ((2987, b32 0) ::
        factsFrom ((Flow.live 3606).filter (fun r =>
          r ≠ 2987 && tracked.contains r))
          (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [hpar]; wg2_close [])
        | (rw [hbuf]; exact land1_of_lt hbufLt)
        | (rw [add_counter]
           have hl := hblkLt
           show Value.bits 32 _ = _
           nf_simp [b32]
           omega)

/-- The back edge's test at the last block, pc 3606: the counter is zero. -/
theorem seg_free_c' {d' : D} {u : TState}
    (h0 : At u 3606 ((2987, b32 0) ::
      factsFrom ((Flow.live 3606).filter (fun r =>
        r ≠ 2987 && tracked.contains r))
        (valueOf P L g d'))) :
    ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3607 ((137, .pred false) :: (2987, b32 0) ::
        factsFrom ((Flow.live 3607).filter (fun r =>
          r ≠ 2987 && tracked.contains r))
          (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals
      first
        | (rw [Value.pred.injEq, setp_ne_counter (x := 0) (by omega)]; rfl)
        | wg2_close []

/-- The back edge taken: pc 3607 jumps to pc 2667 with the next block's state. -/
theorem seg_free_d {d : D} {u : TState}
    (h0 : At u 3607 ((137, .pred true) ::
      factsFrom ((Flow.live 3607).filter (fun r => tracked.contains r))
        (valueOf P L g d))) :
    ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 2667 (factsFrom ((Flow.live 2667).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  seg_fp h0 using
    try wg2_values
    all_goals wg2_close []

/-- The back edge not taken: pc 3607 falls through to the role's named barrier. -/
theorem seg_free_d' {d' : D} {u : TState}
    (h0 : At u 3607 ((137, .pred false) :: (2987, b32 0) ::
      factsFrom ((Flow.live 3607).filter (fun r =>
        r ≠ 2987 && tracked.contains r))
        (valueOf P L g d'))) :
    ∃ t', run kernel asms L g 1 u = some t' ∧
      At t' 3608 (factsFrom ((Flow.live 3608).filter (fun r => tracked.contains r))
        (valueOf P L g d')) := by
  seg_fp h0 using
    try wg2_values
    all_goals wg2_close []

theorem seg_free_e {d d' : D} {u : TState}
    (h0 : At u 3608 (factsFrom ((Flow.live 3608).filter (fun r => tracked.contains r))
        (valueOf P L g d'))) :
    ∃ t', run kernel asms L g 2 u = some t' ∧
      At t' 3610 (factsFrom ((Flow.live 3610).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  seg_fp h0 using
    try wg2_values
    all_goals wg2_close []

/-- **The `bar_raw_free` arrival's step**: `mbarrier.arrive` on `bar_raw_free[buf]` (pc 3599)
and the loop's bookkeeping (pcs 3600-3607). The parity flips when the ring slot changes
(`%r457 = par != buf ? 1 : 0`), the slot flips (`%r2988 = ~buf & 1`), the counter steps
(`%r2987 += 1`) and the back edge jumps to the body's head (pc 2667) when the counter is
nonzero, i.e. when a further block follows; otherwise it falls through to the named barrier's
pcs 3608-3609. The two successors are `afterFree`'s branches. -/
theorem step_free {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .free) {t u : TState}
    {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 3599 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
  rw [hpc] at hf
  have hbase : t.regs 2784 = some (sb L (rawFreeOff d.buf)) :=
    AtD.regAt hat hpc (by decide +kernel)
  have hb : L.sharedBase + rawFreeOff d.buf < 2 ^ 32 := by
    have h1 := sharedBase_lt hpre
    unfold rawFreeOff
    have h2 := hinv.bufLt
    omega
  have hm : mbarLoc L g t 2784 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + rawFreeOff d.buf⟩ :=
    mbarLoc_b32 hbase hb (sharedAddr_align hpre (by unfold rawFreeOff; omega))
  obtain ⟨rel', sc', he, hu⟩ := fires_arrive_next (A := asms) (t := t) (base := 2784)
    (off := 0) (tx := .imm 0) (count := .imm 1) (cluster := false) (rel := true) (sc := .cta)
    (pc := 3599) (e := e) (o := some u)
    (m := ⟨.shared, g / L.block, L.sharedBase + rawFreeOff d.buf⟩)
    (bytes := truncBits 32 (BitVec.ofInt 64 0)) (n := truncBits 32 (BitVec.ofInt 64 1))
    hm (by simp [readBits, pure, Except.pure]) (by simp [readBits, pure, Except.pure]) hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have h0 : At u 3600
      (factsFrom ((Flow.live 3599).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    rw [hu']
    have h5 : At t 3599 (factsFrom ((Flow.live 3599).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
      rw [← hpc]
      exact at_of_atD hat (by rw [hd]; intro r j h; nomatch h)
    exact At.next h5
  have hixLt : idxInGroup L g < 8 := by
    have := hinv.idxLt; simpa [groupSize] using this
  have hparLt : d.par < 2 := hinv.parLt
  have hbufLt : d.buf < 2 := hinv.bufLt
  have hblkLt : d.block < totalBlocks d.len0 d.len1 := hinv.block
  have htotLt : totalBlocks d.len0 d.len1 < 2 ^ 32 := totalBlocks_lt hinv.lenLt.1 hinv.lenLt.2
  have hlt3 : L.sharedBase + 222952 < 2 ^ 32 := sharedBase_lt hpre
  by_cases hpb : d.par = d.buf
  · obtain ⟨t₁, hr₁, h₁⟩ := seg_free_a0 hpb hparLt hbufLt h0
    by_cases hlt : d.block + 1 < totalBlocks d.len0 d.len1
    · obtain ⟨t₂, hr₂, h₂⟩ := seg_free_b0 (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl rfl rfl rfl hbufLt htotLt hlt h₁
      obtain ⟨t₃, hr₃, h₃⟩ := seg_free_c (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl rfl hblkLt htotLt hlt h₂
      obtain ⟨t₄, hr₄, h₄⟩ := seg_free_d (d :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) h₃
      obtain ⟨t₅, hr₅, h₅⟩ := seg_backBody (d :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) hlt3 hixLt (by simp) (by simp) h₄
      have heq : afterFree d =
          { d with
            site := .rawReady
            block := d.block + 1
            buf := 1 - d.buf
            par := 0
            extra := isExtraBlock (d.block + 1) d.len0 } := by
        simp only [afterFree, hlt, hpb, ↓reduceIte]
      refine Or.inl (Or.inr ⟨afterFree d, t₅, ?_, ?_, ?_⟩)
      · rw [next, he, hd]; rfl
      · exact run_rtg (by
          simpa using run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
      · rw [heq]
        exact ⟨AtD.of_facts (d := { d with
            site := .rawReady
            block := d.block + 1
            buf := 1 - d.buf
            par := 0
            extra := isExtraBlock (d.block + 1) d.len0 }) (pc := 2677) rfl rfl
            (by simp [accAt]) h₅,
          heq ▸ handoff_inv hinv⟩
    · obtain ⟨t₂, hr₂, h₂⟩ := seg_free_b0' (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl hbufLt hblkLt htotLt hlt h₁
      obtain ⟨t₃, hr₃, h₃⟩ := seg_free_c' (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) h₂
      obtain ⟨t₄, hr₄, h₄⟩ := seg_free_d' (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) h₃
      obtain ⟨t₅, hr₅, h₅⟩ := seg_free_e (d := d) (d' :=
        { d with
          par := 0
          buf := 1 - d.buf
          block := d.block + 1 }) h₄
      have heq : afterFree d = { d with site := .barrier } := by
        simp only [afterFree, hlt, ↓reduceIte]
      refine Or.inl (Or.inr ⟨afterFree d, t₅, ?_, ?_, ?_⟩)
      · rw [next, he, hd]; rfl
      · exact run_rtg (by
          simpa using run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
      · rw [heq]
        exact ⟨AtD.of_facts (d := { d with site := .barrier }) (pc := 3610) rfl rfl rfl h₅,
          heq ▸ handoff_inv hinv⟩
  · obtain ⟨t₁, hr₁, h₁⟩ := seg_free_a1 hpb hparLt hbufLt h0
    by_cases hlt : d.block + 1 < totalBlocks d.len0 d.len1
    · obtain ⟨t₂, hr₂, h₂⟩ := seg_free_b1 (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl rfl rfl rfl hbufLt htotLt hlt h₁
      obtain ⟨t₃, hr₃, h₃⟩ := seg_free_c (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl rfl hblkLt htotLt hlt h₂
      obtain ⟨t₄, hr₄, h₄⟩ := seg_free_d (d :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) h₃
      obtain ⟨t₅, hr₅, h₅⟩ := seg_backBody (d :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) hlt3 hixLt (by simp) (by simp) h₄
      have heq : afterFree d =
          { d with
            site := .rawReady
            block := d.block + 1
            buf := 1 - d.buf
            par := 1
            extra := isExtraBlock (d.block + 1) d.len0 } := by
        simp only [afterFree, hlt, hpb, ↓reduceIte]
      refine Or.inl (Or.inr ⟨afterFree d, t₅, ?_, ?_, ?_⟩)
      · rw [next, he, hd]; rfl
      · exact run_rtg (by
          simpa using run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
      · rw [heq]
        exact ⟨AtD.of_facts (d := { d with
            site := .rawReady
            block := d.block + 1
            buf := 1 - d.buf
            par := 1
            extra := isExtraBlock (d.block + 1) d.len0 }) (pc := 2677) rfl rfl
            (by simp [accAt]) h₅,
          heq ▸ handoff_inv hinv⟩
    · obtain ⟨t₂, hr₂, h₂⟩ := seg_free_b1' (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) rfl rfl hbufLt hblkLt htotLt hlt h₁
      obtain ⟨t₃, hr₃, h₃⟩ := seg_free_c' (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) h₂
      obtain ⟨t₄, hr₄, h₄⟩ := seg_free_d' (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) h₃
      obtain ⟨t₅, hr₅, h₅⟩ := seg_free_e (d := d) (d' :=
        { d with
          par := 1
          buf := 1 - d.buf
          block := d.block + 1 }) h₄
      have heq : afterFree d = { d with site := .barrier } := by
        simp only [afterFree, hlt, ↓reduceIte]
      refine Or.inl (Or.inr ⟨afterFree d, t₅, ?_, ?_, ?_⟩)
      · rw [next, he, hd]; rfl
      · exact run_rtg (by
          simpa using run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hr₅)
      · rw [heq]
        exact ⟨AtD.of_facts (d := { d with site := .barrier }) (pc := 3610) rfl rfl rfl h₅,
          heq ▸ handoff_inv hinv⟩

/-! ## The entry run

The prologue hands warpgroup 2 a thread at pc 2607 with the launch's reads. The role's first
event is one of the three length sites: the `ld.global.nc` of `topk_length` (pc 2620) when the
row's main-cache length pointer is present, the `ld.global.nc` of `extra_topk_length` (pc 2630)
when only the extra cache's is, and the `bar_q_utccp` wait (pc 2644) when neither is. The
local prefix reads the batch count, the two pointers and the two `topk` constants from
`param_0` (`ld.param`, the launch's bytes) and branches on the CTA's place in the grid
(`%ctaid.y < b`, `Entry.batch`) and on the main-cache pointer's null test.

The segments are `seg_fp` over the closed arithmetic, `ld_param` for the `param_0` reads
(whose bytes the launch supplies: `supplied_80`, `supplied_144`) and `run_bra_to` for the
branches. The table states the two pointer words (`%r3017`/`%r3018`), the two `.nc` addresses
(`%r3833`/`%r3835`) and the branch predicates (`%p130`-`%p132`), so the segments read them off
the state; `live_step` and `live_sub` carry a segment's facts to the next program counter.

-/

theorem entry_valueOf (d : D) {r : Nat} (hr : r = 460 ∨ r = 461 ∨ r = 463 ∨ r = 2991) :
    _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g r = valueOf P L g d r := by
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp [_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf, valueOf, table,
      PTX.Flow.lookupLit, Option.getD_some]

theorem entry_at (d : D) {t : TState} (h : Entry P L g t) :
    At t 2607 (atFacts P L g d 2607) := by
  have hl : atFacts P L g d 2607 =
      factsFrom [460, 461, 463, 2991] (valueOf P L g d) := by
    simp only [atFacts, show Flow.live 2607 = [460, 461, 463, 2991] from by decide +kernel]
    rw [show List.filter (fun r => tracked.contains r) [460, 461, 463, 2991] =
      [460, 461, 463, 2991] from by decide +kernel]
  refine ⟨h.pc, h.sub, h.acc, h.fault, ?_⟩
  rw [hl]
  refine holds_of_pointwise fun r hr => ?_
  rw [← entry_valueOf d (by simpa using hr)]
  exact holds_mem h.regs (mem_factsFrom hr)

theorem at_written {d : D} {t t' : TState} {pc : Nat} {ws : List Nat}
    (h : At t pc (atFacts P L g d pc)) (hpc : t'.pc = pc + 1) (hs : t'.sub = t.sub)
    (ha : t'.acc = t.acc) (hf : t'.fault = t.fault)
    (hw : ∀ r ∈ ws, t'.regs r = some (valueOf P L g d r)) (hfr : ∀ r, r ∉ ws → t'.regs r = t.regs r)
    (hl : ∀ r ∈ Flow.live (pc + 1), r ∈ ws ∨ r ∈ Flow.live pc) :
    At t' (pc + 1) (atFacts P L g d (pc + 1)) := by
  refine ⟨hpc, hs.trans h.2.1, ha.trans h.2.2.1, hf.trans h.2.2.2.1,
    holds_of_pointwise fun r hr => ?_⟩
  by_cases hm : r ∈ ws
  · exact hw r hm
  · rw [hfr r hm]
    obtain ⟨hrl, hrt⟩ := List.mem_filter.mp hr
    rcases hl r hrl with h' | h'
    · exact absurd h' hm
    · exact holds_mem h.2.2.2.2 (mem_factsFrom (List.mem_filter.mpr ⟨h', hrt⟩))

/-- Facts of a list hold as facts of a sublist. -/
theorem holds_of_facts {R : Nat → Option Value} {F G : List (Nat × Value)}
    (h : Holds R F) (hsub : ∀ p ∈ G, p ∈ F) : Holds R G := by
  induction G with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨r, v⟩ := p
    exact ⟨holds_mem h (hsub _ (by simp)), ih fun q hq => hsub q (by simp [hq])⟩

theorem at_restate {t : TState} {pc : Nat} {F G : List (Nat × Value)}
    (h : At t pc F) (hFG : ∀ p ∈ G, p ∈ F) : At t pc G :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_of_facts h.2.2.2.2 hFG⟩

theorem atFacts_sub {d : D} {pc pc' : Nat}
    (hs : ∀ r, r ∈ (Flow.live pc).filter (fun r => tracked.contains r) →
      r ∈ (Flow.live pc').filter (fun r => tracked.contains r)) :
    ∀ p ∈ atFacts P L g d pc, p ∈ atFacts P L g d pc' := by
  intro p hp
  simp only [atFacts, factsFrom, List.mem_map] at hp ⊢
  obtain ⟨r, hr, rfl⟩ := hp
  exact ⟨r, hs r hr, rfl⟩

theorem run_bra_to {L : Launch} {g : Nat} {t : TState} {pc target p b : Nat}
    {F G : List (Nat × Value)} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc F) (hp : (p, .pred pick) ∈ F)
    (hb : b = if pick then target else pc + 1)
    (hFG : ∀ q ∈ G, q ∈ F)
    (h1 : pc ∉ paramAdds := by decide) (h2 : pc ∉ prefetchTensorMapSites := by decide) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b G := by
  obtain ⟨t', hr, ht⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g) hc pick h
    (holds_mem h.2.2.2.2 hp)
    (fun a ha => Thread.asms_localRule_bra (t := t) (target := target)
      (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha) (by seg_free_pc)
  rw [← hb] at ht
  exact ⟨t', hr, at_restate ht hFG⟩

theorem ld_param {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    {pc w off r dst : Nat} {ty : DType}
    (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off r dst)⟩)
    (hrp : t.regs r = some (.ptr 64 false (.param (param "0")) 0))
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h : At t pc (atFacts P L g d pc))
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g d dst)
    (hl : ∀ x ∈ Flow.live (pc + 1), x ∈ [dst] ∨ x ∈ Flow.live pc)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off r dst).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (atFacts P L g d (pc + 1)) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (Thread.paramLoad ty off r dst)) = none := by
    intro b hb
    exact Thread.asms_localRule_mem (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) b hb
  refine ⟨_, run_local hc rfl h (Thread.exec_ldParamReg (A := asms) hrp hpre.param0Object
    ⟨by omega, hsze⟩ hal hsup (Assumption.SegFreePc.of_eq h.1 (by seg_free_pc)) hL hw hr),
    at_written h ?_ rfl rfl rfl ?_ ?_ hl⟩
  · simp [setReg, PTX.next, h.1]
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [setReg, PTX.next, hv]
  · intro x hx
    simp only [List.mem_singleton] at hx
    simp [setReg, PTX.next, Function.update_of_ne hx]

theorem param_b32 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramElem 32 32 (paramNat L (param "0") 0 4) = b32 P.b := by
  rw [show paramNat L (param "0") 0 4 = Thread.paramWord L 0 4 from rfl,
    Thread.paramWord_b hpre, paramElem_of_ne (by decide)]
  show Value.bits 32 (BitVec.ofNat 64 (P.b % 2 ^ 32)) = b32 P.b
  rw [show P.b % 2 ^ 32 = P.b from Nat.mod_eq_of_lt (by have := hpre.bLt; omega)]
  rfl

theorem param_topk32 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramElem 32 32 (paramNat L (param "0") 40 4) = b32 P.topk := by
  have h : Thread.paramWord L 40 4 = P.topk % 2 ^ 32 :=
    Thread.paramWord_four fun k hk => by simpa using hpre.paramTopk k hk
  rw [show paramNat L (param "0") 40 4 = Thread.paramWord L 40 4 from rfl, h,
    paramElem_of_ne (by decide)]
  show Value.bits 32 (BitVec.ofNat 64 (P.topk % 2 ^ 32)) = b32 P.topk
  rw [show P.topk % 2 ^ 32 = P.topk from Nat.mod_eq_of_lt (by have := topk_lt hpre; omega)]
  rfl

theorem param_extra32 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramElem 32 32 (paramNat L (param "0") 120 4) = b32 P.extra_topk := by
  have h : Thread.paramWord L 120 4 = P.extra_topk % 2 ^ 32 :=
    Thread.paramWord_four fun k hk => by simpa using hpre.paramExtraTopk k hk
  rw [show paramNat L (param "0") 120 4 = Thread.paramWord L 120 4 from rfl, h,
    paramElem_of_ne (by decide)]
  show Value.bits 32 (BitVec.ofNat 64 (P.extra_topk % 2 ^ 32)) = b32 P.extra_topk
  rw [show P.extra_topk % 2 ^ 32 = P.extra_topk from
    Nat.mod_eq_of_lt (by have := extra_topk_lt hpre; omega)]
  rfl

theorem param_80 {P : Params} {L : Launch} {mem0 : Mem0} (_hpre : Pre P L mem0) :
    paramElem 64 64 (paramNat L (param "0") 80 8) = b64 (Thread.paramWord L 80 8) := by
  rw [paramElem_of_ne (by decide)]
  rfl

theorem param_144 {P : Params} {L : Launch} {mem0 : Mem0} (_hpre : Pre P L mem0) :
    paramElem 64 64 (paramNat L (param "0") 144 8) = b64 (Thread.paramWord L 144 8) := by
  rw [paramElem_of_ne (by decide)]
  rfl

/-- A zero pointer word is the null pointer. -/
theorem ptrIsNull_none {L : Launch} {off : Nat} (hw : Thread.paramWord L off 8 = 0) :
    Thread.ptrIsNull L off = true := by
  unfold Thread.ptrIsNull
  rw [hw]
  rfl

/-- An absent `topk_length` pointer is null. -/
theorem ptrIsNull_80_none {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (h : P.topkLenBase = none) : Thread.ptrIsNull L 80 = true :=
  ptrIsNull_none (Thread.paramWord_80_zero hpre h)

/-- An absent `extra_topk_length` pointer is null. -/
theorem ptrIsNull_144_none {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (h : P.extraTopkLenBase = none) : Thread.ptrIsNull L 144 = true :=
  ptrIsNull_none (Thread.paramWord_144_zero hpre h)

theorem ptrIsNull_80_some {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {x : Nat} (h : P.topkLenBase = some x) : Thread.ptrIsNull L 80 = false := by
  unfold Thread.ptrIsNull
  rw [show Thread.paramWord L 80 8 = x % 2 ^ 64 from Thread.paramWord_80_some hpre h]
  have hx : 0 < x := hpre.topkLenNonNull x h
  have hxlt : x < 2 ^ 64 := hpre.topkLenBaseLt x h
  have h1 : truncBits 64 (BitVec.ofNat 64 (x % 2 ^ 64)) = BitVec.ofNat 64 (x % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, BitVec.toNat_ofNat]
  have h2 : truncBits 64 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by decide
  rw [h1, h2]
  show compare Cmp.eq IType.b 64 (BitVec.ofNat 64 (x % 2 ^ 64)) 0#64 = false
  unfold compare
  rw [decide_eq_false_iff_not]
  simp [BitVec.toNat_ofNat]
  omega

theorem ptrIsNull_144_some {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {x : Nat} (h : P.extraTopkLenBase = some x) : Thread.ptrIsNull L 144 = false := by
  unfold Thread.ptrIsNull
  rw [show Thread.paramWord L 144 8 = x % 2 ^ 64 from Thread.paramWord_144_some hpre h]
  have hx : 0 < x := hpre.extraTopkLenNonNull x h
  have hxlt : x < 2 ^ 64 := hpre.extraTopkLenBaseLt x h
  have h1 : truncBits 64 (BitVec.ofNat 64 (x % 2 ^ 64)) = BitVec.ofNat 64 (x % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp [truncBits, BitVec.toNat_ofNat]
  have h2 : truncBits 64 (BitVec.ofInt 64 0) = BitVec.ofNat 64 0 := by decide
  rw [h1, h2]
  show compare Cmp.eq IType.b 64 (BitVec.ofNat 64 (x % 2 ^ 64)) 0#64 = false
  unfold compare
  rw [decide_eq_false_iff_not]
  simp [BitVec.toNat_ofNat]
  omega

theorem shr3_value {x : Nat} :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (x % 128)) >>>
      truncBits 32 (BitVec.ofInt 64 3)) = b32 ((x % 128) / 8) := by
  have h3 : truncBits 32 (BitVec.ofInt 64 3) = (3#64 : BitVec 64) := by decide
  rw [h3]
  show Value.bits 32 _ = Value.bits 32 _
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, truncBits]
  omega

theorem cmp_ge_value {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : a < b) :
    Value.pred (compare Cmp.ge IType.s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b))) = Value.pred (decide (b ≤ a)) := by
  rw [Value.pred.injEq]
  have h1 : toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) = (a : Int) := toSigned32_ofNat ha
  have h2 : toSigned 32 (truncBits 32 (BitVec.ofNat 64 b)) = (b : Int) := toSigned32_ofNat hb
  unfold compare
  rw [h1, h2]
  simp only [decide_eq_decide]
  omega

theorem supplied_80 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ParamSupplied L (param "0") 80 8 := by
  cases h : P.topkLenBase with
  | none =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    exact fun k hk => ⟨0, hb.1 k hk⟩
  | some x =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

theorem supplied_144 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ParamSupplied L (param "0") 144 8 := by
  cases h : P.extraTopkLenBase with
  | none =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    exact fun k hk => ⟨0, hb.1 k hk⟩
  | some x =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

/-- The live registers of one pc all lie in the next one's facts (or in a written list). -/
theorem live_step {a b : Nat} {l : List Nat}
    (h : (Flow.live b).all (fun x => l.contains x || (Flow.live a).contains x) = true) :
    ∀ x ∈ Flow.live b, x ∈ l ∨ x ∈ Flow.live a := by
  intro x hx
  have h1 := List.all_eq_true.mp h x hx
  simp only [Bool.or_eq_true, List.contains_iff_mem] at h1
  exact h1

/-- The tracked registers of one pc are tracked and live at another. -/
theorem live_sub {pc pc' : Nat}
    (h : (Flow.live pc).all (fun r => !(tracked.contains r) || (Flow.live pc').contains r)
      = true) :
    ∀ r, r ∈ (Flow.live pc).filter (fun r => tracked.contains r) →
      r ∈ (Flow.live pc').filter (fun r => tracked.contains r) := by
  intro r hr
  obtain ⟨hrl, hrt⟩ := List.mem_filter.mp hr
  have h1 := List.all_eq_true.mp h r hrl
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h1
  rcases h1 with h' | h'
  · rw [h'] at hrt
    exact absurd hrt (by decide)
  · exact List.mem_filter.mpr ⟨h', hrt⟩

/-- The 64-bit sum of two address words below `2 ^ 64`. -/
theorem add64_value {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 a) +
      truncBits 64 (BitVec.ofNat 64 b))) = b64 ((a + b) % 2 ^ 64) := by
  rw [truncBits_ofNat ha (by omega), truncBits_ofNat hb (by omega)]
  show Value.bits 64 (truncBits 64 (BitVec.ofNat 64 a + BitVec.ofNat 64 b)) =
    Value.bits 64 (BitVec.ofNat 64 ((a + b) % 2 ^ 64))
  congr 1
  have hm : (a + b) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [truncBits, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hm, Nat.mod_mod, Nat.add_mod]

theorem truncBits32_toNat (c : Nat) :
    (truncBits 32 (BitVec.ofNat 64 c)).toNat = c % 2 ^ 32 := by
  rw [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_mod_of_dvd c (by decide : 2 ^ 32 ∣ 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt c (by decide : 0 < 2 ^ 32); omega)

theorem mul4_toNat (c : Nat) :
    (truncBits 32 (BitVec.ofNat 64 c)).toNat * (truncBits 32 (BitVec.ofInt 64 4)).toNat
      = (c % 2 ^ 32) * 4 := by
  rw [truncBits32_toNat]
  rfl

theorem addr64_value {pw c : Nat} (hpw : pw < 2 ^ 64) (hc : c < 2 ^ 32) :
    Value.bits 64 (truncBits 64 (truncBits 64 (BitVec.ofNat 64 pw) +
      truncBits 64 (BitVec.ofNat 64
        ((truncBits 32 (BitVec.ofNat 64 c)).toNat *
          (truncBits 32 (BitVec.ofInt 64 4)).toNat)))) =
      b64 ((pw + 4 * c) % 2 ^ 64) := by
  rw [mul4_toNat, Nat.mod_eq_of_lt hc, Nat.mul_comm]
  exact add64_value hpw (by omega)

/-- The `and` of two literal 64-bit words whose values fit the word: the normal form of an
`and.b32` before it is truncated to 32 bits. -/
theorem and_ofNat_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact (Nat.mod_eq_of_lt (Nat.and_lt_two_pow a hb)).symm

/-- **The whole-word ceiling**: `and.b32 %r, %r, -64` of a padded length is
`ku::ceil(len, 64)` (pcs 2626 and 2635). -/
theorem and_neg64_ceil {x : Nat} (h : x + 63 < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 (x + 63)) &&&
      truncBits 32 (BitVec.ofInt 64 (-64))) = b32 (ceilToMultiple x topkBlock) := by
  have hce : ceilToMultiple x topkBlock = (x + 63) / 64 * 64 := by
    unfold ceilToMultiple topkBlock
    rw [show x + 64 - 1 = x + 63 from by omega]
  have hm : truncBits 32 (BitVec.ofInt 64 (-64)) = BitVec.ofNat 64 ((2 ^ 32 : Nat) - 64) := by
    decide
  rw [hce, show truncBits 32 (BitVec.ofNat 64 (x + 63)) = BitVec.ofNat 64 (x + 63) from
    truncBits_ofNat (by omega) (by decide), hm,
    and_ofNat_ofNat (by omega) (by decide), land_neg64_of_lt h]
  rfl

/-- **The padded count**: `max.s32 %r, %r, 64` of the ceiling is `origPadded` (pc 2636). -/
theorem max64_value {x : Nat} (hx : x < 2 ^ 31) :
    Value.bits 32 (if compare Cmp.gt IType.s 32 (truncBits 32 (BitVec.ofNat 64 x))
        (truncBits 32 (BitVec.ofInt 64 64)) then truncBits 32 (BitVec.ofNat 64 x)
      else truncBits 32 (BitVec.ofInt 64 64)) = b32 (max x 64) := by
  have h64 : truncBits 32 (BitVec.ofInt 64 64) = BitVec.ofNat 64 64 := by decide
  have hgt : compare Cmp.gt IType.s 32 (truncBits 32 (BitVec.ofNat 64 x))
      (truncBits 32 (BitVec.ofInt 64 64)) = decide (64 < x) := by
    simp only [compare]
    rw [h64, toSigned32_ofNat hx,
      show toSigned 32 (64#64 : BitVec 64) = (64 : Int) from by decide]
    rw [decide_eq_decide]
    omega
  rw [hgt]
  by_cases h : 64 < x
  · simp only [h]
    have hm : max x 64 = x := Nat.max_eq_left (by omega)
    rw [hm, show truncBits 32 (BitVec.ofNat 64 x) = BitVec.ofNat 64 x from
      truncBits_ofNat (by omega) (by decide)]
    rfl
  · simp only [h]
    have hm : max x 64 = 64 := Nat.max_eq_right (by omega)
    rw [hm, h64]
    rfl

/-- **The wrapped difference**: `sub.s32 %r2444, %r2441, %r2437` is
`ceil - (len1 + 63)` as a 32-bit word (pc 2638). -/
theorem sub_ceil_value {c n : Nat} (hn : n < 2 ^ 32) (hc : c < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 c) -
      truncBits 32 (BitVec.ofNat 64 n))) = b32 ((c + (2 ^ 32 - n)) % 2 ^ 32) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hc64 : c < 2 ^ 64 := by omega
  have key : (2 ^ 64 - n + c) % 2 ^ 32 = (c + (2 ^ 32 - n)) % 2 ^ 32 := by
    have hpow : (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 := by norm_num
    rcases (by omega : n ≤ c ∨ c ≤ n) with h | h
    · have e1 : 2 ^ 32 * 2 ^ 32 - n + c = (c - n) + 2 ^ 32 * 2 ^ 32 := by omega
      have e2 : c + (2 ^ 32 - n) = (c - n) + 1 * 2 ^ 32 := by omega
      rw [hpow, e1, e2, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
    · have e1 : 2 ^ 32 * 2 ^ 32 - n + c =
          (2 ^ 32 - (n - c)) + (2 ^ 32 - 1) * 2 ^ 32 := by omega
      have e2 : c + (2 ^ 32 - n) = (2 ^ 32 - (n - c)) + 0 * 2 ^ 32 := by omega
      rw [hpow, e1, e2, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right]
  have h1 : truncBits 32 (BitVec.ofNat 64 c) = BitVec.ofNat 64 c := truncBits_ofNat hc (by decide)
  have h2 : truncBits 32 (BitVec.ofNat 64 n) = BitVec.ofNat 64 n := truncBits_ofNat hn (by decide)
  show Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 c) -
    truncBits 32 (BitVec.ofNat 64 n))) = b32 ((c + (2 ^ 32 - n)) % 2 ^ 32)
  rw [h1, h2]
  have hnf : truncBits 32 (BitVec.ofNat 64 c - BitVec.ofNat 64 n) =
      BitVec.ofNat 64 ((c + (2 ^ 32 - n)) % 2 ^ 32) := by
    have e3 : ∀ a : Nat, a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := fun a =>
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
    apply BitVec.eq_of_toNat_eq
    rw [truncBits, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hc64, Nat.mod_eq_of_lt hn64,
      Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64), e3, key, BitVec.toNat_ofNat, e3]
  rw [hnf]
  rfl

/-- **The entry prefix**: from the prologue's hand-off at pc 2607 to the main-cache pointer's
null test (pc 2617), with the two `param_0` constants' values as the table states them. -/
theorem start_prefix {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} (hentry : Entry P L g t)
    (d : D) (hv85 : paramElem 32 32 (paramNat L (param "0") 40 4) = valueOf P L g d 2985)
    (hv86 : paramElem 32 32 (paramNat L (param "0") 120 4) = valueOf P L g d 2986) :
    ∃ t', run kernel asms L g 10 t = some t' ∧ At t' 2617 (atFacts P L g d 2617) := by
  have hcy : ctaidY L g < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have he : ctaidY L g < P.b := hentry.batch
  have hbLt : P.b < 2 ^ 31 := hpre.bLt
  have hcy31 : ctaidY L g < 2 ^ 31 := by omega
  have h0 : At t 2607 (atFacts P L g d 2607) := entry_at _ hentry
  -- the group and the lane
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 2 t = some t1 ∧
      At t1 2609 (atFacts P L g d 2609) := by
    seg_fp h0 using
      try wg2_values
      all_goals first
        | exact and7_value (x := tidOf L g)
        | exact shr3_value (x := tidOf L g)
  -- the batch count
  have hrp1 : t1.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm : (2991, valueOf P L g d 2991) ∈ atFacts P L g d 2609 :=
      mem_factsFrom (by decide +kernel)
    have := holds_mem h1.2.2.2.2 hm
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  have hv_b : paramElem 32 32 (paramNat L (param "0") 0 4) = valueOf P L g d 2429 := by
    rw [param_b32 hpre]; wg2_values
  obtain ⟨t2, hr2, h2⟩ := ld_param (d := d) (pc := 2609) (w := 32) (off := 0)
    (r := 2991) (dst := 2429) (ty := .int .b 32) hpre Flow.code_2609 hrp1
    (fun k hk => ⟨_, hpre.paramB k hk⟩) (by decide) (by decide) h1 hv_b
    (live_step (a := 2609) (b := 2610) (l := [2429]) (by decide +kernel))
    (by decide) (by decide)
  -- the exit test
  obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 2611 (atFacts P L g d 2611) := by
    seg_fp h2 using
      try wg2_values
      all_goals first
        | exact cmp_ge_value hcy31 hbLt he
        | wg2_close []
  -- the CTA is a row of the grid: the exit branch is not taken
  have hpick : decide (P.b ≤ ctaidY L g) = false := by
    rw [decide_eq_false_iff_not]
    exact Nat.not_le.mpr he
  have hp130 : (130, Value.pred (decide (P.b ≤ ctaidY L g))) ∈
      atFacts P L g d 2611 := by
    have hm := mem_factsFrom (live := (Flow.live 2611).filter (fun r => tracked.contains r))
      (val := valueOf P L g d) (by decide +kernel : 130 ∈
        (Flow.live 2611).filter (fun r => tracked.contains r))
    simpa [atFacts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using hm
  obtain ⟨t4, hr4, h4⟩ := run_bra_to (pc := 2611) (target := 3611) (p := 130)
    (pick := decide (P.b ≤ ctaidY L g)) Flow.code_2611 h3 hp130
    (b := 2612) (by rw [hpick]; rfl)
    (atFacts_sub (pc := 2612) (pc' := 2611) (live_sub (by decide +kernel)))
  -- the two length pointers and the two parameter constants
  have hrp2 : t4.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm : (2991, valueOf P L g d 2991) ∈ atFacts P L g d 2612 :=
      mem_factsFrom (by decide +kernel)
    have := holds_mem h4.2.2.2.2 hm
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  have hv80 : paramElem 64 64 (paramNat L (param "0") 80 8) = valueOf P L g d 3017 := by
    rw [param_80 hpre]; wg2_values
  obtain ⟨t5, hr5, h5⟩ := ld_param (d := d) (pc := 2612) (w := 64) (off := 80)
    (r := 2991) (dst := 3017) (ty := .int .b 64) hpre Flow.code_2612 hrp2
    (supplied_80 hpre) (by decide) (by decide) h4 hv80
    (live_step (a := 2612) (b := 2613) (l := [3017]) (by decide +kernel))
    (by decide) (by decide)
  have hrp3 : t5.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm : (2991, valueOf P L g d 2991) ∈ atFacts P L g d 2613 :=
      mem_factsFrom (by decide +kernel)
    have := holds_mem h5.2.2.2.2 hm
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  obtain ⟨t6, hr6, h6⟩ := ld_param (d := d) (pc := 2613) (w := 32) (off := 40)
    (r := 2991) (dst := 2985) (ty := .int .b 32) hpre Flow.code_2613 hrp3
    (fun k hk => ⟨_, hpre.paramTopk k hk⟩) (by decide) (by decide) h5 hv85
    (live_step (a := 2613) (b := 2614) (l := [2985]) (by decide +kernel))
    (by decide) (by decide)
  have hrp4 : t6.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm : (2991, valueOf P L g d 2991) ∈ atFacts P L g d 2614 :=
      mem_factsFrom (by decide +kernel)
    have := holds_mem h6.2.2.2.2 hm
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  have hv144 : paramElem 64 64 (paramNat L (param "0") 144 8) = valueOf P L g d 3018 := by
    rw [param_144 hpre]; wg2_values
  obtain ⟨t7, hr7, h7⟩ := ld_param (d := d) (pc := 2614) (w := 64) (off := 144)
    (r := 2991) (dst := 3018) (ty := .int .b 64) hpre Flow.code_2614 hrp4
    (supplied_144 hpre) (by decide) (by decide) h6 hv144
    (live_step (a := 2614) (b := 2615) (l := [3018]) (by decide +kernel))
    (by decide) (by decide)
  have hrp5 : t7.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm : (2991, valueOf P L g d 2991) ∈ atFacts P L g d 2615 :=
      mem_factsFrom (by decide +kernel)
    have := holds_mem h7.2.2.2.2 hm
    simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  obtain ⟨t8, hr8, h8⟩ := ld_param (d := d) (pc := 2615) (w := 32) (off := 120)
    (r := 2991) (dst := 2986) (ty := .int .b 32) hpre Flow.code_2615 hrp5
    (fun k hk => ⟨_, hpre.paramExtraTopk k hk⟩) (by decide) (by decide) h7 hv86
    (live_step (a := 2615) (b := 2616) (l := [2986]) (by decide +kernel))
    (by decide) (by decide)
  -- the main-cache pointer's null test
  obtain ⟨t9, hr9, h9⟩ : ∃ t9, run kernel asms L g 1 t8 = some t9 ∧
      At t9 2617 (atFacts P L g d 2617) := by
    seg_fp h8 using
      try wg2_values
      all_goals first
        | rfl
        | wg2_close []
  refine ⟨t9, ?_, h9⟩
  simpa using run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp hr1 hr2) hr3) hr4) hr5) hr6) hr7) hr8) hr9

/-- **The entry run to the `topk_length` read**: from the prologue's hand-off at pc 2607 to the
`.nc` load of pc 2620, when the row's main-cache length pointer is present. -/
theorem start_lenOrig {mem0 : Mem0} (hpre : Pre P L mem0) {x : Nat} (hb : P.topkLenBase = some x)
    {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g) := by
  have hsite : (init P L g).site = .lenOrig := by simp [init, firstSite, hb]
  have hcy : ctaidY L g < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hv85 : paramElem 32 32 (paramNat L (param "0") 40 4) =
      valueOf P L g (init P L g) 2985 := by
    rw [param_topk32 hpre]
    wg2_values
    simp [hsite]
  have hv86 : paramElem 32 32 (paramNat L (param "0") 120 4) =
      valueOf P L g (init P L g) 2986 := by
    rw [param_extra32 hpre]
    wg2_values
    simp [hsite]
  obtain ⟨t8, hr8, h8⟩ := start_prefix hpre hentry (init P L g) hv85 hv86
  -- the main-cache pointer is not null: the length read follows
  have hp131 : (131, Value.pred (Thread.ptrIsNull L 80)) ∈
      atFacts P L g (init P L g) 2617 := by
    have hm := mem_factsFrom (live := (Flow.live 2617).filter (fun r => tracked.contains r))
      (val := valueOf P L g (init P L g)) (by decide +kernel : 131 ∈
        (Flow.live 2617).filter (fun r => tracked.contains r))
    simpa [atFacts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hpick80 : Thread.ptrIsNull L 80 = false := ptrIsNull_80_some hpre hb
  obtain ⟨t10, hr10, h10⟩ := run_bra_to (pc := 2617) (target := 2621) (p := 131)
    (pick := Thread.ptrIsNull L 80) Flow.code_2617 h8 hp131
    (b := 2618) (by rw [hpick80]; rfl)
    (atFacts_sub (pc := 2618) (pc' := 2617) (live_sub (by decide +kernel)))
  -- the read's address: the pointer plus four bytes per batch
  obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 2 t10 = some t11 ∧
      At t11 2620 (atFacts P L g (init P L g) 2620) := by
    seg_fp h10 using
      try wg2_values
      all_goals first
        | exact addr64_value (Thread.paramWord_lt L 80) hcy
        | wg2_close [hcy]
  exact ⟨t11, run_rtg (by
      simpa using run_comp (run_comp hr8 hr10) hr11),
    AtD.of_facts (d := init P L g) (pc := 2620) (hpc := by rw [hsite]; rfl)
      (hsub := by simp [Site.sub, hsite]) (hacc := by simp [accAt, hsite]) h11
      (by simp [payloadFacts, hsite]),
    init_inv hpre g hentry.batch⟩

theorem seg_mainCeil {d : D} (hsite0 : d.site ≠ .lenOrig) (hbr : d.len0 + 63 < 2 ^ 31) :
    Seg kernel asms L g 6 2621 (atFacts P L g d 2621) 2627 (atFacts P L g d 2627) := by
  intro t10 h10
  obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 1 t10 = some t11 ∧
      At t11 2622 (atFacts P L g d 2622) := by
    seg_fp h10 using
      try wg2_values
      all_goals first
        | norm_bits []
        | wg2_close []
  obtain ⟨t12, hr12, h12⟩ : ∃ t12, run kernel asms L g 1 t11 = some t12 ∧
      At t12 2623 (atFacts P L g d 2623) := by
    seg_fp h11 using
      try wg2_values
      all_goals first
        | norm_bits [hsite0]
        | wg2_close [hsite0]
  obtain ⟨t13, hr13, h13⟩ : ∃ t13, run kernel asms L g 1 t12 = some t13 ∧
      At t13 2624 (atFacts P L g d 2624) := by
    seg_fp h12 using
      try wg2_values
      all_goals first
        | exact shr31_value hbr
        | norm_bits [hbr]
  obtain ⟨t14, hr14, h14⟩ : ∃ t14, run kernel asms L g 1 t13 = some t14 ∧
      At t14 2625 (atFacts P L g d 2625) := by
    seg_fp h13 using
      try wg2_values
      all_goals first
        | norm_bits []
        | wg2_close []
  obtain ⟨t15, hr15, h15⟩ : ∃ t15, run kernel asms L g 1 t14 = some t15 ∧
      At t15 2626 (atFacts P L g d 2626) := by
    seg_fp h14 using
      try wg2_values
      all_goals first
        | norm_bits [hbr]
        | wg2_close [hbr]
  obtain ⟨t16, hr16, h16⟩ : ∃ t16, run kernel asms L g 1 t15 = some t16 ∧
      At t16 2627 (atFacts P L g d 2627) := by
    seg_fp h15 using
      try wg2_values
      all_goals first
        | exact and_neg64_ceil (x := d.len0) (by omega)
        | norm_bits []
  exact ⟨t16, by simpa using run_comp (run_comp (run_comp (run_comp
    (run_comp hr11 hr12) hr13) hr14) hr15) hr16, h16⟩

theorem seg_extraLenAddr {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) {ptr : Nat}
    (hb : P.extraTopkLenBase = some ptr) :
    Seg kernel asms L g 3 2627 (atFacts P L g d 2627) 2630 (atFacts P L g d 2630) := by
  intro t9 h9
  -- the extra pointer is not null: the `.nc` read follows
  have hp132 : (132, Value.pred (Thread.ptrIsNull L 144)) ∈
      atFacts P L g d 2627 := by
    have hm := mem_factsFrom (live := (Flow.live 2627).filter (fun r => tracked.contains r))
      (val := valueOf P L g d) (by decide +kernel : 132 ∈
        (Flow.live 2627).filter (fun r => tracked.contains r))
    simpa [atFacts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hpick : Thread.ptrIsNull L 144 = false := ptrIsNull_144_some hpre hb
  obtain ⟨t10, hr10, h10⟩ := run_bra_to (pc := 2627) (target := 2631) (p := 132)
    (pick := Thread.ptrIsNull L 144) Flow.code_2627 h9 hp132
    (b := 2628) (by rw [hpick]; rfl)
    (atFacts_sub (pc := 2628) (pc' := 2627) (live_sub (by decide +kernel)))
  -- the read's address: the pointer plus four bytes per batch
  obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 2 t10 = some t11 ∧
      At t11 2630 (atFacts P L g d 2630) := by
    seg_fp h10 using
      try wg2_values
      all_goals first
        | exact addr64_value (Thread.paramWord_lt L 144) (Nat.mod_lt _ (by decide))
        | wg2_close []
  exact ⟨t11, run_comp hr10 hr11, h11⟩

theorem seg_skipExtraLen {mem0 : Mem0} {d : D} (hpre : Pre P L mem0)
    (hb : P.extraTopkLenBase = none) :
    Seg kernel asms L g 1 2627 (atFacts P L g d 2627) 2631 (atFacts P L g d 2631) := by
  intro t9 h9
  -- the extra pointer is null too: the `bar_q_utccp` wait follows
  have hp132 : (132, Value.pred (Thread.ptrIsNull L 144)) ∈
      atFacts P L g d 2627 := by
    have hm := mem_factsFrom (live := (Flow.live 2627).filter (fun r => tracked.contains r))
      (val := valueOf P L g d) (by decide +kernel : 132 ∈
        (Flow.live 2627).filter (fun r => tracked.contains r))
    simpa [atFacts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using hm
  obtain ⟨t10, hr10, h10⟩ := run_bra_to (pc := 2627) (target := 2631) (p := 132)
    (pick := Thread.ptrIsNull L 144) Flow.code_2627 h9 hp132
    (b := 2631) (by rw [ptrIsNull_144_none hpre hb]; rfl)
    (atFacts_sub (pc := 2631) (pc' := 2627) (live_sub (by decide +kernel)))
  exact ⟨t10, hr10, h10⟩

theorem seg_extraCeil {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hinv : Inv P L g d)
    (hsite : d.site = .qUtccp) (hpar : d.par = 0) :
    Seg kernel asms L g 13 2631 (atFacts P L g d 2631) 2644 (atFacts P L g d 2644) := by
  intro t10 h10
  have hsite0 : d.site ≠ .lenOrig := by rw [hsite]; exact fun h => nomatch h
  have hsite1 : d.site ≠ .lenExtra := by rw [hsite]; exact fun h => nomatch h
  have hshared : L.sharedBase < 2 ^ 32 := by have := sharedBase_lt hpre; omega
  have hbr0 : d.len0 + 63 < 2 ^ 31 := by
    have h := topkLen_le hpre hinv.batch
    have hb := hpre.topkAdd63Lt
    rw [hinv.len0]
    omega
  have hbr1 : d.len1 + 63 < 2 ^ 31 := by
    have h := extraTopkLen_le hpre hinv.batch
    have hb := hpre.extraTopkAdd63Lt
    rw [hinv.len1]
    omega
  have hce1 : ceilToMultiple d.len1 topkBlock ≤ d.len1 + 63 := by
    have h := Nat.div_mul_le_self (d.len1 + 64 - 1) 64
    unfold ceilToMultiple topkBlock
    omega
  have hceil1 : ceilToMultiple d.len1 topkBlock < 2 ^ 32 := by omega
  have hceil0 : ceilToMultiple d.len0 topkBlock < 2 ^ 31 := by
    have h := Nat.div_mul_le_self (d.len0 + 64 - 1) 64
    unfold ceilToMultiple topkBlock
    omega
  have hpad31 : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31 := by
    rw [hinv.len0, hinv.len1]
    exact hpre.paddedRange _ hinv.batch
  have hborg : d.len1 + 63 + origPadded d.len0 < 2 ^ 32 := by omega
  have hpad : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 32 := by omega
  -- the extra cache's `ku::ceil`
  obtain ⟨t11, hr11, h11⟩ : ∃ t11, run kernel asms L g 1 t10 = some t11 ∧
      At t11 2632 (atFacts P L g d 2632) := by
    seg_fp h10 using
      try wg2_values
      all_goals first
        | norm_bits [hsite0, hsite1, hbr1, or_false, false_or]
        | wg2_close [hsite0, hsite1, hbr1, or_false, false_or]
  obtain ⟨t12, hr12, h12⟩ : ∃ t12, run kernel asms L g 1 t11 = some t12 ∧
      At t12 2633 (atFacts P L g d 2633) := by
    seg_fp h11 using
      try wg2_values
      all_goals first
        | exact shr31_value hbr1
        | norm_bits [hbr1]
  obtain ⟨t13, hr13, h13⟩ : ∃ t13, run kernel asms L g 1 t12 = some t13 ∧
      At t13 2634 (atFacts P L g d 2634) := by
    seg_fp h12 using
      try wg2_values
      all_goals first
        | norm_bits []
        | wg2_close []
  obtain ⟨t14, hr14, h14⟩ : ∃ t14, run kernel asms L g 1 t13 = some t14 ∧
      At t14 2635 (atFacts P L g d 2635) := by
    seg_fp h13 using
      try wg2_values
      all_goals first
        | norm_bits [hbr1]
        | wg2_close [hbr1]
  obtain ⟨t15, hr15, h15⟩ : ∃ t15, run kernel asms L g 1 t14 = some t15 ∧
      At t15 2636 (atFacts P L g d 2636) := by
    seg_fp h14 using
      try wg2_values
      all_goals first
        | exact and_neg64_ceil (x := d.len1) (by omega)
        | norm_bits [hbr1]
  obtain ⟨t16, hr16, h16⟩ : ∃ t16, run kernel asms L g 1 t15 = some t16 ∧
      At t16 2637 (atFacts P L g d 2637) := by
    seg_fp h15 using
      try wg2_values
      all_goals first
        | exact max64_value (x := ceilToMultiple d.len0 topkBlock) hceil0
        | norm_bits [hceil0]
  obtain ⟨t17, hr17, h17⟩ : ∃ t17, run kernel asms L g 1 t16 = some t17 ∧
      At t17 2638 (atFacts P L g d 2638) := by
    seg_fp h16 using
      try wg2_values
      all_goals first
        | norm_bits [hbr1, hborg]
        | wg2_close [hbr1, hborg]
  obtain ⟨t18, hr18, h18⟩ : ∃ t18, run kernel asms L g 1 t17 = some t18 ∧
      At t18 2639 (atFacts P L g d 2639) := by
    seg_fp h17 using
      try wg2_values
      all_goals first
        | exact sub_ceil_value (by omega) hceil1
        | norm_bits [hbr1, hceil1]
  obtain ⟨t19, hr19, h19⟩ : ∃ t19, run kernel asms L g 1 t18 = some t19 ∧
      At t19 2640 (atFacts P L g d 2640) := by
    seg_fp h18 using
      try wg2_values
      all_goals first
        | norm_bits [hbr1, hborg, hceil1, hpad]
        | wg2_close [hbr1, hborg, hceil1, hpad]
  obtain ⟨t20, hr20, h20⟩ : ∃ t20, run kernel asms L g 1 t19 = some t20 ∧
      At t20 2641 (atFacts P L g d 2641) := by
    seg_fp h19 using
      try wg2_values
      all_goals first
        | norm_bits [hshared, sb, b32]
        | wg2_close [hshared, sb, b32]
  obtain ⟨t21, hr21, h21⟩ : ∃ t21, run kernel asms L g 1 t20 = some t21 ∧
      At t21 2642 (atFacts P L g d 2642) := by
    seg_fp h20 using
      try wg2_values
      all_goals first
        | exact addr_eq (x := L.sharedBase) (c := 222784) (off := L.sharedBase + 222784)
            rfl (by omega) (by have := sharedBase_lt hpre; omega)
        | norm_bits [hshared, sb, b32]
  obtain ⟨t22, hr22, h22⟩ : ∃ t22, run kernel asms L g 2 t21 = some t22 ∧
      At t22 2644 (atFacts P L g d 2644) := by
    seg_fp h21 using
      try wg2_values
      all_goals first
        | norm_bits [hpar]
        | wg2_close []
  exact ⟨t22, by simpa using run_comp (run_comp (run_comp (run_comp (run_comp (run_comp
    (run_comp (run_comp hr11 hr12) hr13) hr14) hr15) hr16) hr17) hr18) (by
      simpa using run_comp (run_comp (run_comp hr19 hr20) hr21) hr22), h22⟩

/-- **The main-cache count's ceiling**: from the two pointers' null tests (pc 2617) to the extra
pointer's test (pc 2627), when the main-cache length pointer is absent. The branch at 2617 skips
the `.nc` read, and the main cache's `ku::ceil` runs instead (pcs 2621-2626). -/
theorem start_ceil0 {mem0 : Mem0} (hpre : Pre P L mem0) {hb0 : P.topkLenBase = none}
    {hbatch : eOf L g < P.b} {hsite0 : (init P L g).site ≠ .lenOrig} {t : TState}
    (h8 : At t 2617 (atFacts P L g (init P L g) 2617)) :
    ∃ t', run kernel asms L g 7 t = some t' ∧
      At t' 2627 (atFacts P L g (init P L g) 2627) := by
  have hlen0 : (init P L g).len0 = P.topk := by
    have hp := hpre.paramTopkLen
    rw [hb0] at hp
    exact hp.2 (eOf L g) hbatch
  have hbr : (init P L g).len0 + 63 < 2 ^ 31 := by
    rw [hlen0]
    exact hpre.topkAdd63Lt
  have hp131 : (131, Value.pred (Thread.ptrIsNull L 80)) ∈
      atFacts P L g (init P L g) 2617 := by
    have hm := mem_factsFrom (live := (Flow.live 2617).filter (fun r => tracked.contains r))
      (val := valueOf P L g (init P L g)) (by decide +kernel : 131 ∈
        (Flow.live 2617).filter (fun r => tracked.contains r))
    simpa [atFacts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using hm
  obtain ⟨t10, hr10, h10⟩ := run_bra_to (pc := 2617) (target := 2621) (p := 131)
    (pick := Thread.ptrIsNull L 80) Flow.code_2617 h8 hp131
    (b := 2621) (by rw [ptrIsNull_80_none hpre hb0]; rfl)
    (atFacts_sub (pc := 2621) (pc' := 2617) (live_sub (by decide +kernel)))
  obtain ⟨t11, hr11, h11⟩ := seg_mainCeil hsite0 hbr t10 h10
  exact ⟨t11, run_comp hr10 hr11, h11⟩

/-- **The entry run to the `extra_topk_length` read**: from the prologue's hand-off at pc 2607
to the `.nc` load of pc 2630, when the main-cache length pointer is absent and the extra one is
present. -/
theorem start_lenExtra {mem0 : Mem0} (hpre : Pre P L mem0) {y : Nat} (hb0 : P.topkLenBase = none)
    (hb1 : P.extraTopkLenBase = some y) {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g) := by
  have hsite : (init P L g).site = .lenExtra := by simp [init, firstSite, hb0, hb1]
  have hsite0 : (init P L g).site ≠ .lenOrig := by rw [hsite]; exact fun h => nomatch h
  have hlen0eq : (init P L g).len0 = P.topk := by
    have hp := hpre.paramTopkLen
    rw [hb0] at hp
    exact hp.2 (eOf L g) hentry.batch
  have hv85 : paramElem 32 32 (paramNat L (param "0") 40 4) =
      valueOf P L g (init P L g) 2985 := by
    rw [param_topk32 hpre]
    wg2_values
    simp [hsite, hlen0eq]
  have hv86 : paramElem 32 32 (paramNat L (param "0") 120 4) =
      valueOf P L g (init P L g) 2986 := by
    rw [param_extra32 hpre]
    wg2_values
    simp [hsite]
  obtain ⟨t8, hr8, h8⟩ := start_prefix hpre hentry (init P L g) hv85 hv86
  obtain ⟨t9, hr9, h9⟩ := start_ceil0 (g := g) (mem0 := mem0) hpre (hb0 := hb0)
    (hbatch := hentry.batch) (hsite0 := hsite0) h8
  obtain ⟨t11, hr11, h11⟩ := seg_extraLenAddr hpre hb1 t9 h9
  exact ⟨t11, run_rtg (run_comp (run_comp hr8 hr9) hr11),
    AtD.of_facts (d := init P L g) (pc := 2630) (hpc := by rw [hsite]; rfl)
      (hsub := by simp [Site.sub, hsite]) (hacc := by simp [accAt, hsite]) h11
      (by simp [payloadFacts, hsite]),
    init_inv hpre g hentry.batch⟩

/-- **The entry run to the `bar_q_utccp` wait**: from the prologue's hand-off at pc 2607 to the
first wait of pc 2644, when both length pointers are absent. The two null tests skip the `.nc`
reads, and both caches' `ku::ceil` computations, the padded total and the wait's three operands
run in between (pcs 2621-2643). -/
theorem start_none {mem0 : Mem0} (hpre : Pre P L mem0) (hb0 : P.topkLenBase = none)
    (hb1 : P.extraTopkLenBase = none) {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g) := by
  have hsite : (init P L g).site = .qUtccp := by simp [init, firstSite, hb0, hb1]
  have hsite0 : (init P L g).site ≠ .lenOrig := by rw [hsite]; exact fun h => nomatch h
  have hsite1 : (init P L g).site ≠ .lenExtra := by rw [hsite]; exact fun h => nomatch h
  have hlen0eq : (init P L g).len0 = P.topk := by
    have hp := hpre.paramTopkLen
    rw [hb0] at hp
    exact hp.2 (eOf L g) hentry.batch
  have hlen1eq : (init P L g).len1 = P.extra_topk := by
    have hp := hpre.paramExtraTopkLen
    rw [hb1] at hp
    exact hp.2 (eOf L g) hentry.batch
  have hv85 : paramElem 32 32 (paramNat L (param "0") 40 4) =
      valueOf P L g (init P L g) 2985 := by
    rw [param_topk32 hpre]
    wg2_values
    simp [hsite, hlen0eq]
  have hv86 : paramElem 32 32 (paramNat L (param "0") 120 4) =
      valueOf P L g (init P L g) 2986 := by
    rw [param_extra32 hpre]
    wg2_values
    simp [hsite, hlen1eq]
  obtain ⟨t8, hr8, h8⟩ := start_prefix hpre hentry (init P L g) hv85 hv86
  obtain ⟨t9, hr9, h9⟩ := start_ceil0 (g := g) (mem0 := mem0) hpre (hb0 := hb0)
    (hbatch := hentry.batch) (hsite0 := hsite0) h8
  obtain ⟨t10, hr10, h10⟩ := seg_skipExtraLen hpre hb1 t9 h9
  obtain ⟨t11, hr11, h11⟩ := seg_extraCeil hpre (init_inv hpre g hentry.batch) hsite rfl t10 h10
  exact ⟨t11, run_rtg (run_comp (run_comp (run_comp hr8 hr9) hr10) hr11),
    AtD.of_facts (d := init P L g) (pc := 2644) (hpc := by rw [hsite]; rfl)
      (hsub := by simp [Site.sub, hsite]) (hacc := by simp [accAt, hsite]) h11
      (by simp [payloadFacts, hsite]),
    init_inv hpre g hentry.batch⟩

/-- **The entry run from the prologue's hand-off to the role's first site**, in all three cases
of the two length pointers: the `topk_length` read, the `extra_topk_length` read, or (both
absent) straight to the `bar_q_utccp` wait. -/
theorem start_all {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g) := by
  cases h0 : P.topkLenBase with
  | none =>
    cases h1 : P.extraTopkLenBase with
    | none => exact start_none hpre h0 h1 hentry
    | some y => exact start_lenExtra hpre h0 h1 hentry
  | some x => exact start_lenOrig hpre h0 hentry

/-- The two optional runtime lengths load one scalar into their parameter register. -/
def runtimeLenSite (orig : Bool) : Site := if orig then .lenOrig else .lenExtra

def runtimeLenDest (orig : Bool) : Nat := if orig then 2985 else 2986

def runtimeLenBase (orig : Bool) : Nat := if orig then 3833 else 3835

def runtimeLenLoad (orig : Bool) : MemAccess where
  kind := .load
  space := some .global
  sem := .weak
  elem := .int .s 32
  nc := true
  addr := ⟨.reg (runtimeLenBase orig) 64, 0⟩
  dsts := [some (runtimeLenDest orig)]

theorem runtimeLenLoad_code (orig : Bool) :
    kernel.code[(runtimeLenSite orig).pc]? = some ⟨none, .mem (runtimeLenLoad orig)⟩ := by
  cases orig
  · exact Flow.code_2630
  · exact Flow.code_2620

theorem fires_runtimeLen {d : D} {orig : Bool} {t u : TState} {e : Event}
    (hd : d.site = runtimeLenSite orig) (hat : AtD P L g d t)
    (hf : Fires d.site.pc (eventTmpl asms L g t (.mem (runtimeLenLoad orig))) e (some u)) :
    ∃ loc bs, e = ⟨d.site.pc, .nc loc bs⟩ ∧ u = afterLoad t (runtimeLenLoad orig).regs bs := by
  have hn : asms.any (·.ncLoads t.pc) = true := by rw [hat.1, hd]; cases orig <;> decide +kernel
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := runtimeLenBase orig) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  unfold loadTmpl at hf
  split at hf
  · simp only [Fires] at hf
    exact absurd hf.2 (by simp)
  · have hc : (runtimeLenLoad orig).nc = true := rfl
    rw [hc] at hf
    rw [ite_eq_left (show Space.global = Space.global ∧ _ from ⟨rfl, hn⟩)] at hf
    obtain ⟨bs, -, he, hu⟩ := hf
    exact ⟨_, bs, he, Option.some.inj hu⟩

theorem runtimeLen_live (orig : Bool) :
    ∀ reg ∈ Flow.live ((runtimeLenSite orig).pc + 1),
      reg ∈ [runtimeLenDest orig] ∨ reg ∈ Flow.live (runtimeLenSite orig).pc := by
  cases orig <;> exact live_step (by decide +kernel)

theorem afterRuntimeLen_facts {d d' : D} {orig : Bool} {t : TState} {bs : List (Option Byte)}
    {value : Value} (hd : d.site = runtimeLenSite orig) (hat : AtD P L g d t)
    (hv : rebuild 3 bs = .ok value) (hwrite : value = valueOf P L g d' (runtimeLenDest orig))
    (hframe : ∀ reg ∈ (Flow.live ((runtimeLenSite orig).pc + 1)).filter tracked.contains,
      reg ≠ runtimeLenDest orig → valueOf P L g d' reg = valueOf P L g d reg) :
    At (afterLoad t (runtimeLenLoad orig).regs bs) ((runtimeLenSite orig).pc + 1)
      (atFacts P L g d' ((runtimeLenSite orig).pc + 1)) := by
  have hsub : t.sub = 0 := by rw [hat.2.1, hd]; cases orig <;> rfl
  have hacc : t.acc = [] := by rw [hat.2.2.1, accAt, hd]; cases orig <;> rfl
  have he : afterLoad t (runtimeLenLoad orig).regs bs =
      PTX.next (setReg t (runtimeLenDest orig) value) := by
    rw [afterLoad, hv, hsub, hacc]
    simp [runtimeLenLoad, MemAccess.regs, setRegs, hsub, hacc, PTX.next, setReg]
  rw [he]
  refine ⟨?_, hsub, hacc, hat.2.2.2.1, holds_of_pointwise ?_⟩
  · change t.pc + 1 = (runtimeLenSite orig).pc + 1
    rw [hat.1, hd]
  · intro reg hm
    by_cases hreg : reg = runtimeLenDest orig
    · subst reg
      simp [PTX.next, setReg, hwrite]
    · have hmem := List.mem_filter.mp hm
      have hr : reg ∈ Flow.live (runtimeLenSite orig).pc := by
        rcases runtimeLen_live orig reg hmem.1 with heq | hr
        · exact (hreg (List.mem_singleton.mp heq)).elim
        · exact hr
      have hr' : reg ∈ (Flow.live d.site.pc).filter tracked.contains := by
        rw [hd]
        exact List.mem_filter.mpr ⟨hr, hmem.2⟩
      simp [PTX.next, setReg, Function.update_of_ne hreg, hframe reg hm hreg, hat.reg hr']
theorem lenNext_inv {mem0 : Mem0} (hpre : Pre P L mem0) (hb : eOf L g < P.b) {site : Site}
    (hs : PayloadOk { init P L g with site := site }) :
    Inv P L g { init P L g with site := site } := by
  have h := init_inv hpre g hb
  exact ⟨h.bufLt, h.parLt, h.bufBlock, h.parBlock, h.len0, h.len1, h.block, h.extra,
    h.groupLt, h.idxLt, h.rawFit, h.scaleFit, h.tileFit, fun _ => rfl, h.lenLt, h.batch, hs⟩

theorem lenOrigNext_inv {mem0 : Mem0} (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    : Inv P L g (lenOrigNext P L g) := by
  apply lenNext_inv hpre hb
  split <;> trivial

theorem lenExtraNext_inv {mem0 : Mem0} (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    : Inv P L g (lenExtraNext P L g) :=
  lenNext_inv hpre hb trivial

theorem afterLenOrig_facts {mem0 : Mem0} {d : D} {t : TState} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hd : d.site = .lenOrig) (hat : AtD P L g d t) (hinv : Inv P L g d)
    (hv : rebuild 3 bs = .ok (b32 (P.topkLen (eOf L g)))) :
    At (afterLoad t (runtimeLenLoad true).regs bs) 2621
      (atFacts P L g (lenOrigNext P L g) 2621) := by
  apply afterRuntimeLen_facts (orig := true) hd hat hv
  · cases hb : P.extraTopkLenBase <;>
      simp [lenOrigNext, hb, init, runtimeLenDest, valueOf, table, PTX.Flow.lookupLit]
  · intro reg hmem hne
    have hm := (List.mem_filter.mp hmem).1
    change reg ∈ Flow.live 2621 at hm
    rw [show Flow.live 2621 = [460, 461, 512, 513, 2985, 2986, 3018] by decide +kernel] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (hne rfl).elim
    · cases hb : P.extraTopkLenBase with
      | none =>
        have he := hpre.paramExtraTopkLen
        rw [hb] at he
        simp [lenOrigNext, hb, init, valueOf, table, hd, PTX.Flow.lookupLit, he.2 _ hinv.batch]
      | some ptr =>
        simp [lenOrigNext, hb, init, valueOf, table, hd, PTX.Flow.lookupLit]
    · rfl

theorem afterLenExtra_facts {d : D} {t : TState} {bs : List (Option Byte)} (hd : d.site = .lenExtra)
    (hat : AtD P L g d t) (hinv : Inv P L g d)
    (hv : rebuild 3 bs = .ok (b32 (P.extraTopkLen (eOf L g)))) :
    At (afterLoad t (runtimeLenLoad false).regs bs) 2631
      (atFacts P L g (lenExtraNext P L g) 2631) := by
  apply afterRuntimeLen_facts (orig := false) hd hat hv
  · simp [lenExtraNext, init, runtimeLenDest, valueOf, table, PTX.Flow.lookupLit]
  · intro reg hmem hne
    have hm := (List.mem_filter.mp hmem).1
    change reg ∈ Flow.live 2631 at hm
    rw [show Flow.live 2631 = [461, 512, 513, 514, 2986] by decide +kernel] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · simp [lenExtraNext, init, valueOf, table, PTX.Flow.lookupLit, hinv.len0]
    · exact (hne rfl).elim
/-- The main length read flows through its ceiling and the optional extra length's null test. -/
theorem stepAt_lenOrig {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .lenOrig) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (runtimeLenLoad true)⟩ := by
      rw [hd]
      exact runtimeLenLoad_code true
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨loc, bs, he, hu⟩ := fires_runtimeLen (orig := true) hd hat hf
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b32 (P.topkLen (eOf L g)))
    · let d' := lenOrigNext P L g
      have hnew : Inv P L g d' := lenOrigNext_inv hpre hinv.batch
      have hstart := afterLenOrig_facts hpre hd hat hinv hv
      rw [← hu] at hstart
      have h63 : d'.len0 + 63 < 2 ^ 31 := by
        have h := topkLen_le hpre hinv.batch
        have hb := hpre.topkAdd63Lt
        rw [hnew.len0]
        omega
      have hnon : d'.site ≠ .lenOrig := by
        cases hb : P.extraTopkLenBase <;> simp [d', lenOrigNext, hb]
      obtain ⟨u1, hr1, h1⟩ := seg_mainCeil hnon h63 u hstart
      cases hb : P.extraTopkLenBase with
      | none =>
        have hq : d'.site = .qUtccp := by simp [d', lenOrigNext, hb]
        obtain ⟨u2, hr2, h2⟩ := seg_skipExtraLen hpre hb u1 h1
        obtain ⟨u3, hr3, h3⟩ := seg_extraCeil hpre hnew hq rfl u2 h2
        refine Or.inl (Or.inr ⟨d', u3, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3), ?_⟩)
        · simp [next, nextSite, hd, hv, d']
        · change AtD P L g d' u3 ∧ Inv P L g d'
          exact ⟨AtD.of_facts (d := d') (by rw [hq]; rfl) (by rw [hq]; rfl)
            (by simp [accAt, hq]) h3 (by simp [payloadFacts, hq]), hnew⟩
      | some ptr =>
        have hq : d'.site = .lenExtra := by simp [d', lenOrigNext, hb]
        obtain ⟨u2, hr2, h2⟩ := seg_extraLenAddr hpre hb u1 h1
        refine Or.inl (Or.inr ⟨d', u2, ?_, run_rtg (run_comp hr1 hr2), ?_⟩)
        · simp [next, nextSite, hd, hv, d']
        · change AtD P L g d' u2 ∧ Inv P L g d'
          exact ⟨AtD.of_facts (d := d') (by rw [hq]; rfl) (by rw [hq]; rfl)
            (by simp [accAt, hq]) h2 (by simp [payloadFacts, hq]), hnew⟩
    · refine Or.inl (Or.inl ?_)
      cases hr : rebuild 3 bs with
      | error f => simp [next, nextSite, hd, hr]
      | ok v =>
        have hne : v ≠ b32 (P.topkLen (eOf L g)) := fun h => hv (hr.trans (congrArg Except.ok h))
        simp [next, nextSite, hd, hr, hne]

/-- After the extra length read, both padded counts are ready for the first query wait. -/
theorem stepAt_lenExtra {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .lenExtra) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t e u} ins hat hinv hc hf => by
    have hc' : kernel.code[d.site.pc]? = some ⟨none, .mem (runtimeLenLoad false)⟩ := by
      rw [hd]
      exact runtimeLenLoad_code false
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    obtain ⟨loc, bs, he, hu⟩ := fires_runtimeLen (orig := false) hd hat hf
    rw [he]
    by_cases hv : rebuild 3 bs = .ok (b32 (P.extraTopkLen (eOf L g)))
    · let d' := lenExtraNext P L g
      have hnew : Inv P L g d' := lenExtraNext_inv hpre hinv.batch
      have hstart := afterLenExtra_facts hd hat hinv hv
      rw [← hu] at hstart
      obtain ⟨u1, hr1, h1⟩ := seg_extraCeil hpre hnew rfl rfl u hstart
      refine Or.inl (Or.inr ⟨d', u1, ?_, run_rtg hr1, ?_⟩)
      · simp [next, nextSite, hd, hv, d']
      · change AtD P L g d' u1 ∧ Inv P L g d'
        exact ⟨AtD.of_facts (d := d') rfl rfl rfl h1, hnew⟩
    · refine Or.inl (Or.inl ?_)
      cases hr : rebuild 3 bs with
      | error f => simp [next, nextSite, hd, hr]
      | ok v =>
        have hne : v ≠ b32 (P.extraTopkLen (eOf L g)) :=
          fun h => hv (hr.trans (congrArg Except.ok h))
        simp [next, nextSite, hd, hr, hne]

/-- The fence, arrivals, waits and named barrier steps. -/
theorem steps_known {mem0 : Mem0} (hpre : Pre P L mem0) (d : D)
    (hd : d.site = .fence ∨ d.site = .ready ∨ d.site = .barrier ∨
      d.site = .rawReady ∨ d.site = .svDone ∨ d.site = .qUtccp ∨ d.site = .free) :
    (code P L g).StepAt d := by
  rcases hd with hd | hd | hd | hd | hd | hd | hd
  · exact stepAt_fence hpre d hd
  · exact stepAt_ready hpre d hd
  · exact stepAt_barrier hpre d hd
  · exact stepAt_of P L g d fun _ hat hinv hc hf => step_rawReady hpre d hd hat hinv hc hf
  · exact stepAt_of P L g d fun _ hat hinv hc hf => step_svDone hpre d hd hat hinv hc hf
  · exact stepAt_of P L g d fun _ hat hinv hc hf => step_qUtccp hpre d hd hat hinv hc hf
  · exact stepAt_of P L g d fun _ hat hinv hc hf => step_free hpre d hd hat hinv hc hf

/-- Every event site of the dequantizer preserves its thread invariant. -/
theorem steps_all {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) : (code P L g).StepAt d := by
  cases hd : d.site
  case lenOrig => exact stepAt_lenOrig hpre d hd
  case lenExtra => exact stepAt_lenExtra hpre d hd
  case scale => exact stepAt_scale hpre d hd
  case raw => exact stepAt_raw hpre d hd
  case store => exact stepAt_store hpre d hd
  all_goals exact steps_known hpre d (by simp [hd])

/-- Soundness of the dequantizer from its hand-off. -/
theorem sound {mem0 : Mem0} (hpre : Pre P L mem0) :
    Sound P L g :=
  ⟨fun _ _ hp he => start_all hp he, steps_all hpre⟩

/-- The shared launch prefix and the dequantizer use the same machine interface. -/
abbrev launchPrologue (L : Launch) (g : Nat) :=
  _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.code L g

abbrev LaunchSite := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Site

def launchNext (P : Params) (L : Launch) (g : Nat) :
    Sum LaunchSite D → Event → Option (Option (Sum LaunchSite D))
  | .inl site, e =>
    match (launchPrologue L g).next site e with
    | none => none
    | some (some site') => some (some (.inl site'))
    | some none => if site = .handoff 2 then some (some (.inr (init P L g))) else some none
  | .inr d, e => ((code P L g).next d e).map (Option.map Sum.inr)

/-- The whole launch for a dequantizer thread, including the shared prologue events. -/
def launchCode (P : Params) (L : Launch) (g : Nat) : Code kernel asms L g where
  D := Sum LaunchSite D
  init := .inl (launchPrologue L g).init
  pc := Sum.elim (launchPrologue L g).pc (code P L g).pc
  sub := Sum.elim (launchPrologue L g).sub (code P L g).sub
  acc := Sum.elim (launchPrologue L g).acc (code P L g).acc
  facts := Sum.elim (launchPrologue L g).facts (code P L g).facts
  inv := Sum.elim (launchPrologue L g).inv (code P L g).inv
  next := launchNext P L g

/-- The dequantizer thread machine starts in the empty state and runs the shared prologue. -/
def machine (P : Params) (L : Launch) (g : Nat) : Machine kernel asms L g :=
  (launchCode P L g).toMachine

end Wg2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
