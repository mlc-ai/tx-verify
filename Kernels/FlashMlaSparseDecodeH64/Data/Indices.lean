-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Data.List.Range
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Sparse-index arithmetic of the FlashMLA SM100 sparse decode head64 kernel

`deepseek-ai/FlashMLA` commit `395cb3afbb331fef7b1b21e9340861b9436b42d8`,
`csrc/cuda_kernels/sm100/decode/sparse/head64/kernel.cuh`, turns one query row's sparse index
array into TMA gather coordinates: the index warp (`kernel.cuh:535-616`) reads a block's indices
as one `int2` per lane of 32 (`kernel.cuh:550-557`), and `process_one_block`
(`kernel.cuh:558-595`) turns each of the two indices into a validity flag and an interleaved TMA
row (`kernel.cuh:577-585`). This module models that arithmetic as pure functions of `Nat`/`Int`
values, for `Spec.lean` and `Post` to name. It carries no memory or execution semantics.

The per-row index budget comes from `run_main_loop` (`kernel.cuh:121-124,132,142`): the main
cache's runtime length `len` is padded to `origPadded len` and split into `numOrigBlocks len`
blocks, the extra cache's runtime length `extraLen` contributes `ceilDiv extraLen 64` blocks, and
`totalBlocks` is the total. A block `b` with `numOrigBlocks len ≤ b` (`isExtraBlock`) is read from
the extra cache, and its slots are rebased on `numOrigBlocks len` (`kernel.cuh:555,563`). A slot
is valid exactly when its index is not the marker `-1` and its position is below the length of
its own cache (`kernel.cuh:582`).

The model reads the C expressions at the values `Pre` allows: an index is `-1` or a nonnegative
token index below `num_blocks * page_block_size`, so `Int.toNat` agrees with the C's
`(unsigned int)` cast. The marker `-1` would divide to a large unsigned number in C
(`kernel.cuh:570-571`) and to `0` here; `kvSlotValid` rejects it, so no position or row is ever
formed from it.

Only the no-split V4.1 instance (`v41_h64_no_split`,
`Config{ModelType::V41, ModelType::V41, false}`) is in scope: both caches store 528-byte V4.1
tokens (`kv_cache_format.h:5-20`), and the host guarantees `topk % 64 = 0` and
`extra_topk % 64 = 0` (`kernel.cuh:672-673`). The lengths are the runtime ones (`topk_length` /
`extra_topk_length` when those pointers are non-null, the constants otherwise).
-/

namespace PTX.Kernels.FlashMlaSparseDecodeH64

/-! ## Constants and the padded block budget -/

/-- `B_TOPK` (`config.h:48`): the number of sparse indices one block covers. -/
def topkBlock : Nat := 64

/-- The lanes of the warp that transforms indices (`kernel.cuh:50,535`). -/
def indexLanes : Nat := 32

/-- Indices per lane: each lane loads one `int2` (`kernel.cuh:553,555`). -/
def indicesPerLane : Nat := 2

/-- `KVCacheFormat<V41>::BYTES_PER_TOKEN` (`kv_cache_format.h:19`): 512 e4m3 bytes and 16 ue8m0
scale bytes. `kernel.cuh:540-541` divides each cache's block stride by its format's token width;
both caches of the no-split instance are V4.1, so both divisions use 528. -/
def bytesPerToken : Nat := 528

/-- `⌈n / d⌉`: the number of `d`-sized blocks that hold `n` slots. -/
def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

/-- `ku::ceil(a, b) = (a + b - 1) / b * b` (`kerutils/common/common.h:36-39`): `n` rounded up to
a whole number of blocks, a length rather than a count. -/
def ceilToMultiple (n d : Nat) : Nat := (n + d - 1) / d * d

theorem ceilToMultiple_eq_ceilDiv_mul (n d : Nat) : ceilToMultiple n d = ceilDiv n d * d := rfl

/-- `orig_topk_padded = max(ku::ceil(topk_length, B_TOPK), B_TOPK)` (`kernel.cuh:122`): the main
cache's index budget of one query row, a whole number of blocks and at least one. -/
def origPadded (len : Nat) : Nat := max (ceilToMultiple len topkBlock) topkBlock

/-- `orig_topk_padded / B_TOPK` (`kernel.cuh:142`): the number of main-cache blocks. -/
def numOrigBlocks (len : Nat) : Nat := origPadded len / topkBlock

/-- `total_topk_padded / B_TOPK` (`kernel.cuh:124,132`): the number of blocks of both caches. -/
def totalBlocks (len extraLen : Nat) : Nat :=
  (origPadded len + ceilToMultiple extraLen topkBlock) / topkBlock

/-! ## Slots, their validity, and the token row -/

/-- `block_idx >= num_orig_kv_blocks` (`kv_cache_utils.cuh:12-27`, `kernel.cuh:555,563`): whether
block `b` of a query row belongs to the extra cache. -/
def isExtraBlock (b len : Nat) : Bool := decide (numOrigBlocks len ≤ b)

/-- The position of slot `(b, lane, i)` in the index array of its own cache: `abs_pos + i` of
`kernel.cuh:563`, where an extra block is rebased on `num_orig_kv_blocks` (`kernel.cuh:555`). -/
def slotPos (len : Nat) (b lane i : Nat) : Nat :=
  if isExtraBlock b len then (b - numOrigBlocks len) * topkBlock + lane * 2 + i
  else b * topkBlock + lane * 2 + i

/-- The index budget a block's slots are checked against:
`IS_EXTRA_BLOCK ? extra_topk_length : topk_length` (`kernel.cuh:582`). -/
def slotLen (len extraLen : Nat) (b : Nat) : Nat :=
  if isExtraBlock b len then extraLen else len

/-- `cur_idx != -1 && (abs_pos+i < (IS_EXTRA_BLOCK ? extra_topk_length : topk_length))`
(`kernel.cuh:582`): whether a slot holds a KV token; `-1` is the invalid marker. -/
def kvSlotValid (len extraLen : Nat) (b lane i : Nat) (idx : Int) : Bool :=
  idx != -1 && decide (slotPos len b lane i < slotLen len extraLen b)

/-- `(unsigned int)cur_idx / cur_block_size` (`kernel.cuh:570`): the cache block of a token. -/
def blockOf (idx : Int) (page : Nat) : Nat := idx.toNat / page

/-- `(unsigned int)cur_idx % cur_block_size` (`kernel.cuh:571`): the token's row in its block. -/
def inBlock (idx : Int) (page : Nat) : Nat := idx.toNat % page

/-- The TMA gather coordinate of a valid token (`kernel.cuh:539-541,561,584`):
`block_idx * (stride_kv_block / TMA_K_STRIDE) + idx_in_block * 1`, where
`TMA_K_STRIDE = BYTES_PER_TOKEN` (`config.h:46`). -/
def rowOf (blockStride page : Nat) (idx : Int) : Nat :=
  blockOf idx page * (blockStride / bytesPerToken) + inBlock idx page

/-- The two tensormaps of the kernel (`kernel.cuh:513`): the main and the extra KV cache. -/
inductive Cache where
  | orig
  | extra
  deriving DecidableEq, Repr

/-- One sparse-index slot: a `(block, lane, pair)` position of the index warp with the index it
read and the TMA row of that token in `cache`. `pair` selects the `.x`/`.y` half of the lane's
`int2`. -/
structure Slot where
  cache : Cache
  block : Nat
  lane : Nat
  pair : Nat
  index : Int
  row : Nat
  deriving DecidableEq, Repr

/-- The cache a block reads. -/
def slotCache (len b : Nat) : Cache := if isExtraBlock b len then .extra else .orig

/-- `cur_block_size = IS_EXTRA_BLOCK ? extra_page_block_size : page_block_size`
(`kernel.cuh:560`). -/
def slotPage (len origPage extraPage b : Nat) : Nat :=
  if isExtraBlock b len then extraPage else origPage

/-- `cur_tma_coords_step_per_block = IS_EXTRA_BLOCK ? stride_extra_kv_block :
stride_kv_block`, the token width being `bytesPerToken` (`kernel.cuh:540-541,561`). -/
def slotBlockStride (len origStride extraStride b : Nat) : Nat :=
  if isExtraBlock b len then extraStride else origStride

/-- The index read for slot `(b, lane, i)` (`kernel.cuh:550-557`): from the extra array, rebased
on `num_orig_kv_blocks`, for an extra block, and from the main array otherwise. -/
def slotIndex (len : Nat) (indices extraIndices : Nat → Int) (b lane i : Nat) : Int :=
  if isExtraBlock b len then extraIndices (slotPos len b lane i)
  else indices (slotPos len b lane i)

/-- The slot at position `(b, lane, i)`: the cache tag, the index read, and the row that index
names in that cache's geometry. -/
def slotAt (len origPage extraPage origStride extraStride : Nat)
    (indices extraIndices : Nat → Int) (b lane i : Nat) : Slot where
  cache := slotCache len b
  block := b
  lane := lane
  pair := i
  index := slotIndex len indices extraIndices b lane i
  row := rowOf (slotBlockStride len origStride extraStride b)
    (slotPage len origPage extraPage b) (slotIndex len indices extraIndices b lane i)

/-- The valid slots of one query row, in enumeration order `(block, lane, pair)`: `Post` sums
over this list. `indices` and `extraIndices` are the row's index arrays as functions of the slot
position; a slot is kept when `kvSlotValid` accepts its index (`kernel.cuh:582`). -/
def validSlots (len extraLen origPage extraPage origStride extraStride : Nat)
    (indices extraIndices : Nat → Int) : List Slot :=
  (List.range (totalBlocks len extraLen)).flatMap fun b =>
    (List.range indexLanes).flatMap fun lane =>
      (List.range indicesPerLane).flatMap fun i =>
        if kvSlotValid len extraLen b lane i (slotIndex len indices extraIndices b lane i) then
          [slotAt len origPage extraPage origStride extraStride indices extraIndices b lane i]
        else []

/-! ## Padded block arithmetic -/

theorem le_ceilToMultiple {n d : Nat} (hd : 0 < d) : n ≤ ceilToMultiple n d := by
  have h := Nat.div_add_mod' (n + d - 1) d
  have hr := Nat.mod_lt (n + d - 1) hd
  unfold ceilToMultiple
  omega

theorem ceilToMultiple_mod (n d : Nat) : ceilToMultiple n d % d = 0 := by
  unfold ceilToMultiple
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left d _)

theorem ceilToMultiple_zero (d : Nat) : ceilToMultiple 0 d = 0 := by
  unfold ceilToMultiple
  cases d with
  | zero => rfl
  | succ d => simp

/-- The host guarantees a multiple of the block size for a length without a runtime override
(`topk % 64 = 0`, `extra_topk % 64 = 0`, `kernel.cuh:672-673`); such a length needs no padding.
-/
theorem ceilToMultiple_eq_self_of_dvd {n d : Nat} (hd : 0 < d) (h : d ∣ n) :
    ceilToMultiple n d = n := by
  obtain ⟨k, rfl⟩ := h
  unfold ceilToMultiple
  have hdiv : (d * k + d - 1) / d = k := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm k d]
      omega
    · rw [Nat.add_mul, one_mul, Nat.mul_comm k d]
      omega
  rw [hdiv, Nat.mul_comm]

theorem origPadded_pos (len : Nat) : 0 < origPadded len := by
  unfold origPadded
  exact lt_of_lt_of_le (by decide : (0 : Nat) < topkBlock) (Nat.le_max_right _ _)

theorem origPadded_zero : origPadded 0 = 64 := by
  unfold origPadded
  rw [ceilToMultiple_zero]
  simp [topkBlock]

theorem numOrigBlocks_zero : numOrigBlocks 0 = 1 := by
  unfold numOrigBlocks
  rw [origPadded_zero]
  decide

theorem origPadded_mod (len : Nat) : origPadded len % topkBlock = 0 := by
  unfold origPadded
  rcases Nat.le_total (ceilToMultiple len topkBlock) topkBlock with h | h
  · rw [Nat.max_eq_right h, Nat.mod_self]
  · rw [Nat.max_eq_left h, ceilToMultiple_mod]

theorem numOrigBlocks_mul (len : Nat) : numOrigBlocks len * topkBlock = origPadded len := by
  unfold numOrigBlocks
  exact Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr (origPadded_mod len))

theorem numOrigBlocks_pos (len : Nat) : 0 < numOrigBlocks len := by
  have h := numOrigBlocks_mul len
  rcases Nat.eq_zero_or_pos (numOrigBlocks len) with h0 | hpos
  · rw [h0, Nat.zero_mul] at h
    have := origPadded_pos len
    omega
  · exact hpos

/-- A length that is a positive multiple of the block size has no padded block of its own:
`max(ceil(len, 64), 64) = len`, the `topk_length`-absent case (`kernel.cuh:121-122`). -/
theorem origPadded_eq_self_of_dvd {len : Nat} (hpos : 0 < len) (h : topkBlock ∣ len) :
    origPadded len = len := by
  unfold origPadded
  rw [ceilToMultiple_eq_self_of_dvd (by decide : 0 < topkBlock) h]
  exact Nat.max_eq_left (Nat.le_of_dvd hpos h)

theorem totalBlocks_eq (len extraLen : Nat) :
    totalBlocks len extraLen =
      numOrigBlocks len + ceilToMultiple extraLen topkBlock / topkBlock := by
  unfold totalBlocks
  rw [← numOrigBlocks_mul len]
  rw [Nat.add_comm (numOrigBlocks len * topkBlock) (ceilToMultiple extraLen topkBlock)]
  rw [Nat.add_mul_div_right _ _ (by decide : 0 < topkBlock)]
  exact Nat.add_comm _ _

theorem numOrigBlocks_le_totalBlocks (len extraLen : Nat) :
    numOrigBlocks len ≤ totalBlocks len extraLen := by
  rw [totalBlocks_eq]
  exact Nat.le_add_right _ _

theorem totalBlocks_pos (len extraLen : Nat) : 0 < totalBlocks len extraLen :=
  lt_of_lt_of_le (numOrigBlocks_pos len) (numOrigBlocks_le_totalBlocks len extraLen)

/-! ## Slot validity -/

theorem isExtraBlock_eq_true_iff {len b : Nat} :
    isExtraBlock b len = true ↔ numOrigBlocks len ≤ b := by
  unfold isExtraBlock
  exact decide_eq_true_iff

theorem kvSlotValid_eq_true_iff {len extraLen b lane i : Nat} {idx : Int} :
    kvSlotValid len extraLen b lane i idx = true ↔
      idx ≠ -1 ∧ slotPos len b lane i < slotLen len extraLen b := by
  unfold kvSlotValid
  rw [Bool.and_eq_true, decide_eq_true_iff, bne_iff_ne]

/-- The position of a valid slot is below its own cache's index budget
(`kernel.cuh:582`): the `abs_pos+i < length` half of the validity condition. -/
theorem slotPos_lt_slotLen_of_kvSlotValid {len extraLen b lane i : Nat} {idx : Int}
    (h : kvSlotValid len extraLen b lane i idx = true) :
    slotPos len b lane i < slotLen len extraLen b :=
  (kvSlotValid_eq_true_iff.mp h).2

/-- A main-cache slot's position lies in the padded main budget `origPadded`
(`kernel.cuh:563`: `block_idx*B_TOPK + lane_idx*2 + i`). -/
theorem slotPos_lt_origPadded {len b lane i : Nat} (h : isExtraBlock b len = false)
    (hlane : lane < indexLanes) (hi : i < indicesPerLane) :
    slotPos len b lane i < origPadded len := by
  have htb : topkBlock = 64 := rfl
  have hlane' : lane < 32 := hlane
  have hi' : i < 2 := hi
  have hb : b < numOrigBlocks len := by
    have h' := h
    unfold isExtraBlock at h'
    rw [decide_eq_false_iff_not] at h'
    omega
  have hm : slotPos len b lane i = b * topkBlock + lane * 2 + i := by
    unfold slotPos
    rw [ite_eq_right (by simp [h])]
  rw [hm]
  have hmul := numOrigBlocks_mul len
  rw [htb] at hmul ⊢
  omega

/-- An extra-cache slot's position lies in the padded extra budget
(`kernel.cuh:555,563`: `(block_idx-num_orig)*B_TOPK + lane_idx*2 + i`). -/
theorem slotPos_lt_extraPadded {len extraLen b lane i : Nat}
    (h : isExtraBlock b len = true) (hB : b < totalBlocks len extraLen)
    (hlane : lane < indexLanes) (hi : i < indicesPerLane) :
    slotPos len b lane i < ceilToMultiple extraLen topkBlock := by
  have htb : topkBlock = 64 := rfl
  have hlane' : lane < 32 := hlane
  have hi' : i < 2 := hi
  have hle : numOrigBlocks len ≤ b := isExtraBlock_eq_true_iff.mp h
  have hm : slotPos len b lane i =
      (b - numOrigBlocks len) * topkBlock + lane * 2 + i := by
    unfold slotPos
    rw [ite_eq_left h]
  have hB' : b < numOrigBlocks len + ceilToMultiple extraLen topkBlock / topkBlock := by
    rw [← totalBlocks_eq]
    exact hB
  have hc : ceilToMultiple extraLen topkBlock / topkBlock * topkBlock
      = ceilToMultiple extraLen topkBlock :=
    Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr (ceilToMultiple_mod extraLen topkBlock))
  rw [hm, htb] at *
  omega

/-- With no main-cache tokens (`len = 0`) no main-cache slot is valid: every valid slot lies in
an extra block. `origPadded 0 = 64` keeps one block, whose 64 slots all fail `slotPos < 0`. -/
theorem kvSlotValid_origLen_zero_imp_isExtraBlock {extraLen b lane i : Nat} {idx : Int}
    (h : kvSlotValid 0 extraLen b lane i idx = true) : isExtraBlock b 0 = true := by
  by_contra hb
  have hb' : isExtraBlock b 0 = false := by
    cases h' : isExtraBlock b 0 <;> simp_all
  have hlt := slotPos_lt_slotLen_of_kvSlotValid h
  have hcond : ¬(isExtraBlock b 0 = true) := by simp [hb']
  simp only [slotLen, slotPos, ite_eq_right hcond] at hlt
  omega

/-! ## Token rows -/

/-- For a contiguous cache (`stride_kv_block = 528 * page_block_size`, the host layout) the TMA
row of a token is the token index itself. -/
theorem rowOf_contiguous (page : Nat) (idx : Int) :
    rowOf (bytesPerToken * page) page idx = idx.toNat := by
  have hstep : bytesPerToken * page / bytesPerToken = page := by
    unfold bytesPerToken
    rw [Nat.mul_comm]
    exact Nat.mul_div_left page (by decide)
  unfold rowOf blockOf inBlock
  rw [hstep]
  exact Nat.div_add_mod' idx.toNat page

/-! ## The summation domain -/

theorem mem_ite_singleton {α : Type} {c : Prop} [Decidable c] {x s : α} :
    s ∈ (if c then [x] else []) ↔ c ∧ s = x := by
  by_cases h : c <;> simp [h]

/-- Membership in `validSlots`: exactly the valid `(block, lane, pair)` positions with
`block < totalBlocks`, `lane < 32`, `pair < 2`, each carrying the index it read and its row. -/
theorem mem_validSlots {len extraLen origPage extraPage origStride extraStride : Nat}
    {indices extraIndices : Nat → Int} {s : Slot} :
    s ∈ validSlots len extraLen origPage extraPage origStride extraStride indices extraIndices ↔
      ∃ b lane i,
        b < totalBlocks len extraLen ∧ lane < indexLanes ∧ i < indicesPerLane ∧
          kvSlotValid len extraLen b lane i (slotIndex len indices extraIndices b lane i) = true ∧
          s = slotAt len origPage extraPage origStride extraStride indices extraIndices b lane i
  := by
  simp only [validSlots, List.mem_flatMap, List.mem_range, mem_ite_singleton]
  constructor
  · rintro ⟨b, hb, lane, hlane, i, hi, hv, hs⟩
    exact ⟨b, lane, i, hb, hlane, hi, hv, hs⟩
  · rintro ⟨b, lane, i, hb, hlane, hi, hv, hs⟩
    exact ⟨b, hb, lane, hlane, i, hi, hv, hs⟩

end PTX.Kernels.FlashMlaSparseDecodeH64
