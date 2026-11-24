-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Data.Indices
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.Code
public import Lemmas.Flow.Segment
public import Lemmas.Flow.SegChain
public import Lemmas.Flow.Events
public import Lemmas.Flow.Next
public import Lemmas.Flow.Async
public import Lemmas.Flow.Bar
public import Lemmas.Flow.Scalars
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.ParamObject
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.Vector
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.TensorIssue
public import Lemmas.Flow.TensorBox

@[expose] public section

/-! # `wg1Tma`: the raw-KV TMA producer of the FlashMLA sparse decode kernel

Warp 5 of warpgroup 1 (pcs 2162-2331, `kernel.cuh:505-535`, the "interleaved raw-data and scale
retrieval warp") fills the raw KV ring of the kernel from the paged e4m3 cache. The whole warp
runs the role's prefix; its elected lane (`cute::elect_one_sync`, pcs 2163-2169,
`kernel.cuh:512`) does the work, and the other lanes leave for the empty main loop at pc 2587
(`Roles.lean`, `elect_join`).

The elected lane

* reads its CTA's place in the grid (`%ctaid.y >= b` leaves at pc 2172) and the row's two runtime
  lengths (`ld.global.nc` at pcs 2181 and 2191, when their pointers are non-null), and derives the
  row's padded block counts (`origPadded`, `ceilToMultiple`, `Data/Indices`);
* waits for the index warp's `bar_valid_coord_ready[phase]` (pc 2234) and for the raw ring buffer
  to be free, `bar_raw_free[buf]` (pc 2245);
* loads the block's 64 `tma_coord` words from the ring slot, four at a time (the 16
  `ld.shared.v4.b32` at pcs 2250-2299), and issues 16 `cp.async.bulk.tensor.2d...tile::gather4`
  loads into `raw_quant[buf]` (pcs 2259-2303), four rows each (`Data/Sites.gather4Loads`); the KV
  descriptor is `param_1 + 768` for a main-cache block and `param_1 + 896` for an extra-cache
  block (the `selp` at pc 2248), and the loads complete on `bar_raw_ready[buf]` (register 696);
* arrives on `bar_raw_ready[buf]` with the 36864-byte transaction count of a raw block (pc 2305)
  and releases the index slot with `bar_valid_coord_free[phase]` (pc 2308);
* advances the two rings and repeats over the row's blocks (pcs 2309-2327), then passes the named
  barrier `barrier.sync 12, 384` (`everyone_sync`, pc 2330) and returns (pc 3611).

## The sites

The machine's states are the role's event instructions: the election, the two `.nc` length
loads, the four mbarrier polls, the 64 shared-load elements (16 `v4` loads, one state per
element, `Site.coord k j`), the 16 gather4 issues, the two arrivals, the named barrier and the
`ret`. The loads and issues alternate in the program's order — `load 0`, `load 1`, `issue 0`,
`load 2`, `issue 1`, …, `load 15`, `issue 14`, `issue 15` — which `afterCoord` and `afterIssue`
follow.

## The state and its invariant

`D` carries the block being produced, the two ring positions with their phase parities (the index
ring `phase`/`par` of `NUM_INDEX_BUFS = 4`, the raw ring `buf`/`rpar` of `NUM_BUFS = 2`), and the
row's two runtime lengths. `Inv` states that the ring positions and parities are the block's, that
the block is one of the row's padded blocks, and that the lengths are the row's (`Data/Indices`
supplies `numOrigBlocks` and `totalBlocks`); `table` gives every register the role tracks at a
site its value as a function of `D`:

* the shared addresses of the two ring slots and their mbarriers (`coordBase`, `validOff`,
  `readyOff`, `coordFreeOff`, `rawReadyOff`, `rawFreeOff` — the last four are the `Mbar` objects
  of `Proof/Protocol/Mbar.lean`), formed from the `wksp_buf` symbol at pcs 2201, 2229-2244;
* the raw ring destinations `rawBase buf + 2304 * k` (`raw_quant`'s 64 rows of
  `RAW_TOKEN_SMEM_STRIDE = 576` bytes, four rows per gather4, each destination 128-byte aligned);
* the gather4 coordinates: the index warp's `tma_coord` word of position `p` is `coordAt`, and
  `coordAt_rowOf` proves a valid slot's word is `Data/Indices.rowOf` of the slot's index in the
  block's cache geometry;
* the selected KV descriptor `param_1 + kvOff` and the cache-policy word.

## The entry interface

This role's machine starts at pc 2162, before its election initializer. Its `Entry` states the
thread is at pc 2162 with `%r2 = %ctaid.y` (460), `%rd1 = param_1`'s address (2990),
`%rd2 = param_0`'s address (2991) at the prologue's values, its warp index `%r6` is 5 and its
lane is `%r8`, and its CTA is a batch and a query of the grid. The prologue's and warpgroup-1
head's machines must supply this hand-off (`Proof/Thread/Prologue.lean` stops at pc 1842).

## Proof coverage

Proved here:

* the site vocabulary, the `eventPcs_ok`/`site_event` obligations (every site is an unguarded
  event instruction of the decoded program), and `issue_op`: every gather4 issue reads the KV map
  register 3049 and completes on barrier register 696 in mode `.fourRows`;
* the successor relation `next`, the invariant `Inv`, the register table, the machine `code`, and
  that the initial state satisfies the invariant (`init_inv`);
* the arithmetic bridges to `Data/Indices`: `coordAt_rowOf` for a valid slot and
  `coordAt_invalid` for the `-1` marker;
* the role's shadow objects: `mbar_adds`, `slot_scales` and `raw_dst_adds` read the mbarrier
  addresses, the ring scales and the raw destinations off the decoded additions, and
  `issueDst_aligned` proves each gather4 destination 128-byte aligned;
* the entry run: `start_of_entry`, the three local instructions from `Entry` to the election;
* `handoff_unelected`, which takes an unelected lane from the election to the idle role;
* `stepAt_elect`, which follows the elected lane's launch parameter reads and pointer tests to
  the first length site or the Q-copy poll;
* `stepAt_waitQ` and `stepAt_waitLast`, which retry failed polls and reach the next poll on
  success. The previous-store wait initializes both rings and their parities on success;
* `stepAt_waitCoord` and `stepAt_waitFree`, which retry failed ring polls. Success prepares the
  next poll or selects the KV map and computes the coordinate ring address;
* `fires_coord`, `stepAt_coordMid` and `stepAt_coordLast`, which identify each coordinate read's
  location, accumulate the first three words, write the vector registers on the fourth, and
  reach the next coordinate read or gather4 issue;
* `stepAt_issue` and `gather_issue_fields`, which verify each gather4 continuation and its
  published map address, destination, completion barrier, and 2304-byte transfer;
* `stepAt_coordFree`, which advances both rings after releasing the index slot and either
  resumes the loop or reaches the final named barrier;
* `stepAt_lenOrig` and `stepAt_lenExtra`, which verify the optional length loads, the padded
  counts, and the branch from the main length to the extra length or the Q-copy poll;
* the last two sites: `stepAt_barrier` (the arrival on barrier 12 and the branch to the `ret`) and
  `stepAt_exit`; `steps_of_loop` reduces the machine's `steps` field to the loop sites below;
* the loop's hand-off: the ring advance of `afterFree` is `advance`/`toBarrier`, and
  `afterFree_inv` preserves the invariant across it; `totalBlocks_lt` bounds the row's block count
  from the launch's padded-length range;
* `stepAt_rawReady`, the expect-tx arrival on `bar_raw_ready[buf]` (pc 2305)
  and the two `add`s that form the index ring's free mbarrier (2306, 2307).

`steps` assembles every site's continuation. `entry_sound` adds the entry run for the shared
launch machine's hand-off. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Tma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The assumptions the role is evaluated under. -/
abbrev asms : List Assumption := Assumptions.all

/-- The batch whose sparse index row the CTA reads (`%ctaid.y`). -/
def eOf (L : Launch) (g : Nat) : Nat := ctaidY L g

/-- The query whose sparse index row the CTA reads (`%ctaid.x`). -/
def qOf (L : Launch) (g : Nat) : Nat := ctaidX L g

/-- The little-endian `n`-byte word at byte `off` of the scalar parameter object `param_0`; a
byte the launch does not supply counts as zero. -/
abbrev paramWord (L : Launch) (off n : Nat) : Nat := paramNat L (param "0") off n

/-! ## The shared objects of the role

The role forms its addresses from the `wksp_buf` symbol (a `mov.b32` from the shared symbol, pcs
2201 and 2230); `sb L off` is `wksp_buf + off`. The byte offsets below are `SharedMemoryPlan`'s
(`config.h:141-172`): `tma_coord` at 221728 with four 256-byte slots, `is_token_valid` at 221696
with four 8-byte slots, the mbarrier block at 222768, and the `kv` union's two `raw_quant` blocks
at 131072 with 36864-byte blocks. -/

/-- The shared byte offset of `tma_coord[phase]` (`config.h:164`): the index warp's 64 words. -/
def coordBase (phase : Nat) : Nat := 221728 + 256 * phase

/-- The shared byte offset of `is_token_valid[phase]` (`config.h:163`). The index warp writes it;
the raw-KV producer does not read it, but it shares the ring slot. -/
def validOff (phase : Nat) : Nat := 221696 + 8 * phase

/-- `bar_valid_coord_ready[phase]` (`config.h:166`, count 32). -/
def readyOff (phase : Nat) : Nat := 222840 + 8 * phase

/-- `bar_valid_coord_free[phase]` (`config.h:167`, count 129). -/
def coordFreeOff (phase : Nat) : Nat := 222872 + 8 * phase

/-- `bar_raw_ready[buf]` (`config.h:168`, count 1). -/
def rawReadyOff (buf : Nat) : Nat := 222808 + 8 * buf

/-- `bar_raw_free[buf]` (`config.h:169`, count 128). -/
def rawFreeOff (buf : Nat) : Nat := 222824 + 8 * buf

/-- `bar_q_utccp` (`config.h:65`, count 1). -/
def qUtccpOff : Nat := 222784

/-- `bar_last_store_done` (`config.h:63`, count 128). -/
def lastStoreOff : Nat := 222768

/-- The raw ring buffer `raw_quant[buf]`: 36864 bytes of 64 rows of 576. -/
def rawBase (buf : Nat) : Nat := 131072 + 36864 * buf

/-- The shared destination of gather4 issue `k`: four rows of 576 bytes. -/
def issueDst (buf k : Nat) : Nat := rawBase buf + 2304 * k

/-- The four row coordinates of issue `k` are `tma_coord` positions `4k .. 4k+3`. -/
def coordPos (k j : Nat) : Nat := 4 * k + j

/-- The registers the 16 `ld.shared.v4.b32` loads write, in program order. -/
def coordRegs : List Nat :=
  [692, 693, 694, 695, 698, 699, 700, 701, 703, 704, 705, 706, 708, 709, 710, 711,
   713, 714, 715, 716, 718, 719, 720, 721, 723, 724, 725, 726, 728, 729, 730, 731,
   733, 734, 735, 736, 738, 739, 740, 741, 743, 744, 745, 746, 748, 749, 750, 751,
   753, 754, 755, 756, 758, 759, 760, 761, 763, 764, 765, 766, 768, 769, 770, 771]

/-- The destination registers of the 16 gather4 issues, in program order. -/
def issueRegs : List Nat :=
  [690, 697, 702, 707, 712, 717, 722, 727, 732, 737, 742, 747, 752, 757, 762, 767]

/-- The 32-bit pattern of an index, as the `s32` load of the index array returns it. -/
def ipat (z : Int) : Nat := i32Bits z

/-- The index the row's array gives slot `(b, lane, i)` (`Data/Indices.slotIndex`), rebased on
the main cache's block count for an extra block. -/
def slotIdx (P : Params) (L : Launch) (g b l i : Nat) : Int :=
  slotIndex (P.topkLen (eOf L g)) (P.idx (eOf L g) (qOf L g)) (P.extraIdx (eOf L g) (qOf L g))
    b l i

/-- The block stride in token rows of the slot's cache (`kernel.cuh:540-541,561`). -/
def slotStride (P : Params) (L : Launch) (g b : Nat) : Nat :=
  slotBlockStride (P.topkLen (eOf L g)) P.blockStride P.extraBlockStride b

/-- The tokens per page block of the slot's cache (`kernel.cuh:560`). -/
def slotPg (P : Params) (L : Launch) (g b : Nat) : Nat :=
  slotPage (P.topkLen (eOf L g)) P.page P.extraPage b

/-- The validity the code's `cur_idx != -1 && abs_pos + i < len` computes (`kernel.cuh:582`). -/
def validBit (P : Params) (L : Launch) (g b l i : Nat) : Bool :=
  kvSlotValid (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b l i (slotIdx P L g b l i)

/-- The `tma_coord` word the code computes for a slot: `(unsigned)idx / page` times the block's
row stride plus `idx % page` (`kernel.cuh:570,571,584`). -/
def rowBits (P : Params) (L : Launch) (g b l i : Nat) : Nat :=
  ipat (slotIdx P L g b l i) / slotPg P L g b * (slotStride P L g b / bytesPerToken) +
    ipat (slotIdx P L g b l i) % slotPg P L g b

/-- The `tma_coord` word of slot `(block, lane, pair)`, as the index warp computes it for that
lane: the physical row of a valid slot, the `-1` marker otherwise. The lane is a parameter
because the TMA lane reads the words the index warp's 32 lanes wrote. -/
def coordWord (P : Params) (L : Launch) (g : Nat) (b l i : Nat) : Nat :=
  if validBit P L g b l i then rowBits P L g b l i else 2 ^ 32 - 1

/-- The `tma_coord` word at position `p` of the block's ring slot (`p = 2 * lane + pair`). -/
def coordAt (P : Params) (L : Launch) (g : Nat) (b p : Nat) : Nat :=
  coordWord P L g b (p / 2) (p % 2)

/-! ## The ring arithmetic of the role

The role carries the index ring's slot `phase` (which it derives as `block % 4`) with the phase
parity `par` of `bar_valid_coord_ready`, and the raw ring's buffer `buf` (`block % 2`) with the
parity `rpar` with which it polls `bar_raw_free`. The loop's two exit tests are the block count
the row's padded lengths give (`%r2964`, a counter from `-totalBlocks`) and the branch at 2225
(the main-cache test `%p52`). -/

/-! ## The sites

One state per event instruction. `.coord k j` is element `j` of the `v4` load `k` (the same pc for
the four elements, `sub = j`), `.issue k` the `k`-th gather4 issue. -/

inductive Site where
  /-- The election of the lane that produces the raw KV (2165). -/
  | elect
  /-- The row's main-cache length, `ld.global.nc` (2181). -/
  | lenOrig
  /-- The row's extra-cache length, `ld.global.nc` (2191). -/
  | lenExtra
  /-- The poll of `bar_q_utccp` (2205). -/
  | waitQ
  /-- The poll of `bar_last_store_done` (2209). -/
  | waitLast
  /-- The poll of `bar_valid_coord_ready[phase]` (2234). -/
  | waitCoord
  /-- The poll of `bar_raw_free[buf]` (2245). -/
  | waitFree
  /-- Element `j` of coordinate load `k`, `ld.shared.v4.b32` (2250-2299). -/
  | coord (k : Fin 16) (j : Fin 4)
  /-- Gather4 issue `k`, `cp.async.bulk.tensor.2d...tile::gather4` (2259-2303). -/
  | issue (k : Fin 16)
  /-- The expect-tx arrival on `bar_raw_ready[buf]` (2305). -/
  | rawReady
  /-- The release of the index slot, `bar_valid_coord_free[phase]` (2308). -/
  | coordFree
  /-- `barrier.sync 12, 384` of `everyone_sync` (2330). -/
  | barrier
  /-- The kernel's single `ret` (3611). -/
  | exit
  deriving DecidableEq

/-- The pcs of the 16 `ld.shared.v4.b32` coordinate loads, in program order. -/
def coordPcs : List Nat :=
  [Flow.load_19, Flow.load_20, Flow.load_21, Flow.load_22, Flow.load_23, Flow.load_24,
   Flow.load_25, Flow.load_26, Flow.load_27, Flow.load_28, Flow.load_29, Flow.load_30,
   Flow.load_31, Flow.load_32, Flow.load_33, Flow.load_34]

/-- The pcs of the 16 gather4 issues, in program order. -/
def issuePcs : List Nat :=
  [Flow.tensorCopy_12, Flow.tensorCopy_13, Flow.tensorCopy_14, Flow.tensorCopy_15,
   Flow.tensorCopy_16, Flow.tensorCopy_17, Flow.tensorCopy_18, Flow.tensorCopy_19,
   Flow.tensorCopy_20, Flow.tensorCopy_21, Flow.tensorCopy_22, Flow.tensorCopy_23,
   Flow.tensorCopy_24, Flow.tensorCopy_25, Flow.tensorCopy_26, Flow.tensorCopy_27]

/-- The program counter of a site. -/
def Site.pc : Site → Nat
  | .elect => Flow.elect_7
  | .lenOrig => Flow.load_17
  | .lenExtra => Flow.load_18
  | .waitQ => Flow.mbarWait_7
  | .waitLast => Flow.mbarWait_8
  | .waitCoord => Flow.mbarWait_9
  | .waitFree => Flow.mbarWait_10
  | .coord k _ => coordPcs.getD k.val 0
  | .issue k => issuePcs.getD k.val 0
  | .rawReady => Flow.mbarArrive_4
  | .coordFree => Flow.mbarArrive_5
  | .barrier => Flow.bar_12
  | .exit => Flow.exit_0

/-- The sub-step of a site: the element of a vector load. -/
def Site.sub : Site → Nat
  | .coord _ j => j.val
  | _ => 0

/-- The first length site under the length pointers of `param_0`: a null pointer reads the
parameter's constant instead of the row's runtime length, so the load is not an event then. The
test is the pointer word the code compares (`%rd1` at 2177, `%rd2` at 2182), not the parameter's
`Option`: a pointer whose 64-bit word is zero is null whatever its mathematical value. -/
def firstLenSite (L : Launch) : Site :=
  if paramWord L 80 8 = 0 then (if paramWord L 144 8 = 0 then .waitQ else .lenExtra)
  else .lenOrig

/-! ## The abstract state and its invariant -/

/-- The role's state: the next event, the block, the index ring's slot and parity, the raw ring's
buffer and parity, and the row's two runtime lengths. -/
structure D where
  site : Site
  /-- The block whose raw rows the body produces. -/
  block : Nat
  /-- The `tma_coord` ring slot (`%r2967`). -/
  phase : Nat
  /-- The index ring's phase parity (`%r455`). -/
  par : Nat
  /-- The `raw_quant` ring buffer (`%r2966`). -/
  buf : Nat
  /-- The raw ring's poll parity (`%r454`). -/
  rpar : Nat
  /-- The row's main-cache length (`%r2962`). -/
  len0 : Nat
  /-- The row's extra-cache length (`%r2963`). -/
  len1 : Nat
  /-- The words the coordinate reads returned, by position: position `p` is element `p % 4` of
  load `p / 4`. The machine records each read's value and compares it with nothing. -/
  cw : Nat → Value

/-- A length site is reached only when its pointer is not null: a null pointer reads the
parameter's constant, so the load is not an event (`firstLenSite`). -/
def LenOk (L : Launch) : Site → Prop
  | .lenOrig => paramWord L 80 8 ≠ 0
  | .lenExtra => paramWord L 144 8 ≠ 0
  | _ => True

/-- **The role's loop invariant**: the two ring positions and parities are the block's, the block
is one of the row's padded blocks (or the role is past the loop), and the lengths are the row's
runtime lengths. The ring slots, mbarrier addresses and raw destinations are functions of these
(`coordBase`, `readyOff`, `rawBase`, `issueDst`). -/
structure Inv (P : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The index ring's slot is one of the four. -/
  phase_lt : d.phase < 4
  /-- The index ring's parity is a bit. -/
  par_lt : d.par < 2
  /-- The raw ring's buffer is one of the two. -/
  buf_lt : d.buf < 2
  /-- The raw ring's parity is a bit. -/
  rpar_lt : d.rpar < 2
  /-- The index ring's slot is the block's position in it. -/
  phase_eq : d.site ≠ .barrier → d.site ≠ .exit → d.phase = d.block % 4
  /-- The index ring's parity flips when the slot wraps. -/
  par_eq : d.site ≠ .barrier → d.site ≠ .exit → d.par = d.block / 4 % 2
  /-- The raw ring's buffer is the block's position in it. -/
  buf_eq : d.site ≠ .barrier → d.site ≠ .exit → d.buf = d.block % 2
  /-- The raw ring's parity is the block's position in the ring. -/
  rpar_eq : d.site ≠ .barrier → d.site ≠ .exit → d.rpar = d.block / 2 % 2
  /-- The first length is the row's runtime main-cache length. -/
  len0 : d.len0 = P.topkLen (eOf L g)
  /-- The second length is the row's runtime extra-cache length. -/
  len1 : d.len1 = P.extraTopkLen (eOf L g)
  /-- The block is one of the row's padded blocks; the barrier is past the last one. -/
  block_le : d.site = .barrier ∨ d.site = .exit ∨ d.block < totalBlocks d.len0 d.len1
  /-- The CTA is a row of the batch: the lengths are a row's, so the loop's counters fit. -/
  batch : eOf L g < P.b
  /-- A length site's pointer is not null. -/
  lenOk : LenOk L d.site

/-- The initial state: the election, block 0, both rings at their slot 0 with parity 0, and the
row's two lengths. -/
def init (P : Params) (L : Launch) (g : Nat) : D where
  site := .elect
  block := 0
  phase := 0
  par := 0
  buf := 0
  rpar := 0
  len0 := P.topkLen (eOf L g)
  len1 := P.extraTopkLen (eOf L g)
  cw := fun _ => b32 0

/-- The offset of the KV tensor map the block reads: the main cache's descriptor `param_1 + 768`
for a main-cache block, the extra cache's `param_1 + 896` for an extra-cache block (the `selp` at
pc 2248; `Data/Sites.paramKvOffsetSelector`). -/
def kvOff (d : D) : Nat := if d.block < numOrigBlocks d.len0 then 768 else 896

/-- The row's number of main-cache blocks (`%r489`). -/
def numOrig (d : D) : Nat := numOrigBlocks d.len0

/-- The row's number of blocks of both caches (`- %r2964`). -/
def total (d : D) : Nat := totalBlocks d.len0 d.len1

/-! ## The register table

The registers the role tracks, valued by the state. Every entry is one the code computes from the
state's fields: the shared addresses, the ring positions, the loop counter, the descriptor
selection, the raw destinations and the gather4 coordinates. -/

/-- The registers the role's table values: the ring positions and parities, the loop's two block
counts and counter, the mbarrier addresses and parities, the ring slots' shared addresses, the
descriptor selection, the raw destinations and the gather4 coordinates. -/
def tracked : List Nat :=
  [52, 146, 147, 454, 455, 460, 486, 487, 488, 489, 662, 663, 664, 669, 670, 671, 672, 680,
   685, 686, 687, 688, 689, 690, 691, 696, 772, 773, 776, 777, 780, 781, 782, 783, 790, 791,
   2962, 2963, 2964, 2965, 2966, 2967, 2990, 2991, 3007, 3008, 3045, 3047, 3049, 3050,
   3051] ++ coordRegs ++ issueRegs

/-- The raw ring destinations of the 16 gather4 issues: `rawBase buf + 2304 * k`. -/
def issueDsts (L : Launch) (d : D) : List (Nat × Value) :=
  [(697, sb L (issueDst d.buf 1)), (702, sb L (issueDst d.buf 2)),
   (707, sb L (issueDst d.buf 3)), (712, sb L (issueDst d.buf 4)),
   (717, sb L (issueDst d.buf 5)), (722, sb L (issueDst d.buf 6)),
   (727, sb L (issueDst d.buf 7)), (732, sb L (issueDst d.buf 8)),
   (737, sb L (issueDst d.buf 9)), (742, sb L (issueDst d.buf 10)),
   (747, sb L (issueDst d.buf 11)), (752, sb L (issueDst d.buf 12)),
   (757, sb L (issueDst d.buf 13)), (762, sb L (issueDst d.buf 14)),
   (767, sb L (issueDst d.buf 15))]

/-- The coordinate registers with their positions: register `coordRegs[p]` holds position `p`. -/
def coordKeys : List (Nat × Nat) :=
  [(692, 0), (693, 1), (694, 2), (695, 3), (698, 4), (699, 5), (700, 6), (701, 7), (703, 8),
   (704, 9), (705, 10), (706, 11), (708, 12), (709, 13), (710, 14), (711, 15), (713, 16),
   (714, 17), (715, 18), (716, 19), (718, 20), (719, 21), (720, 22), (721, 23), (723, 24),
   (724, 25), (725, 26), (726, 27), (728, 28), (729, 29), (730, 30), (731, 31), (733, 32),
   (734, 33), (735, 34), (736, 35), (738, 36), (739, 37), (740, 38), (741, 39), (743, 40),
   (744, 41), (745, 42), (746, 43), (748, 44), (749, 45), (750, 46), (751, 47), (753, 48),
   (754, 49), (755, 50), (756, 51), (758, 52), (759, 53), (760, 54), (761, 55), (763, 56),
   (764, 57), (765, 58), (766, 59), (768, 60), (769, 61), (770, 62), (771, 63)]

/-- The coordinate registers with the words the reads recorded. -/
def coordTable (cw : Nat → Value) : List (Nat × Value) :=
  coordKeys.map fun x => (x.1, cw x.2)

/-- The registers of state `d` other than the coordinates, with their values. `%r690` is issue
0's destination and the raw block's base at once (`issueDst buf 0 = rawBase buf`). -/
def baseTable (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  (460, b32 (ctaidY L g)) ::
  (2990, .ptr 64 false (.param (param "1")) 0) ::
  (2991, .ptr 64 false (.param (param "0")) 0) ::
  (662, b32 0) :: (663, b32 (2 ^ 32 - 1)) ::
  (664, b32 P.b) :: (3007, b64 (paramWord L 80 8)) ::
  (3008, b64 (paramWord L 144 8)) ::
  (3045, b64 ((paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)) ::
  (3047, b64 ((paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)) ::
  (486, b32 (ceilToMultiple d.len0 topkBlock)) ::
  (487, b32 (origPadded d.len0)) ::
  (488, b32 (origPadded d.len0 + ceilToMultiple d.len1 topkBlock)) ::
  (669, sb L qUtccpOff) :: (670, b32 0) :: (671, b32 10000000) ::
  (680, sb L 0) :: (672, sb L lastStoreOff) ::
  (52, .pred (decide (d.block < numOrigBlocks d.len0))) ::
  (146, .bits 16 (BitVec.ofNat 64 d.par)) ::
  (454, .bits 16 (BitVec.ofNat 64 d.rpar)) :: (147, .bits 16 (BitVec.ofNat 64 d.rpar)) ::
  (455, .bits 16 (BitVec.ofNat 64 d.par)) ::
  (489, b32 (numOrigBlocks d.len0)) ::
  (685, sb L (readyOff d.phase)) :: (686, b32 d.par) :: (687, b32 10000000) ::
  (776, sb L 0) :: (777, sb L (8 * d.phase)) ::
  (2964, b32 ((d.block + (2 ^ 32 - totalBlocks d.len0 d.len1)) % 2 ^ 32)) ::
  (2965, b32 d.block) :: (2966, b32 d.buf) :: (2967, b32 d.phase) ::
  (688, sb L (rawFreeOff d.buf)) :: (689, b32 (1 - d.rpar)) ::
  (780, sb L (8 * d.buf)) :: (781, b32 (2 ^ 32 - 1 - d.buf)) ::
  (690, sb L (rawBase d.buf)) :: (696, sb L (rawReadyOff d.buf)) ::
  (783, sb L (36864 * d.buf)) ::
  (3051, b64 (if d.block < numOrigBlocks d.len0 then 768 else 896)) ::
  (691, b32 0) ::
  (3049, b64 ((P.param1Base + kvOff d) % 2 ^ 64)) ::
  (3050, b64 1364590687093260288) ::
  (782, sb L (256 * d.phase)) ::
  (772, b32 36864) :: (773, sb L (coordFreeOff d.phase)) ::
  (790, b32 12) :: (791, b32 384) ::
  (2962, b32 d.len0) ::
  (2963, b32 (match d.site with
    | .lenOrig => P.extra_topk
    | _ => d.len1)) ::
  issueDsts L d

/-- The registers of state `d` with their values. -/
def table (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  baseTable P L g d ++ coordTable d.cw

/-- The value of a register at state `d`: the table's, else the zero word. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table P L g d).lookup r).getD (b32 0)

/-- The facts of state `d`: the registers live at its site that the table values. -/
def facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsFrom ((Flow.live d.site.pc).filter fun r => tracked.contains r) (valueOf P L g d)

/-- The values a vector coordinate load has returned before its current element: element `j` of
load `k` follows the elements `0 .. j-1` at positions `4k .. 4k+j-1`, whose words `coordAt`
fixes. Every other site carries no pending values. A thread state between two elements of a
`ld.shared.v4.b32` holds exactly these (`afterLoad` appends the element it read). -/
def accAt (d : D) : List Value :=
  match d.site with
  | .coord k j => (List.range j.val).map fun i => d.cw (coordPos k.val i)
  | _ => []

/-- A state outside a coordinate load has no pending values. -/
theorem accAt_of_not_coord {d : D}
    (h : ∀ k j, d.site ≠ .coord k j) : accAt d = [] := by
  unfold accAt
  cases hsite : d.site <;> simp_all

/-- The pending values of a coordinate site are the words before its element. -/
theorem accAt_of_coord {d : D} {k : Fin 16} {j : Fin 4}
    (hd : d.site = .coord k j) :
    accAt d = (List.range j.val).map fun i => d.cw (coordPos k.val i) := by
  unfold accAt
  rw [hd]

/-- A concrete state of an abstract state: at the site's program counter and sub-step, with the
site's facts and the values its vector load has returned so far. -/
def AtD (P : Params) (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = accAt d ∧ t.fault = none ∧
    Holds t.regs (facts P L g d)

/-! ## The successor relation -/

/-- The site after element `j` of coordinate load `k`: the element's next sub-step, or the next
load or issue in the program's order (`load 0`, `load 1`, `issue 0`, `load 2`, `issue 1`, …). -/
def afterCoord (k : Fin 16) (j : Fin 4) : Site :=
  if hj : j.val + 1 < 4 then .coord k ⟨j.val + 1, hj⟩
  else if k.val = 0 then .coord 1 0
  else .issue ⟨k.val - 1, by omega⟩

/-- The site after gather4 issue `k`: coordinate load `k + 2` while one remains, then the last
issue, then the arrival. -/
def afterIssue (k : Fin 16) : Site :=
  if hk : k.val + 2 < 16 then .coord ⟨k.val + 2, hk⟩ 0
  else if k.val = 14 then .issue 15
  else .rawReady

/-- The state after the index slot's release: the next block's loop head (the polls at 2225-2245
follow the loop's local head), or the barrier when it was the last block. The two ring positions
and parities advance as the code's 2309-2327 compute them. -/
def afterFree (d : D) : D :=
  if d.block + 1 < totalBlocks d.len0 d.len1 then
    { site := .waitCoord
      block := d.block + 1
      phase := (d.phase + 1) % 4
      par := if d.phase = 3 then 1 - d.par else d.par
      buf := 1 - d.buf
      rpar := if d.rpar = d.buf then 0 else 1
      len0 := d.len0
      len1 := d.len1
      cw := d.cw }
  else { d with site := .barrier, block := d.block + 1 }

/-- The ring advance of the block hand-off: the next block, the next index slot with its parity,
and the other raw buffer with the parity its poll uses (the code's 2309-2327). -/
def advance (d : D) : D where
  site := .waitCoord
  block := d.block + 1
  phase := (d.phase + 1) % 4
  par := if d.phase = 3 then 1 - d.par else d.par
  buf := 1 - d.buf
  rpar := if d.rpar = d.buf then 0 else 1
  len0 := d.len0
  len1 := d.len1
  cw := d.cw

theorem afterFree_eq_advance {d : D} (h : d.block + 1 < totalBlocks d.len0 d.len1) :
    afterFree d = advance d := by
  simp only [afterFree, advance, h, ↓reduceIte]

/-- The barrier hand-off after the last block. -/
def toBarrier (d : D) : D := { d with site := .barrier, block := d.block + 1 }

theorem afterFree_eq_barrier {d : D} (h : ¬ d.block + 1 < totalBlocks d.len0 d.len1) :
    afterFree d = toBarrier d := by
  simp only [afterFree, toBarrier, h, ↓reduceIte]

/-- The loop entry initializes both ring slots and their parities. -/
def beginLoop (d : D) : D :=
  { d with site := .waitCoord, block := 0, phase := 0, par := 0, buf := 0, rpar := 0 }

/-- The abstract successor after event `e`.

The election continues only for the elected lane (its leader is the thread's own lane); the other
lanes run the idle main loop and are not followed. A length load continues only on the row's
runtime length (`Assumption.ncReadOnly` fixes its bytes to the launch content) and a coordinate
element only on the block's `tma_coord` word of its position. A poll continues to the next site on
success and stays at the poll otherwise. An issue continues on the raw ring's completion barrier;
an arrival on the ring's own mbarrier. -/
def next (P : Params) (L : Launch) (g : Nat) : D → Event → Option (Option D)
  | d, e =>
    match d.site with
    | .elect =>
      match e.kind with
      | .elect _ _ ld =>
        if ld = PTX.laneOf L g then
          (if ctaidY L g < P.b then some (some { d with site := firstLenSite L })
            else some none)
        else some none
      | _ => none
    | .lenOrig =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.topkLen (eOf L g)) then
            some (some
              { d with
                site := if paramWord L 144 8 = 0 then .waitQ else .lenExtra
                len0 := P.topkLen (eOf L g) })
          else some none
        | .error _ => some none
      | _ => none
    | .lenExtra =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.extraTopkLen (eOf L g)) then
            some (some { d with site := .waitQ, len1 := P.extraTopkLen (eOf L g) })
          else some none
        | .error _ => some none
      | _ => none
    | .waitQ =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .waitLast } else d))
      | _ => none
    | .waitLast =>
      match e.kind with
      | .wait _ _ ok _ _ =>
        some (some (if ok then
          (if totalBlocks d.len0 d.len1 = 0 then { d with site := .barrier }
           else beginLoop d) else d))
      | _ => none
    | .waitCoord =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .waitFree } else d))
      | _ => none
    | .waitFree =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .coord 0 0 } else d))
      | _ => none
    | .coord k j =>
      match e.kind with
      | .rd a bs =>
        if a.loc = ⟨.shared, ctaOf L g, L.sharedBase + coordBase d.phase +
            16 * k.val + 4 * j.val⟩ ∧
            a.size = 4 then
          match rebuild 3 bs with
          | .ok v =>
            some (some { d with site := afterCoord k j,
                                cw := Function.update d.cw (coordPos k.val j.val) v })
          | .error _ => none
        else some none
      | _ => none
    | .issue k =>
      match e.kind with
      | .tensorIssue _ s =>
        if s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ then
          some (some { d with site := afterIssue k })
        else some none
      | _ => none
    | .rawReady =>
      match e.kind with
      | .arrive m tx _ _ _ =>
        if m = ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ ∧ tx = 36864 then
          some (some { d with site := .coordFree })
        else some none
      | _ => none
    | .coordFree =>
      match e.kind with
      | .arrive m _ _ _ _ =>
        if m = ⟨.shared, ctaOf L g, L.sharedBase + coordFreeOff d.phase⟩ then
          some (some (afterFree d))
        else some none
      | _ => none
    | .barrier =>
      match e.kind with
      | .bar id _ _ => some (some (if id = 12 then { d with site := .exit } else d))
      | _ => none
    | .exit =>
      match e.kind with
      | .exit => some none
      | _ => none

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

/-! ## The recorded coordinate words

The machine records every coordinate word it reads (`D.cw`) and never compares it. What the
words are is the reference invariant `Ref`: the words of the current block read so far are the
index warp's `tma_coord` words. `ref_next` carries it across every step whose read returns the
published word (`Expect`); the source of that word is a fact about the whole execution
(`TmaCoordinateRef`). -/

/-- The coordinate positions of the current block read before the site, in the program's order
`load 0`, `load 1`, `issue 0`, `load 2`, …, `load 15`, `issue 14`, `issue 15`. -/
def readCount : Site → Nat
  | .coord k j => coordPos k.val j.val
  | .issue k => 4 * min (k.val + 2) 16
  | .rawReady | .coordFree => 64
  | _ => 0

/-- **The role's reference invariant**: every coordinate word read in the current block is the
`tma_coord` word of its position. -/
def Ref (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  ∀ p < readCount d.site, d.cw p = b32 (coordAt P L g d.block p)

/-- What a coordinate read must return for `Ref` to continue: the block's word of its position. -/
def Expect (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  ∀ k j a bs v, d.site = .coord k j → e.kind = .rd a bs → rebuild 3 bs = .ok v →
    v = b32 (coordAt P L g d.block (coordPos k.val j.val))

theorem ref_init (P : Params) (L : Launch) (g : Nat) : Ref P L g (init P L g) :=
  fun _ hp => absurd hp (Nat.not_lt_zero _)

private theorem ref_zero {P : Params} {L : Launch} {g : Nat} {d : D}
    (h : readCount d.site = 0) : Ref P L g d :=
  fun _ hp => absurd (h ▸ hp) (Nat.not_lt_zero _)

private theorem readCount_afterCoord (k : Fin 16) (j : Fin 4) :
    readCount (afterCoord k j) = coordPos k.val j.val + 1 := by
  revert k j
  decide

private theorem readCount_afterIssue (k : Fin 16) :
    readCount (afterIssue k) = readCount (.issue k) := by
  revert k
  decide

private theorem readCount_firstLenSite (L : Launch) : readCount (firstLenSite L) = 0 := by
  unfold firstLenSite
  split
  · split <;> rfl
  · rfl

set_option maxHeartbeats 2000000 in
/-- **`Ref` is preserved by every step whose read returns the expected word.** -/
theorem ref_next {P : Params} {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (hr : Ref P L g d) (hx : Expect P L g d e) (hn : next P L g d e = some (some d')) :
    Ref P L g d' := by
  cases hd : d.site <;> simp only [next, hd] at hn
  case coord k j =>
    split at hn
    · rename_i a bs hk
      split at hn
      · split at hn
        · rename_i v hv
          cases hn
          intro p hp
          simp only [readCount_afterCoord] at hp
          change Function.update d.cw (coordPos k.val j.val) v p = b32 (coordAt P L g d.block p)
          by_cases hpe : p = coordPos k.val j.val
          · subst hpe
            rw [Function.update_self]
            exact hx k j a bs v hd hk hv
          · rw [Function.update_of_ne hpe]
            exact hr p (by rw [hd]; simp only [readCount]; omega)
        · cases hn
      · cases hn
    · cases hn
  case issue k =>
    split at hn <;> (try split at hn) <;> cases hn
    exact fun p hp => hr p (by rw [hd, ← readCount_afterIssue]; exact hp)
  case rawReady =>
    split at hn <;> (try split at hn) <;> cases hn
    exact fun p hp => hr p (by rw [hd]; exact hp)
  case elect =>
    revert hn
    cases e.kind
    case elect m n ld =>
      intro hn
      dsimp only at hn
      by_cases h1 : ld = PTX.laneOf L g
      · rw [ite_eq_left h1] at hn
        by_cases h2 : ctaidY L g < P.b
        · rw [ite_eq_left h2] at hn
          have hd' := Option.some.inj (Option.some.inj hn)
          exact ref_zero (by rw [← hd']; dsimp only; exact readCount_firstLenSite L)
        · rw [ite_eq_right h2] at hn
          cases hn
      · rw [ite_eq_right h1] at hn
        cases hn
    all_goals intro hn; cases hn
  case exit => split at hn <;> cases hn
  case lenOrig | lenExtra =>
    revert hn
    cases e.kind
    case nc a bs =>
      intro hn
      dsimp only at hn
      cases hrb : rebuild 3 bs with
      | error f => rw [hrb] at hn; cases hn
      | ok v =>
        rw [hrb] at hn
        dsimp only at hn
        split at hn
        · rw [← Option.some.inj (Option.some.inj hn)]
          exact ref_zero (by dsimp only; first | rfl | (split <;> rfl))
        · cases hn
    all_goals intro hn; cases hn
  case coordFree =>
    split at hn <;> (try split at hn) <;> cases hn
    exact ref_zero (by unfold afterFree; split <;> rfl)
  all_goals
    split at hn <;> try cases hn
    all_goals (repeat' split) <;> first | exact ref_zero rfl | exact hr

/-- A state whose recorded words differ only away from register `r` gives `r` the same value. -/
private theorem lookup_keys {c c' : Nat → Value} {r : Nat} (l : List (Nat × Nat))
    (h : ∀ x ∈ l, x.1 = r → c' x.2 = c x.2) :
    (l.map fun x => (x.1, c' x.2)).lookup r = (l.map fun x => (x.1, c x.2)).lookup r := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hl : ∀ y ∈ l, y.1 = r → c' y.2 = c y.2 := fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : x.1 = r
    · have hb : (r == x.1) = true := beq_iff_eq.mpr hx.symm
      simp only [List.map_cons, List.lookup, hb, h x List.mem_cons_self hx]
    · have hb : (r == x.1) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => hx h.symm
      simp only [List.map_cons, List.lookup, hb]
      exact ih hl

private theorem lookup_coordTable {c c' : Nat → Value} {r : Nat}
    (h : ∀ x ∈ coordKeys, x.1 = r → c' x.2 = c x.2) :
    (coordTable c').lookup r = (coordTable c).lookup r :=
  lookup_keys coordKeys h

private theorem coordKeys_reg : ∀ x ∈ coordKeys, coordRegs.getD x.2 0 = x.1 := by
  decide

private theorem lookup_append_congr {a b b' : List (Nat × Value)} {r : Nat}
    (h : b'.lookup r = b.lookup r) : (a ++ b').lookup r = (a ++ b).lookup r := by
  induction a with
  | nil => exact h
  | cons x a ih =>
    obtain ⟨k, v⟩ := x
    cases hk : r == k <;> simp only [List.cons_append, List.lookup, hk, ih]

/-- **Recorded words are values of the coordinate registers only**: replacing the words leaves
every register whose positions keep their words with its value. -/
theorem valueOf_cw {P : Params} {L : Launch} {g : Nat} {d : D} {c : Nat → Value} {r : Nat}
    (h : ∀ x ∈ coordKeys, x.1 = r → c x.2 = d.cw x.2) :
    valueOf P L g { d with cw := c } r = valueOf P L g d r := by
  change ((baseTable P L g d ++ coordTable c).lookup r).getD _ =
    ((baseTable P L g d ++ coordTable d.cw).lookup r).getD _
  rw [lookup_append_congr (lookup_coordTable h)]

/-! ## The sites are event instructions -/

/-- The pcs of the role's event instructions, in program order. -/
def eventPcs : List Nat :=
  [Flow.elect_7, Flow.load_17, Flow.load_18, Flow.mbarWait_7, Flow.mbarWait_8, Flow.mbarWait_9,
   Flow.mbarWait_10] ++ coordPcs ++ issuePcs ++
    [Flow.mbarArrive_4, Flow.mbarArrive_5, Flow.bar_12, Flow.exit_0]

/-- Every pc of `eventPcs` holds an unguarded event instruction. -/
theorem eventPcs_ok :
    eventPcs.all (fun pc => match codeAt pc with
      | some i => !i.op.isLocal && i.guard.isNone
      | none => false) = true := by
  decide +kernel

/-- A site's pc is one of the role's event pcs. -/
theorem mem_eventPcs (s : Site) : s.pc ∈ eventPcs := by
  cases s with
  | coord k j => fin_cases k <;> fin_cases j <;> decide
  | issue k => fin_cases k <;> decide
  | elect => decide
  | lenOrig => decide
  | lenExtra => decide
  | waitQ => decide
  | waitLast => decide
  | waitCoord => decide
  | waitFree => decide
  | rawReady => decide
  | coordFree => decide
  | barrier => decide
  | exit => decide

/-- **Every site is an unguarded event instruction of the decoded program**: the site's pc holds
an instruction that performs an event and has no guard, so the machine's guard obligation is
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
    refine ⟨ins, h, hok.1, ?_⟩
    rw [hok.2]
    trivial

/-! ## The invariant at the initial state -/

/-- The initial state satisfies the invariant. -/
theorem init_inv (P : Params) (L : Launch) (g : Nat) (hb : eOf L g < P.b) :
    Inv P L g (init P L g) := by
  have hpos : 0 < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) :=
    totalBlocks_pos _ _
  refine ⟨by simp [init], by simp [init], by simp [init], by simp [init], ?_, ?_, ?_, ?_, rfl,
    rfl, Or.inr (Or.inr hpos), hb, trivial⟩
  · intro _ _
    simp [init]
  · intro _ _
    simp [init]
  · intro _ _
    simp [init]
  · intro _ _
    simp [init]

/-! ## The bridges to `Data/Indices`

The validity and row arithmetic above is `Wg1Index`'s (the sibling index warp's), restated on the
role's own state; the bridge below is the index warp's `rowBits_eq_rowOf`, with the source's
per-slot cache geometry (`slotStride`, `slotPg`, `slotIdx`) and the launch's index ranges. -/

/-- The pattern of a nonnegative index below `2 ^ 32` is the index itself. -/
theorem ipat_eq_toNat {z : Int} (h0 : 0 ≤ z) (h1 : z.toNat < 2 ^ 32) : ipat z = z.toNat := by
  have hz : z < (2 ^ 32 : Int) := by omega
  simp only [ipat, i32Bits]
  rw [Int.emod_eq_of_lt h0 hz]

/-- The row's main-cache length is at most the parameter's budget. -/
theorem topkLen_le {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) : P.topkLen (eOf L g) ≤ P.topk := by
  cases h : P.topkLenBase with
  | none =>
    have hp := hpre.paramTopkLen
    rw [h] at hp
    exact le_of_eq (hp.2 _ hb)
  | some x =>
    have hp := hpre.paramTopkLen
    rw [h] at hp
    exact (hp.2.2 (eOf L g) hb 0 (by omega)).2 _ hb

/-- The row's extra-cache length is at most the parameter's extra budget. -/
theorem extraLen_le {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) : P.extraTopkLen (eOf L g) ≤ P.extra_topk := by
  cases h : P.extraTopkLenBase with
  | none =>
    have hp := hpre.paramExtraTopkLen
    rw [h] at hp
    exact le_of_eq (hp.2 _ hb)
  | some x =>
    have hp := hpre.paramExtraTopkLen
    rw [h] at hp
    exact (hp.2.2 (eOf L g) hb 0 (by omega)).2 _ hb

/-- **The `tma_coord` word of a valid slot is the physical row `Data/Indices.rowOf` names**:
the code's `(unsigned)idx / page * (stride / 528) + idx % page` (`kernel.cuh:570-571,584`) is
`rowOf` of the row's index in the block's own cache geometry. -/
theorem rowBits_eq_rowOf {P : Params} {L : Launch} {mem0 : Mem0} {g b l i : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (_hblk : b < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hv : validBit P L g b l i = true) :
    rowBits P L g b l i =
      rowOf (slotStride P L g b) (slotPg P L g b) (slotIdx P L g b l i) := by
  have hpos := slotPos_lt_slotLen_of_kvSlotValid hv
  have hne : slotIdx P L g b l i ≠ -1 := (kvSlotValid_eq_true_iff.mp hv).1
  have htopk := topkLen_le hpre hb
  have hextra := extraLen_le hpre hb
  by_cases he : isExtraBlock b (P.topkLen (eOf L g)) = true
  · have hidx : slotIdx P L g b l i =
        P.extraIdx (eOf L g) (qOf L g) (slotPos (P.topkLen (eOf L g)) b l i) := by
      simp only [slotIdx, slotIndex, he, ite_true]
    have hlen' : slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b =
        P.extraTopkLen (eOf L g) := by simp [slotLen, he]
    have hlt : slotPos (P.topkLen (eOf L g)) b l i < P.extra_topk := by omega
    obtain ⟨h0, h1⟩ := hpre.extraIdxRange (eOf L g) hb (qOf L g) hq _
      (by exact ⟨hlen' ▸ hpos, hidx ▸ hne⟩)
    have hbnd : (P.extraIdx (eOf L g) (qOf L g)
        (slotPos (P.topkLen (eOf L g)) b l i)).toNat < 2 ^ 32 := by
      have hp := hpre.extraPos (by omega : 0 < P.extra_topk)
      have hpage : P.extraPage ≤ P.extraBlockStride / 528 := by
        have := hp.2.2.2
        omega
      have hmul : P.extraNumBlocks * P.extraPage ≤
          P.extraNumBlocks * (P.extraBlockStride / 528) := Nat.mul_le_mul_left _ hpage
      have hr := hpre.extraRowsRange
      have := Nat.lt_of_le_of_lt hmul hr
      omega
    simp only [rowBits, slotIdx, slotIndex, he, ite_true, slotStride, slotBlockStride, slotPg,
      slotPage, rowOf, blockOf, inBlock]
    rw [ipat_eq_toNat h0 hbnd]
  · have hf : isExtraBlock b (P.topkLen (eOf L g)) = false := by
      cases h : isExtraBlock b (P.topkLen (eOf L g)) <;> simp_all
    have hidx : slotIdx P L g b l i =
        P.idx (eOf L g) (qOf L g) (slotPos (P.topkLen (eOf L g)) b l i) := by
      simp only [slotIdx, slotIndex, hf, Bool.false_eq_true, ite_false]
    have hlen' : slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b =
        P.topkLen (eOf L g) := by simp [slotLen, hf]
    have hlt : slotPos (P.topkLen (eOf L g)) b l i < P.topk := by omega
    obtain ⟨h0, h1⟩ := hpre.idxRange (eOf L g) hb (qOf L g) hq _
      (by exact ⟨hlen' ▸ hpos, hidx ▸ hne⟩)
    have hbnd : (P.idx (eOf L g) (qOf L g)
        (slotPos (P.topkLen (eOf L g)) b l i)).toNat < 2 ^ 32 := by
      have hpage : P.page ≤ P.blockStride / 528 := by
        have := hpre.pageFits
        omega
      have hmul : P.numBlocks * P.page ≤ P.numBlocks * (P.blockStride / 528) :=
        Nat.mul_le_mul_left _ hpage
      have hr := hpre.rowsRange
      have := Nat.lt_of_le_of_lt hmul hr
      omega
    simp only [rowBits, slotIdx, slotIndex, hf, Bool.false_eq_true, ite_false, slotStride,
      slotBlockStride, slotPg, slotPage, rowOf, blockOf, inBlock]
    rw [ipat_eq_toNat h0 hbnd]

/-- **The `tma_coord` word of a valid slot is the physical row `Data/Indices.rowOf` names** in
the block's own cache geometry. -/
theorem coordWord_rowOf {P : Params} {L : Launch} {mem0 : Mem0} {g b l i : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hblk : b < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hv : validBit P L g b l i = true) :
    coordWord P L g b l i =
      rowOf (slotStride P L g b) (slotPg P L g b)
        (slotIdx P L g b l i) := by
  simp only [coordWord, hv, ite_true]
  exact rowBits_eq_rowOf hpre hb hq hblk hv

/-- The word of an invalid slot is the `-1` marker (`0xffffffff`). -/
theorem coordWord_invalid {P : Params} {L : Launch} {g b l i : Nat}
    (hv : validBit P L g b l i = false) : coordWord P L g b l i = 2 ^ 32 - 1 := by
  simp [coordWord, hv]

/-- **The gather4 coordinate of a valid slot is the physical row of its index**: the word
`coordAt` reads at position `p = 2 * lane + pair` is `Data/Indices.rowOf` of the slot. -/
theorem coordAt_rowOf {P : Params} {L : Launch} {mem0 : Mem0} {g b p : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hblk : b < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hv : validBit P L g b (p / 2) (p % 2) = true) :
    coordAt P L g b p =
      rowOf (slotStride P L g b) (slotPg P L g b)
        (slotIdx P L g b (p / 2) (p % 2)) :=
  coordWord_rowOf hpre hb hq hblk hv

/-- The coordinate of an invalid slot is the `-1` marker. -/
theorem coordAt_invalid {P : Params} {L : Launch} {g b p : Nat}
    (hv : validBit P L g b (p / 2) (p % 2) = false) :
    coordAt P L g b p = 2 ^ 32 - 1 :=
  coordWord_invalid hv

/-! ## The mbarrier objects of `Proof/Protocol/Mbar.lean` -/

/-- The raw ring's two buffers. -/
theorem rawReadyOff_eq (b : Fin 2) : rawReadyOff b.val = (Protocol.Mbar.rawReady b).off := by
  fin_cases b <;> rfl

theorem rawFreeOff_eq (b : Fin 2) : rawFreeOff b.val = (Protocol.Mbar.rawFree b).off := by
  fin_cases b <;> rfl

/-! ## The entry interface and the role's soundness -/

/-- The hand-off from the warpgroup-1 head to the role: a thread state at pc 2162 whose registers
are the prologue's values. `Proof/Thread/Prologue.lean` stops at the first event of warpgroup 1
(pc 1842) and has no hand-off to pc 2162, so this is the interface the role's start needs.

`warp` is the prologue's warp-index broadcast (`%r6 = %tid.x >> 5`, register 464); warp 5 is this
role. `lane` is the prologue's lane index (register 466). `regs` are the launch reads the
prologue's table gives (`%r2 = %ctaid.y`, register 460) and the two parameter-space addresses
(`param_1` in register 2990, `param_0` in 2991). The role forms its shared addresses (the
`wksp_buf` base, the ring slots and the mbarriers) itself from the shared symbol at pcs 2201-2244,
so it needs no shared register in the hand-off. `batch` and `query` are the CTA's place in the
kernel's `(s_q, b, 1)` grid. -/
structure Entry (P : Params) (L : Launch) (g : Nat) (t : TState) : Prop where
  /-- The thread is at pc 2162, before its election initializer. -/
  pc : t.pc = 2162
  /-- The state is at an instruction boundary. -/
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  /-- The thread is warp 5 of warpgroup 1. -/
  warp : t.regs 464 = some (b32 5)
  /-- The thread's lane in its warp (`%r8`). -/
  lane : t.regs 466 = some (b32 (laneOf L g))
  /-- The prologue's launch reads and the two parameter-space addresses, at the prologue's own
  values (`Prologue.values`). -/
  regs : Holds t.regs (factsFrom [460, 2990, 2991]
    (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g))
  /-- The CTA is a batch index of the grid. -/
  batch : ctaidY L g < P.b
  /-- The CTA is a query index of the grid. -/
  query : ctaidX L g < P.s_q

/-- The role's soundness: the entry state reaches the initial abstract state and every abstract
state's event continues to its successor. The entry run from `{}` is not part of it — that run
crosses the prologue's and the warpgroup-1 head's events and belongs to those machines. -/
structure Sound (P : Params) (L : Launch) (g : Nat) : Prop where
  /-- Local instructions from the hand-off reach the initial site's state. -/
  start : ∀ (mem0 : Mem0) (t : TState), Pre P L mem0 → Entry P L g t →
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g)
  /-- Every site's event reaches its successor's state (`Code.StepAt`), or the role's end. -/
  steps : ∀ d, (code P L g).StepAt d

/-- **The entry run**: the three local instructions of pcs 2162-2164 (the election's initializer
moves) reach the election with the initial state's facts. -/
theorem start_of_entry (P : Params) (L : Launch) (g : Nat) {t : TState}
    (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' := by
  have h0 : At t 2162 (factsFrom [460, 2990, 2991]
      (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g)) :=
    ⟨hentry.pc, hentry.sub, hentry.acc, hentry.fault, hentry.regs⟩
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 3 t = some t' ∧
      At t' (Site.elect.pc) (facts P L g (init P L g)) := by
    seg_fp h0 using
      try simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some]
      all_goals (try seg_close)
  exact ⟨t', run_rtg hr, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩⟩

/-- **The site obligation of every state** — the `site` half of `Code.StepAt`: every state sits
at an unguarded event instruction. -/
theorem stepAt_site (P : Params) (L : Launch) (g : Nat) (d : D) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts P L g d) ins.guard :=
  site_event P L g d

/-! ## Evidence from the decoded program

The role's mbarrier addresses, ring slots and raw destinations are the decoded instructions'
immediates, not a restatement of the source. -/

/-- Each four-row destination is 128-byte aligned: the raw block's base and the 2304-byte
offsets are multiples of 128. -/
theorem issueDst_aligned {b : Nat} (hb : b % 128 = 0) (buf k : Nat) :
    (b + issueDst buf k) % 128 = 0 := by
  unfold issueDst rawBase
  omega

/-! ## The last two sites -/

/-- `barrier.sync` fires the arrival on its id register with its count register; the count equal
to the block size is the CTA barrier and carries no count (`barTmpl`). -/
theorem fires_bar_12 {t : TState} (h790 : t.regs 790 = some (b32 12))
    (h791 : t.regs 791 = some (b32 384)) (hb : L.block = 384) :
    eventTmpl asms L g t (.barSyncN (.reg 790) (.reg 791) false) =
      .bar 12 (PTX.next t) none .sync := by
  have h12 : readBits L g t 32 (.reg 790) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h790 (by decide)
  have h384 : readBits L g t 32 (.reg 791) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h791 (by decide)
  simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
    show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
    show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hb,
    show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and,
    or_true, reduceCtorEq]

/-- The invariant at the `ret`: the ring bits carry over, the position and parity fields are
vacuous there, and the block bound holds because the role has left the loop. -/
theorem Inv.exit {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d) :
    Inv P L g { d with site := .exit } := by
  refine ⟨h.phase_lt, h.par_lt, h.buf_lt, h.rpar_lt, ?_, ?_, ?_, ?_, h.len0, h.len1,
    Or.inr (Or.inl rfl), h.batch, trivial⟩
  · intro _ h2
    exact absurd rfl h2
  · intro _ h2
    exact absurd rfl h2
  · intro _ h2
    exact absurd rfl h2
  · intro _ h2
    exact absurd rfl h2

/-- The barrier register values of a state at `.barrier`: `%r790 = 12` and `%r791 = 384`
(pcs 2328 and 2329). -/
theorem barrier_regs (P : Params) (L : Launch) (g : Nat) {d : D} (hd : d.site = .barrier)
    {t : TState} (hat : AtD P L g d t) :
    t.regs 790 = some (b32 12) ∧ t.regs 791 = some (b32 384) := by
  have hpc : d.site.pc = 2330 := by
    rw [hd]
    rfl
  have hm := hat.2.2.2.2
  constructor
  · have := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 790) (by
      rw [hpc]
      decide +kernel))
    simpa [facts, hd, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  · have := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 791) (by
      rw [hpc]
      decide +kernel))
    simpa [facts, hd, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this

/-- No assumption of the kernel's list has a local rule for a branch. -/
theorem asms_localRule_bra {L : Launch} {g : Nat} {t : TState} {target : Nat} {uni : Bool} :
    ∀ a ∈ asms, a.localRule L g t (.bra target uni) = none := by
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Assumption.idealReal_localRule_none (fun f hf => by
      simp [Assumption.FloatForm.ofOp] at hf)
  · exact Assumption.approxExact_localRule_none (fun f hf => by
      simp [Assumption.ApproxForm.ofOp] at hf)
  · simp only [Assumptions.mulBf16x2]
  · simp only [Assumptions.cvtBf16x2]
  · simp only [Assumptions.cvtUe8m0]
  · simp only [Assumptions.lg2Exact]
  · rfl
  · simp only [Assumptions.paramPointers]
    repeat' split
    all_goals rfl
  · rfl
  · simp [Assumptions.sharedBits, Assumptions.deadPackRule]
  · rfl

/-- **The named barrier's step**: the arrival on barrier 12 continues at the `ret` (pc 3611)
through the unconditional branch at 2331. -/
theorem stepAt_barrier {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .barrier) : (code P L g).StepAt d := by
  refine ⟨fun _ => stepAt_site P L g d, ?_⟩
  intro t e u ins hat hinv hc hf
  have hpc' : (code P L g).pc d = Site.barrier.pc := by simp [code, hd]
  rw [hpc'] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_12)
  obtain ⟨h790, h791⟩ := barrier_regs P L g hd hat
  rw [fires_bar_12 (L := L) (g := g) h790 h791 hpre.block] at hf
  obtain ⟨he, hu⟩ := hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have hnext : (code P L g).next d e = some (some { d with site := .exit }) := by
    rw [he]
    simp [code, next, hd]
  have hpc : t.pc = 2330 := by
    rw [hat.1, hpc']
    rfl
  have hsub : t.sub = 0 := by
    have h : (code P L g).sub d = d.site.sub := rfl
    rw [hat.2.1, h, hd]
    rfl
  have hacc : t.acc = [] := by
    rw [hat.2.2.1]
    exact accAt_of_not_coord (fun k j hk => by rw [hd] at hk; exact nomatch hk)
  have h0 : At t 2330 [(790, b32 12), (791, b32 384)] :=
    ⟨hpc, hsub, hacc, hat.2.2.2.1, h790, h791, trivial⟩
  have hec : execLocalA asms L g (PTX.next t) (.bra 3611 false) =
      .ok { PTX.next t with pc := 3611 } := by
    rw [Assumption.SegFreePc.exec (A := asms) (by seg_free_pc) rfl,
      execLocalRule_of_none (asms_localRule_bra (L := L) (g := g) (t := PTX.next t))]
    simp only [execLocal, Op.rule, execBranch, pure, Except.pure]
  have hr : run kernel asms L g 1 (PTX.next t) = some { PTX.next t with pc := 3611 } :=
    run_local Flow.code_2331 rfl (At.next h0) hec
  rw [hu']
  refine Or.inl (Or.inr ⟨{ d with site := .exit }, { PTX.next t with pc := 3611 }, hnext,
    run_rtg hr, ?_⟩)
  refine ⟨⟨?_, ?_, ?_, ?_, trivial⟩, Inv.exit hinv⟩
  · simp only [code]
    rfl
  · have h : (code P L g).sub { d with site := .exit } = 0 := rfl
    rw [h]
    simpa [PTX.next] using h0.2.1
  · have h : (code P L g).acc { d with site := .exit } = [] := rfl
    rw [h]
    simpa [PTX.next] using h0.2.2.1
  · simpa [PTX.next] using h0.2.2.2.1

/-- The `ret` has no continuing event. -/
theorem stepAt_exit {P : Params} {L : Launch} {g : Nat} (d : D) (hd : d.site = .exit) :
    (code P L g).StepAt d := by
  refine ⟨fun _ => stepAt_site P L g d, ?_⟩
  intro t e u ins hat hinv hc hf
  have hpc' : (code P L g).pc d = Site.exit.pc := by simp [code, hd]
  rw [hpc'] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
  obtain ⟨-, hu⟩ := hf
  exact absurd hu (by simp)

/-! ## Reading the facts of a site state -/

/-- The machine's projections on the role's code are its definitions. -/
theorem code_pc (P : Params) (L : Launch) (g : Nat) (d : D) : (code P L g).pc d = d.site.pc :=
  rfl

theorem code_sub (P : Params) (L : Launch) (g : Nat) (d : D) :
    (code P L g).sub d = d.site.sub := rfl

theorem code_acc (P : Params) (L : Launch) (g : Nat) (d : D) :
    (code P L g).acc d = accAt d := rfl

theorem code_facts (P : Params) (L : Launch) (g : Nat) (d : D) :
    (code P L g).facts d = facts P L g d := rfl

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "tma_values" : tactic =>
  `(tactic| simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none,
      sb, qUtccpOff, lastStoreOff, readyOff, coordFreeOff, rawReadyOff, rawFreeOff, coordBase,
      validOff, rawBase, issueDst])

/-- Close a segment's written-register equation: the stated value, or the shared address's
32-bit arithmetic with the ring position `$e` below its bound. -/
macro "tma_close " e:term : tactic =>
  `(tactic| first
    | seg_close [sb]
    | (simp only [sb, b32, Value.bits.injEq, true_and]
       nf_simp [sb]
       interval_cases $e <;> omega))

variable {P : Params} {L : Launch} {g : Nat}

/-- A tracked register live at the state's site holds the table's value. -/
theorem atD_reg {d : D} {t : TState} (h : (code P L g).AtD d t) {r : Nat}
    (hm : r ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  have hh := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) hm)
  simpa [facts] using hh

/-- A register live at a state whose site's pc is `pc`, valued by the facts of state `d`. -/
theorem atD_regAt {d : D} {t : TState} (h : (code P L g).AtD d t) {pc : Nat} (hpc : d.site.pc = pc)
    {r : Nat} (hm : r ∈ (Flow.live pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  subst hpc
  exact atD_reg h hm

/-- A state outside a coordinate load has no pending values, so its concrete states are at an
instruction boundary. -/
theorem atD_acc_nil {d : D} {t : TState} (h : (code P L g).AtD d t)
    (hd : ∀ k j, d.site ≠ .coord k j) : t.acc = [] := by
  rw [h.2.2.1]
  exact accAt_of_not_coord hd

/-- A concrete state of a site state is at the site's instruction boundary. -/
theorem atD_at {d : D} {t : TState} (h : (code P L g).AtD d t) (hsub : d.site.sub = 0)
    (hd : ∀ k j, d.site ≠ .coord k j) :
    At t d.site.pc (facts P L g d) :=
  ⟨h.1, by rw [h.2.1, code_sub]; exact hsub, atD_acc_nil h hd, h.2.2.2.1, h.2.2.2.2⟩

/-- **After a fired poll**: the thread is at the next instruction, its predicate is the poll's
outcome, and every fact of the polling state still holds. -/
theorem at_afterWait {d : D} {t u : TState} (hat : (code P L g).AtD d t) {p : Nat} {ok : Bool}
    (hsub : d.site.sub = 0) (hacc : ∀ k j, d.site ≠ .coord k j)
    (hu : u = PTX.next (setReg t p (.pred ok)))
    (hp : p ∉ (Flow.live d.site.pc).filter (fun r => tracked.contains r)) :
    At u (d.site.pc + 1) ((p, .pred ok) :: facts P L g d) := by
  subst hu
  have hset : At (setReg t p (.pred ok)) d.site.pc
      ((p, .pred ok) :: facts P L g d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show t.pc = d.site.pc
      rw [hat.1, code_pc]
    · show t.sub = 0
      rw [hat.2.1, code_sub]
      exact hsub
    · show t.acc = []
      rw [hat.2.2.1, code_acc]
      exact accAt_of_not_coord hacc
    · show t.fault = none
      exact hat.2.2.2.1
    · rw [holds_cons]
      refine ⟨by simp [setReg], ?_⟩
      refine holds_of_pointwise fun r hr => ?_
      have hne : r ≠ p := fun e => hp (e ▸ hr)
      have h := holds_mem hat.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) hr)
      simpa [setReg, Function.update_of_ne hne] using h
  exact At.next hset

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

/-- The invariant does not read the recorded words. -/
theorem inv_cw {d : D} (h : Inv P L g d) (c : Nat → Value) : Inv P L g { d with cw := c } :=
  ⟨h.phase_lt, h.par_lt, h.buf_lt, h.rpar_lt, h.phase_eq, h.par_eq, h.buf_eq, h.rpar_eq, h.len0,
    h.len1, h.block_le, h.batch, h.lenOk⟩

/-- A change of the next site preserves the invariant (the source is inside the loop). -/
theorem inv_setSite {d : D} (h : Inv P L g d) (hb : d.site ≠ .barrier) (he : d.site ≠ .exit)
    (s : Site) (hs : LenOk L s := by first | exact True.intro | assumption) :
    Inv P L g { d with site := s } := by
  refine ⟨h.phase_lt, h.par_lt, h.buf_lt, h.rpar_lt, ?_, ?_, ?_, ?_, h.len0, h.len1, ?_,
    h.batch, hs⟩
  · intro _ _
    exact h.phase_eq hb he
  · intro _ _
    exact h.par_eq hb he
  · intro _ _
    exact h.buf_eq hb he
  · intro _ _
    exact h.rpar_eq hb he
  · rcases h.block_le with h' | h' | h'
    · exact absurd h' hb
    · exact absurd h' he
    · exact Or.inr (Or.inr h')

/-- The shared window's base is eight-byte aligned, and so is an mbarrier offset: an address
word of the role is an eight-byte aligned shared address. -/
theorem sharedAddr_align {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {off : Nat} (h : off % 8 = 0) : (L.sharedBase + off) % 8 = 0 := by
  have h8 : L.sharedBase % 8 = 0 := by
    rw [hpre.sharedBase]
    have := hpre.sharedAlignment
    omega
  omega

/-- A state at an instruction boundary whose facts are a site's is a concrete state of that
site, when the site carries no pending values. -/
theorem good_of_at {d : D} {t : TState} (h : At t d.site.pc (facts P L g d)) (hsub : d.site.sub = 0)
    (hacc : accAt d = []) (hinv : Inv P L g d) :
    (code P L g).Good (some d) t :=
  ⟨⟨by rw [code_pc]; exact h.1, by rw [code_sub, h.2.1]; exact hsub.symm,
    by rw [code_acc, h.2.2.1, hacc], h.2.2.2.1, h.2.2.2.2⟩, hinv⟩

/-- **The loop's hand-off preserves the invariant**: the two ring positions and parities advance
as the code's 2309-2327 compute them, and the next block is one of the row's. -/
theorem afterFree_inv {d : D} (h : Inv P L g d) (hb : d.site ≠ .barrier) (he : d.site ≠ .exit)
    : Inv P L g (afterFree d) := by
  unfold afterFree
  split
  next hcont =>
    have hphase := h.phase_eq hb he
    have hpar := h.par_eq hb he
    have hbuf := h.buf_eq hb he
    have hrpar := h.rpar_eq hb he
    have hpl := h.phase_lt
    have hprl := h.par_lt
    have hbl := h.buf_lt
    have hrl := h.rpar_lt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.len0, h.len1, Or.inr (Or.inr hcont), h.batch,
      trivial⟩
    · show (d.phase + 1) % 4 < 4
      omega
    · show (if d.phase = 3 then 1 - d.par else d.par) < 2
      split <;> omega
    · show 1 - d.buf < 2
      omega
    · show (if d.rpar = d.buf then 0 else 1) < 2
      split <;> omega
    · intro _ _
      show (d.phase + 1) % 4 = (d.block + 1) % 4
      omega
    · intro _ _
      show (if d.phase = 3 then 1 - d.par else d.par) = (d.block + 1) / 4 % 2
      split <;> omega
    · intro _ _
      show 1 - d.buf = (d.block + 1) % 2
      omega
    · intro _ _
      show (if d.rpar = d.buf then 0 else 1) = (d.block + 1) / 2 % 2
      have hp4 : d.block % 4 = d.phase := hphase.symm
      interval_cases d.phase <;> split <;> omega
  next hcont =>
    refine ⟨h.phase_lt, h.par_lt, h.buf_lt, h.rpar_lt, ?_, ?_, ?_, ?_, h.len0, h.len1,
      Or.inl rfl, h.batch, trivial⟩
    · intro h1 _
      exact absurd rfl h1
    · intro h1 _
      exact absurd rfl h1
    · intro h1 _
      exact absurd rfl h1
    · intro h1 _
      exact absurd rfl h1

/-- A length rounded up to a multiple of 64 that does not exceed a multiple of 64 does not exceed
it. -/
theorem ceilToMultiple_le {n k : Nat} (hn : n ≤ k) (hk : k % 64 = 0) :
    ceilToMultiple n 64 ≤ k := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hk
  unfold ceilToMultiple
  have h1 : (n + 63) / 64 < q + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 64)]
    omega
  omega

/-- The row's padded main-cache length is at most the parameter's budget. -/
theorem origPadded_le {len : Nat} {P : Params} (hlen : len ≤ P.topk) (hdiv : P.topk % 64 = 0)
    (hpos : 0 < P.topk) : origPadded len ≤ P.topk := by
  unfold origPadded topkBlock
  have h64 : 64 ≤ P.topk := by
    rcases Nat.eq_zero_or_pos P.topk with h | h
    · omega
    · have := ceilToMultiple_le hlen hdiv
      have hd : P.topk / 64 * 64 = P.topk := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hdiv)
      have : 0 < P.topk / 64 := by omega
      have : 1 ≤ P.topk / 64 := this
      nlinarith
  have := ceilToMultiple_le hlen hdiv
  omega

/-- The row's padded token count fits signed 32 bits, so its 64-token block count fits 25 bits. -/
theorem totalBlocks_lt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) :
    totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) < 2 ^ 25 := by
  unfold totalBlocks
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < topkBlock)).2 (hpre.paddedRange _ hb)

/-! ## The gather4 arrival's step -/

/-- **The raw ring's expect-tx arrival's step**: the arrival on `bar_raw_ready[buf]` with the
36864-byte count of a raw block (pc 2305) and the two `add`s that form the index ring's free
mbarrier (2306, 2307) reach the release of the index slot. -/
theorem step_rawReady {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .rawReady)
    {t u : TState} {e : Event} {ins : Instr} (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
      (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hpc : d.site.pc = 2305 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_4)
  have h696 : t.regs 696 = some (sb L (rawReadyOff d.buf)) :=
    atD_regAt hat hpc (by decide +kernel)
  have h772 : t.regs 772 = some (b32 36864) :=
    atD_regAt hat hpc (by decide +kernel)
  have hB := sharedBase_lt hpre
  have hphase := hinv.phase_lt
  have hb : L.sharedBase + rawReadyOff d.buf < 2 ^ 32 := by
    have h2 := hinv.buf_lt
    unfold rawReadyOff
    omega
  have hm : mbarLoc L g t 696 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + rawReadyOff d.buf⟩ :=
    mbarLoc_b32 h696 hb (sharedAddr_align hpre (by unfold rawReadyOff; omega))
  obtain ⟨rel', sc', he, hu⟩ := fires_arrive_next (A := asms) (t := t) (base := 696)
    (off := 0) (tx := .reg 772) (count := .imm 1) (cluster := false) (rel := true) (sc := .cta)
    (pc := 2305) (e := e) (o := some u)
    (m := ⟨.shared, g / L.block, L.sharedBase + rawReadyOff d.buf⟩)
    (bytes := truncBits 32 (BitVec.ofInt 64 36864)) (n := truncBits 32 (BitVec.ofInt 64 1))
    hm (readBits_b32 h772 (by decide)) (by simp [readBits, pure, Except.pure]) hf
  have hu' : u = PTX.next t := Option.some.inj hu
  have hnot : ∀ k j, d.site ≠ .coord k j := fun k j hk => by rw [hd] at hk; cases hk
  have hbase : At t 2305 (facts P L g d) := by
    have h := atD_at hat (by rw [hd]; rfl) hnot
    rwa [hpc] at h
  have h0 : At u 2306 (factsFrom ((Flow.live 2305).filter (fun r => tracked.contains r))
      (valueOf P L g d)) := by
    have h1 : At u 2306 (facts P L g d) := by
      rw [hu']
      exact At.next hbase
    simpa only [facts, hpc] using h1
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
      At t' 2308 (facts P L g { d with site := .coordFree }) := by
    seg_fp h0 using
      try tma_values
      all_goals tma_close d.phase
  refine Or.inl (Or.inr ⟨{ d with site := .coordFree }, t', ?_, run_rtg hr,
    good_of_at ht rfl rfl (inv_setSite hinv (by rw [hd]; decide) (by rw [hd]; decide) _)⟩)
  rw [he]
  simp only [next]
  rw [hd]
  have hloc : (⟨Space.shared, g / L.block, L.sharedBase + rawReadyOff d.buf⟩ : Loc) =
      ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ := rfl
  have htx : (truncBits 32 (BitVec.ofInt 64 36864)).toNat = 36864 := by decide
  simp only [hloc, htx, true_and, ↓reduceIte]

/-- **The raw ring's arrival's `StepAt`**: the site's event obligation is `step_rawReady`. -/
theorem stepAt_rawReady {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .rawReady)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun _ hat hinv hc hf => step_rawReady hpre d hd hat hinv hc hf

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The Q-copy poll retries on a failed poll and reaches the previous-store poll on success. -/
theorem stepAt_waitQ {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .waitQ)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2205 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2205)
  have h669 : t.regs 669 = some (sb L qUtccpOff) := atD_regAt hat hpc (by decide +kernel)
  have h670 : t.regs 670 = some (b32 0) := atD_regAt hat hpc (by decide +kernel)
  have hbase : L.sharedBase + qUtccpOff < 2 ^ 32 := by
    have := sharedBase_lt hpre
    unfold qUtccpOff
    omega
  have hm : mbarLoc L g t 669 0 = .ok ⟨.shared, ctaOf L g, L.sharedBase + qUtccpOff⟩ :=
    mbarLoc_b32 h669 hbase (sharedAddr_align hpre (by decide))
  have hq : readBits L g t 32 (.reg 670) = .ok (BitVec.ofNat 64 0) :=
    readBits_b32 h670 (by decide)
  obtain ⟨ok, acq, scope, he, hu⟩ := fires_wait_at_succ hm hq hf
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hacc : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hpred : 4118 ∉ (Flow.live d.site.pc).filter tracked.contains := by rw [hpc]; decide +kernel
  have ha := at_afterWait hat hsub hacc hu hpred
  simp only [facts, hpc] at ha
  cases ok
  · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2205 (facts P L g d) := by
      simp only [facts, hpc]
      seg_fp ha using skip
    rw [← hpc] at ht
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr, good_of_at (d := d) ht hsub
      (accAt_of_not_coord hacc) hinv⟩)
    simp [next, hd, he]
  · let d' := { d with site := Site.waitLast }
    have hwin := sharedBase_lt hpre
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2209 (facts P L g d') := by
      simp only [facts, d', Site.pc, Flow.mbarWait_8]
      seg_fp ha using
        try tma_values
        all_goals seg_close [sb]
    have hi : Inv P L g d' := inv_setSite hinv (by simp [hd]) (by simp [hd]) .waitLast
    refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, good_of_at (d := d') ht rfl rfl hi⟩)
    simp [next, hd, he, d']

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- A nonleader keeps the election flag clear and branches to the idle role. -/
theorem handoff_unelected (d : D) (hd : d.site = .elect) {t u : TState} {e : Event} {ins : Instr}
    (hat : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) {mask inst leader : Nat}
    (hkind : e.kind = .elect mask inst leader) (hne : leader ≠ PTX.laneOf L g) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Entry L g t' := by
  have hpc : d.site.pc = 2165 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2165)
  obtain ⟨mk, instanceId, ld, he, hu⟩ := fires_elect hf
  have hld : ld = leader := by
    rw [he] at hkind
    cases hkind
    rfl
  subst ld
  have hb : (PTX.laneOf L g == leader) = false := by simp [Ne.symm hne]
  rw [hb] at hu
  have hnot : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have ht := atD_at hat (by rw [hd]; rfl) hnot
  have hfacts : facts P L g d =
      [(460, b32 (ctaidY L g)), (662, b32 0), (663, b32 (2 ^ 32 - 1)),
        (2990, .ptr 64 false (.param (param "1")) 0),
        (2991, .ptr 64 false (.param (param "0")) 0)] := by
    rw [facts, hpc, show (Flow.live 2165).filter tracked.contains =
        [460, 662, 663, 2990, 2991] from by decide +kernel]
    rfl
  rw [hpc, hfacts] at ht
  have hu' : At u 2166
      [(4116, b32 leader), (4117, .pred false), (460, b32 (ctaidY L g)), (662, b32 0),
        (663, b32 (2 ^ 32 - 1)), (2990, .ptr 64 false (.param (param "1")) 0),
        (2991, .ptr 64 false (.param (param "0")) 0)] := by
    obtain ⟨htp, hsub, hacc, hfault, hregs⟩ := ht
    rw [hu]
    refine ⟨by simp [PTX.next, setReg, htp], hsub, hacc, hfault, ?_⟩
    simpa [PTX.next, setReg, holds_cons, b32] using hregs
  have hidle : _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.entryFacts L g =
      [(460, b32 (ctaidY L g)), (2991, .ptr 64 false (.param (param "0")) 0)] := by
    unfold _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.entryFacts
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Thread.factsAt
    rw [show Flow.live 2587 = [460, 2991] from by decide +kernel]
    rfl
  obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel asms L g 4 u = some t' ∧
      At t' 2587 [(460, b32 (ctaidY L g)), (2991, .ptr 64 false (.param (param "0")) 0)] := by
    seg_fp hu' using skip
  rw [← hidle] at ht'
  exact ⟨t', run_rtg hr, ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩⟩

private theorem beginLoop_tail {d : D} {u : TState} (hwin : L.sharedBase + 222952 < 2 ^ 32)
    (hmain : numOrigBlocks d.len0 < 2 ^ 32)
    (hu : At u 2220 (factsFrom ((Flow.live 2220).filter tracked.contains)
      (valueOf P L g (beginLoop d)))) :
    ∃ t', run kernel asms L g 14 u = some t' ∧
      At t' 2234 (facts P L g (beginLoop d)) := by
  let F (pc : Nat) := factsFrom ((Flow.live pc).filter tracked.contains)
    (valueOf P L g (beginLoop d))
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 5 u = some t1 ∧ At t1 2225 (F 2225) := by
    dsimp only [F]
    seg_fp hu using
      try tma_values
      all_goals rfl
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧ At t2 2226 (F 2226) := by
    have hpos := numOrigBlocks_pos d.len0
    have hmod : numOrigBlocks d.len0 % 4294967296 = numOrigBlocks d.len0 :=
      Nat.mod_eq_of_lt hmain
    have hmod64 : numOrigBlocks d.len0 % 18446744073709551616 = numOrigBlocks d.len0 :=
      Nat.mod_eq_of_lt (by omega)
    have hcmp : PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 0))
        (truncBits 32 (BitVec.ofNat 64 (numOrigBlocks d.len0))) = true := by
      simp [PTX.compare, truncBits, hmod, hmod64, hpos]
    dsimp only [F] at h1 ⊢
    seg_fp h1 using
      try tma_values
      all_goals
        change (Value.pred (PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 0))
          (truncBits 32 (BitVec.ofNat 64 (numOrigBlocks d.len0)))) =
          .pred (decide (0 < numOrigBlocks d.len0)))
        simp [hcmp, hpos]
  obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧ At t3 2229 (F 2229) := by
    dsimp only [F] at h2 ⊢
    seg_fp h2 using
      try tma_values
      all_goals (try simp only [beginLoop]; rfl)
  obtain ⟨t4, r4, h4⟩ : ∃ t4, run kernel asms L g 5 t3 = some t4 ∧ At t4 2234 (F 2234) := by
    dsimp only [F] at h3 ⊢
    seg_fp h3 using
      try tma_values
      all_goals norm_bits [beginLoop, Nat.zero_add, Nat.add_zero]
  exact ⟨t4, run_comp (run_comp (run_comp r1 r2) r3) r4, h4⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The previous-store poll either retries or initializes both rings at their first slot. -/
theorem stepAt_waitLast {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .waitLast)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2209 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2209)
  have h672 : t.regs 672 = some (sb L lastStoreOff) := atD_regAt hat hpc (by decide +kernel)
  have h670 : t.regs 670 = some (b32 0) := atD_regAt hat hpc (by decide +kernel)
  have hwin := sharedBase_lt hpre
  have hbase : L.sharedBase + lastStoreOff < 2 ^ 32 := by unfold lastStoreOff; omega
  have hm : mbarLoc L g t 672 0 = .ok ⟨.shared, ctaOf L g, L.sharedBase + lastStoreOff⟩ :=
    mbarLoc_b32 h672 hbase (sharedAddr_align hpre (by decide))
  have hq : readBits L g t 32 (.reg 670) = .ok (BitVec.ofNat 64 0) :=
    readBits_b32 h670 (by decide)
  obtain ⟨ok, acq, scope, he, hu⟩ := fires_wait_at_succ hm hq hf
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hacc : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hpred : 4119 ∉ (Flow.live d.site.pc).filter tracked.contains := by rw [hpc]; decide +kernel
  have ha := at_afterWait hat hsub hacc hu hpred
  simp only [facts, hpc] at ha
  cases ok
  · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2209 (facts P L g d) := by
      simp only [facts, hpc]
      seg_fp ha using skip
    rw [← hpc] at ht
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr, good_of_at (d := d) ht hsub
      (accAt_of_not_coord hacc) hinv⟩)
    simp [next, hd, he]
  · let d' := beginLoop d
    let F (pc : Nat) := factsFrom ((Flow.live pc).filter tracked.contains) (valueOf P L g d')
    let n := origPadded d.len0 + ceilToMultiple d.len1 topkBlock
    have h64 : 64 ≤ n := by
      unfold n origPadded topkBlock
      have h := le_max_right (ceilToMultiple d.len0 64) 64
      omega
    have h31 : n < 2 ^ 31 := by
      unfold n
      rw [hinv.len0, hinv.len1]
      exact hpre.paddedRange _ hinv.batch
    have ho31 : origPadded d.len0 < 2 ^ 31 := by
      dsimp [n] at h31
      omega
    have hblocks := totalBlocks_pos d.len0 d.len1
    have hblocks_eq : totalBlocks d.len0 d.len1 = n / 64 := rfl
    have hmain_eq : numOrigBlocks d.len0 = origPadded d.len0 / 64 := rfl
    obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 2 u = some t1 ∧
        At t1 2213 ((51, .pred false) :: F 2213) := by
      dsimp only [F]
      seg_fp ha using
        try tma_values
        all_goals first | rfl | norm_signed [n, h64, h31]
    obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
        At t2 2214 (F 2214) := by
      dsimp only [F] at h1 ⊢
      seg_fp h1 using skip
    obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 6 t2 = some t3 ∧
        At t3 2220 (F 2220) := by
      dsimp only [F] at h2 ⊢
      seg_fp h2 using
        try tma_values
        all_goals first | rfl | norm_signed [d', beginLoop, n, h31, ho31,
          hblocks_eq, hmain_eq, hblocks]
    have hmain32 : numOrigBlocks d.len0 < 2 ^ 32 := by rw [hmain_eq]; omega
    obtain ⟨t4, r4, h4⟩ := beginLoop_tail hwin hmain32 h3
    have hat' : At t4 d'.site.pc (facts P L g d') := h4
    have hinv' : Inv P L g d' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv.len0, hinv.len1, .inr (.inr hblocks), hinv.batch,
        trivial⟩
      all_goals simp [d', beginLoop]
    refine Or.inl (Or.inr ⟨d', t4, ?_, run_rtg (run_comp (run_comp (run_comp r1 r2) r3) r4),
      good_of_at (d := d') hat' rfl rfl hinv'⟩)
    simp [next, hd, he, d', Nat.ne_of_gt hblocks]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The index-ready poll retries or computes the raw buffer's free-barrier operands. -/
theorem stepAt_waitCoord {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .waitCoord)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2234 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2234)
  have h685 : t.regs 685 = some (sb L (readyOff d.phase)) := atD_regAt hat hpc (by decide +kernel)
  have h686 : t.regs 686 = some (b32 d.par) := atD_regAt hat hpc (by decide +kernel)
  have hwin := sharedBase_lt hpre
  have hp := hinv.phase_lt
  have hbuf := hinv.buf_lt
  have hrpar := hinv.rpar_lt
  have hbase : L.sharedBase + readyOff d.phase < 2 ^ 32 := by unfold readyOff; omega
  have hm : mbarLoc L g t 685 0 =
      .ok ⟨.shared, ctaOf L g, L.sharedBase + readyOff d.phase⟩ :=
    mbarLoc_b32 h685 hbase (sharedAddr_align hpre (by unfold readyOff; omega))
  have hq := readBits_b32 (L := L) (g := g) h686 (by have := hinv.par_lt; omega)
  obtain ⟨ok, acq, scope, he, hu⟩ := fires_wait_at_succ hm hq hf
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hacc : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hpred : 4120 ∉ (Flow.live d.site.pc).filter tracked.contains := by rw [hpc]; decide +kernel
  have ha := at_afterWait hat hsub hacc hu hpred
  simp only [facts, hpc] at ha
  cases ok
  · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2234 (facts P L g d) := by
      simp only [facts, hpc]
      seg_fp ha using skip
    rw [← hpc] at ht
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr, good_of_at (d := d) ht hsub
      (accAt_of_not_coord hacc) hinv⟩)
    simp [next, hd, he]
  · let d' := { d with site := Site.waitFree }
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 9 u = some t' ∧
        At t' 2245 (facts P L g d') := by
      simp only [facts, d', Site.pc, Flow.mbarWait_10]
      seg_fp ha using
        try tma_values
        all_goals first
          | with_reducible rfl
          | (interval_cases d.rpar <;> decide +kernel)
          | (interval_cases d.buf <;> first | decide +kernel | norm_bits [sb])
    have hi : Inv P L g d' := inv_setSite hinv (by simp [hd]) (by simp [hd]) .waitFree
    refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, good_of_at (d := d') ht rfl rfl hi⟩)
    simp [next, hd, he, d']

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The raw-free poll retries or selects the KV map and addresses the first coordinate group. -/
theorem stepAt_waitFree {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .waitFree)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2245 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2245)
  have h688 : t.regs 688 = some (sb L (rawFreeOff d.buf)) := atD_regAt hat hpc (by decide +kernel)
  have h689 : t.regs 689 = some (b32 (1 - d.rpar)) := atD_regAt hat hpc (by decide +kernel)
  have hwin := sharedBase_lt hpre
  have hphase := hinv.phase_lt
  have hbuf := hinv.buf_lt
  have hbase : L.sharedBase + rawFreeOff d.buf < 2 ^ 32 := by unfold rawFreeOff; omega
  have hm : mbarLoc L g t 688 0 =
      .ok ⟨.shared, ctaOf L g, L.sharedBase + rawFreeOff d.buf⟩ :=
    mbarLoc_b32 h688 hbase (sharedAddr_align hpre (by unfold rawFreeOff; omega))
  have hq := readBits_b32 (L := L) (g := g) h689 (by omega)
  obtain ⟨ok, acq, scope, he, hu⟩ := fires_wait_at_succ hm hq hf
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hacc : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hpred : 4121 ∉ (Flow.live d.site.pc).filter tracked.contains := by rw [hpc]; decide +kernel
  have ha := at_afterWait hat hsub hacc hu hpred
  simp only [facts, hpc] at ha
  cases ok
  · obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 u = some t' ∧
        At t' 2245 (facts P L g d) := by
      simp only [facts, hpc]
      seg_fp ha using skip
    rw [← hpc] at ht
    refine Or.inl (Or.inr ⟨d, t', ?_, run_rtg hr, good_of_at (d := d) ht hsub
      (accAt_of_not_coord hacc) hinv⟩)
    simp [next, hd, he]
  · let d' := { d with site := Site.coord 0 0 }
    have hphase32 : d.phase % 4294967296 = d.phase := Nat.mod_eq_of_lt (by omega)
    have hbase32 : (L.sharedBase + 8 * d.phase) % 4294967296 = L.sharedBase + 8 * d.phase :=
      Nat.mod_eq_of_lt (by omega)
    have hcoord32 : (L.sharedBase + 256 * d.phase) % 4294967296 =
        L.sharedBase + 256 * d.phase := Nat.mod_eq_of_lt (by omega)
    have hcoord64 : (L.sharedBase + 256 * d.phase) % 18446744073709551616 =
        L.sharedBase + 256 * d.phase := Nat.mod_eq_of_lt (by omega)
    have hcoord : d.phase * 248 + (L.sharedBase + 8 * d.phase) =
        L.sharedBase + 256 * d.phase := by omega
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 3 u = some t' ∧
        At t' 2250 (facts P L g d') := by
      rw [facts, show d'.site.pc = 2250 by rfl]
      let live := (Flow.live 2245).filter tracked.contains
      have hlive : live = 52 :: live.drop 1 := by decide +kernel
      change At u 2246 ((4121, .pred true) :: factsFrom live (valueOf P L g d)) at ha
      rw [hlive] at ha
      change At u 2246 ((4121, .pred true) ::
        (52, .pred (decide (d.block < numOrigBlocks d.len0))) ::
        factsFrom (live.drop 1) (valueOf P L g d)) at ha
      by_cases h : d.block < numOrigBlocks d.len0 <;>
        simp only [h, decide_true, decide_false] at ha <;> seg_fp ha using
          try tma_values
          all_goals norm_bits [d', h, hphase32, hbase32, hcoord32, hcoord64, hcoord]
    have hi : Inv P L g d' := inv_setSite hinv (by simp [hd]) (by simp [hd]) (.coord 0 0)
    refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, good_of_at (d := d') ht rfl rfl hi⟩)
    simp [next, hd, he, d']

/-- A four-word load of coordinates from one aligned group in the index ring. -/
def coordLoad (k : Fin 16) : MemAccess :=
  { kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 4,
    addr := { base := .reg 782 32, off := Int.ofNat (221728 + 16 * k.val) },
    dsts := ((coordRegs.drop (4 * k.val)).take 4).map some }

theorem coordLoad_code (k : Fin 16) (j : Fin 4) :
    kernel.code[(Site.coord k j).pc]? =
      some { guard := none, op := .mem (coordLoad k) } := by
  fin_cases k
  · exact Flow.code_2250
  · exact Flow.code_2254
  · exact Flow.code_2260
  · exact Flow.code_2263
  · exact Flow.code_2266
  · exact Flow.code_2269
  · exact Flow.code_2272
  · exact Flow.code_2275
  · exact Flow.code_2278
  · exact Flow.code_2281
  · exact Flow.code_2284
  · exact Flow.code_2287
  · exact Flow.code_2290
  · exact Flow.code_2293
  · exact Flow.code_2296
  · exact Flow.code_2299

private theorem coordLoad_regs (k : Fin 16) : (coordLoad k).regs.length = 4 := by
  fin_cases k <;> decide

private theorem coordLoad_rule (k : Fin 16) : (coordLoad k).rule = some .threadAccess := by
  fin_cases k <;> decide

/-- The pending coordinate load has the defined footprint of its current vector element. -/
theorem coord_read_template {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} {t : TState} {k : Fin 16}
    {j : Fin 4} (hd : d.site = .coord k j) (hat : (code P L g).AtD d t) (hinv : Inv P L g d) :
    eventTmpl asms L g t (.mem (coordLoad k)) =
      .read { loc := ⟨.shared, ctaOf L g,
        L.sharedBase + coordBase d.phase + 16 * k.val + 4 * j.val⟩, size := 4, elem := j.val }
        (afterLoad t (coordLoad k).regs) := by
  let a := L.sharedBase + 256 * d.phase
  let off := 221728 + 16 * k.val
  have hmem : 782 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    simp only [Site.pc]
    fin_cases k <;> decide +kernel
  have hr : t.regs 782 = some (b32 a) := atD_reg hat hmem
  have hlt : a + off < 2 ^ 32 := by
    have := sharedBase_lt hpre
    have := hinv.phase_lt
    have := k.isLt
    simp only [a, off]
    omega
  have hal : (a + off) % 16 = 0 := by
    have hb : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
    simp only [a, off]
    omega
  have hsum : a + off + 4 * j.val =
      L.sharedBase + coordBase d.phase + 16 * k.val + 4 * j.val := by
    simp only [a, off, coordBase]
    omega
  have hsub : t.sub = j.val := by rw [hat.2.1, code_sub, hd]; rfl
  have ht : eventTmpl asms L g t (.mem (coordLoad k)) =
      loadTmpl asms L g t .shared false 32 (coordLoad k).regs 782 (off : Int) := by
    change memTmpl asms L g t (coordLoad k) = _
    rw [memTmpl_direct_weakLoad (sp := .shared) (base := 782) (w := 32)
      (coordLoad_rule k) rfl rfl rfl rfl]
    rfl
  rw [ht]
  simp only [loadTmpl, effAddr_b32_off hr hlt, bind, Except.bind, coordLoad_regs,
    Bool.false_eq_true, ↓reduceIte, hsub]
  rw [elemAcc_ok (by decide) (by simpa using hal)]
  simp only [Loc.at, hsum, ctaOf]

/-- Each vector read names the four-byte coordinate element in the current index slot. -/
theorem fires_coord {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} {t : TState} {e : Event}
    {o : Option TState} {k : Fin 16} {j : Fin 4} (hd : d.site = .coord k j)
    (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hf : Fires d.site.pc (eventTmpl asms L g t (.mem (coordLoad k))) e o) :
    ∃ bs, e = ⟨d.site.pc, .rd { loc := ⟨.shared, ctaOf L g,
      L.sharedBase + coordBase d.phase + 16 * k.val + 4 * j.val⟩, size := 4, elem := j.val } bs⟩ ∧
      o = some (afterLoad t (coordLoad k).regs bs) := by
  rw [coord_read_template hpre hd hat hinv] at hf
  obtain ⟨bs, -, he, ho⟩ := hf
  exact ⟨bs, he, ho⟩

/-- The destinations of a coordinate load are not live at it, so recording a word of the load
changes no fact of its site. -/
private theorem coordLoad_dead (k : Fin 16) :
    ((Flow.live (Site.coord k 0).pc).filter tracked.contains).all
      (fun r => !(coordLoad k).regs.contains r) = true := by
  simp only [Site.pc]
  fin_cases k <;> decide +kernel

private theorem coordLoad_reg (k : Fin 16) (j : Fin 4) :
    coordRegs.getD (coordPos k.val j.val) 0 ∈ (coordLoad k).regs := by
  revert k j
  decide

/-- Recording word `q` keeps the value of every register other than the word's own. -/
private theorem valueOf_update {d : D} {q : Nat} {v : Value} {r : Nat}
    (hq : coordRegs.getD q 0 ≠ r) :
    valueOf P L g { d with cw := Function.update d.cw q v } r = valueOf P L g d r := by
  refine valueOf_cw fun x hx hr => ?_
  have hne : x.2 ≠ q := by
    rintro hxq
    exact hq (by rw [← hxq, coordKeys_reg x hx, hr])
  exact Function.update_of_ne hne _ _

/-- The pending words of a coordinate load after one more element. -/
private theorem acc_update {d : D} {k : Fin 16} {j : Nat} {v : Value} :
    (List.range j).map (fun i => d.cw (coordPos k.val i)) ++ [v] =
      (List.range (j + 1)).map
        (fun i => Function.update d.cw (coordPos k.val j) v (coordPos k.val i)) := by
  rw [List.range_succ, List.map_append]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [Function.update_of_ne (by unfold coordPos; omega)]
  · simp

/-- Each non-final coordinate word stays in the accumulator until the vector load writes its
four destination registers. A read whose bytes do not rebuild faults the thread. -/
theorem stepAt_coordMid {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {k : Fin 16} {j : Fin 4}
    (hd : d.site = .coord k j) (hj : j.val + 1 < 4) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hi : kernel.code[d.site.pc]? = some { guard := none, op := .mem (coordLoad k) } := by
    rw [hd]
    exact coordLoad_code k j
  obtain rfl := Option.some.inj (hc.symm.trans hi)
  obtain ⟨bs, he, hu⟩ := fires_coord hpre hd hat hinv hf
  have huLoad := Option.some.inj hu
  rcases hrb : rebuild 3 bs with f | v
  · refine Or.inr ⟨by simp [next, hd, he, hrb], ?_⟩
    rw [huLoad]
    exact Machine.dead_of_fault (f := f) (by simp [afterLoad, hrb])
  let d' := { d with site := Site.coord k ⟨j.val + 1, hj⟩,
                     cw := Function.update d.cw (coordPos k.val j.val) v }
  have hn : next P L g d e = some (some d') := by
    simp [next, hd, he, hrb, d', afterCoord, hj]
  have huSub : t.sub = j.val := by rw [hat.2.1, code_sub, hd]; rfl
  have hu' := huLoad.trans (afterLoad_mid hrb (by rw [huSub, coordLoad_regs]; exact hj))
  have hb : d.site ≠ .barrier := by simp [hd]
  have hret : d.site ≠ .exit := by simp [hd]
  have hGood : (code P L g).AtD d' u := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hu', code_pc]
      change t.pc = (Site.coord k ⟨j.val + 1, hj⟩).pc
      rw [hat.1, code_pc, hd]
      rfl
    · rw [hu', code_sub]
      exact congrArg (· + 1) huSub
    · rw [hu', code_acc, accAt_of_coord (d := d') rfl]
      change t.acc ++ [v] = _
      rw [hat.2.2.1, code_acc, accAt_of_coord hd]
      exact acc_update
    · rw [hu']
      exact hat.2.2.2.1
    · rw [hu', code_facts]
      have hpc : d'.site.pc = d.site.pc := by rw [hd]; rfl
      have heq : facts P L g d' = facts P L g d := by
        unfold facts
        rw [hpc]
        refine List.map_congr_left fun r hr => ?_
        have hdead := List.all_eq_true.mp (coordLoad_dead k) r (by
          rw [hd] at hr; simpa only [Site.pc] using hr)
        have hq : coordRegs.getD (coordPos k.val j.val) 0 ≠ r := by
          rintro rfl
          rw [List.contains_iff_mem.mpr (coordLoad_reg k j)] at hdead
          exact absurd hdead (by decide)
        have hs : valueOf P L g d' r =
            valueOf P L g { d with cw := Function.update d.cw (coordPos k.val j.val) v } r := by
          cases d with
          | mk site block phase par buf rpar len0 len1 cw =>
            simp only at hd
            subst site
            rfl
        rw [hs, valueOf_update hq]
      rw [heq]
      exact hat.2.2.2.2
  exact Or.inl (Or.inr ⟨d', u, hn, .refl, hGood, inv_cw (inv_setSite hinv hb hret d'.site) _⟩)

private theorem coordLoad_nodup (k : Fin 16) : (coordLoad k).regs.Nodup := by
  fin_cases k <;> decide

private theorem coordLoad_value {d : D} (k : Fin 16) (p : Fin 4) :
    valueOf P L g d ((coordLoad k).regs.getD p.val 0) = d.cw (coordPos k.val p.val) := by
  fin_cases k <;> fin_cases p <;> rfl

private theorem coordLoad_cover (k : Fin 16) (j : Fin 4) :
    ((Flow.live ((Site.coord k j).pc + 1)).filter tracked.contains).all
      (fun r => (coordLoad k).regs.contains r ||
        ((Flow.live (Site.coord k j).pc).filter tracked.contains).contains r) = true := by
  simp only [Site.pc]
  fin_cases k <;> decide +kernel

/-- The fourth word of a coordinate load writes its four destinations with the recorded words. -/
private theorem coordFinal_at {d : D} {t u : TState} {k : Fin 16} {j : Fin 4}
    (hd : d.site = .coord k j) (hj : ¬ j.val + 1 < 4) (hat : (code P L g).AtD d t)
    {bs : List (Option Byte)} {v : Value} (hread : rebuild 3 bs = .ok v)
    (hu : u = afterLoad t (coordLoad k).regs bs) :
    At u ((Site.coord k j).pc + 1)
      (factsFrom ((Flow.live ((Site.coord k j).pc + 1)).filter tracked.contains)
        (valueOf P L g { d with cw := Function.update d.cw (coordPos k.val j.val) v })) := by
  let dc := { d with cw := Function.update d.cw (coordPos k.val j.val) v }
  have hsub : t.sub = j.val := by rw [hat.2.1, code_sub, hd]; rfl
  have helem : j.val + 1 = 4 := by have := j.isLt; omega
  let xs := (List.range 4).map fun p => dc.cw (coordPos k.val p)
  have hxs : t.acc ++ [v] = xs := by
    rw [hat.2.2.1, code_acc, accAt_of_coord hd, acc_update]
    simp only [xs, dc, helem]
  have hupdate := afterLoad_last (t := t) (ds := (coordLoad k).regs) hread
    (by rw [hsub, coordLoad_regs]; exact hj)
  rw [hu, hupdate, hxs]
  have hskel := setRegs_skel t (coordLoad k).regs xs
  refine ⟨?_, rfl, rfl, hskel.2.2.2.trans hat.2.2.2.1, ?_⟩
  · have htpc := hat.1
    rw [code_pc, hd] at htpc
    exact congrArg (· + 1) htpc
  change Holds (setRegs t (coordLoad k).regs xs).regs _
  have hw := holds_setRegs t (coordLoad k).regs xs (valueOf P L g dc)
    (coordLoad_nodup k) (by simp [coordLoad_regs, xs]) (by
      intro p hp
      rw [coordLoad_regs] at hp
      simp only [xs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
        Option.map_some, Option.getD_some]
      exact coordLoad_value (d := dc) k ⟨p, hp⟩)
  refine holds_of_pointwise fun r hr => ?_
  by_cases hwrote : r ∈ (coordLoad k).regs
  · exact holds_mem hw (mem_factsFrom hwrote)
  · have hcovered := (List.all_eq_true.mp (coordLoad_cover k j)) r hr
    simp only [Bool.or_eq_true, List.contains_iff_mem, hwrote, false_or] at hcovered
    rw [setRegs_other t _ xs r hwrote]
    have hq : coordRegs.getD (coordPos k.val j.val) 0 ≠ r := by
      rintro rfl
      exact hwrote (coordLoad_reg k j)
    rw [atD_regAt hat (congrArg Site.pc hd) hcovered, ← valueOf_update hq]

private theorem run_kvParamAdd {mem0 : Mem0} {d : D} {t : TState} {F : List (Nat × Value)}
    (hpre : Pre P L mem0) (h : At t 2256 F)
    (hmap : t.regs 3052 = some (.ptr 64 true (.param (param "1")) 0))
    (hoff : t.regs 3051 = some (b64 (kvOff d))) :
    run kernel asms L g 1 t =
      some (PTX.next (setReg t 3049 (b64 (P.param1Base + kvOff d)))) := by
  have he : (BitVec.ofNat 64 (kvOff d)).toNat = kvOff d :=
    toNat_ofNat_lt (by unfold kvOff; split <;> decide)
  refine run_paramRule Flow.code_2256 h rfl ?_
  have hpc : t.pc = 2256 := h.1
  have hcon : paramAdds.contains 2256 = true := by decide +kernel
  simp only [Assumptions.all, List.findSome?_cons, Assumptions.idealArith,
    Assumptions.approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0,
    Assumptions.lg2Exact, Assumptions.ncReadOnly, Assumption.idealReal, Assumption.approxExact,
    Assumption.ncReadOnly, Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp,
    Assumptions.storeDrain, Assumptions.paramPointers, hpc, hcon, readReg, hmap, hoff, b64,
    Assumptions.offsetOf, he, pure, Except.pure]
  simp [hpre.param1Object]

private theorem coordTailOne {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) :
    Seg kernel asms L g 4 2255
      (factsFrom ((Flow.live 2255).filter tracked.contains) (valueOf P L g d))
      2259 (facts P L g { d with site := .issue 0 }) := by
  intro t ht
  let F := factsFrom ((Flow.live 2255).filter tracked.contains) (valueOf P L g d)
  have h2990 : t.regs 2990 = some (.ptr 64 false (.param (param "1")) 0) :=
    holds_mem ht.2.2.2.2 (mem_factsFrom (by decide +kernel))
  let t1 := PTX.next (setReg t 3052 (.ptr 64 true (.param (param "1")) 0))
  have hr1 : run kernel asms L g 1 t = some t1 := run_cvtaParam Flow.code_2255 ht h2990
  have ht1 : At t1 2256 ((3052, .ptr 64 true (.param (param "1")) 0) :: F) :=
    At.set ht (not_mem_factsFrom (by decide +kernel))
  have h3051 : t1.regs 3051 = some (b64 (kvOff d)) :=
    holds_mem ht1.2.2.2.2 (List.mem_cons_of_mem _ (mem_factsFrom (by decide +kernel)))
  have h3052 : t1.regs 3052 = some (.ptr 64 true (.param (param "1")) 0) :=
    holds_mem ht1.2.2.2.2 (by simp)
  let t2 := PTX.next (setReg t1 3049 (valueOf P L g d 3049))
  have hr2 : run kernel asms L g 1 t1 = some t2 := by
    have hbound := hpre.param1Range
    have hkv : kvOff d < 1024 := by unfold kvOff; split <;> decide
    have haddr : (P.param1Base + kvOff d) % 2 ^ 64 = P.param1Base + kvOff d :=
      Nat.mod_eq_of_lt (by omega)
    simp only [t2, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, haddr]
    exact run_kvParamAdd hpre ht1 h3052 h3051
  have ht2 : At t2 2257
      ((3049, valueOf P L g d 3049) :: (3052, .ptr 64 true (.param (param "1")) 0) :: F) :=
    At.set ht1 (not_mem_facts_cons (by decide) (not_mem_factsFrom (by decide +kernel)))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
      At t3 2259 (facts P L g { d with site := .issue 0 }) := by
    dsimp only [F] at ht2
    seg_fp ht2 using
      tma_values
      all_goals rfl
  exact ⟨t3, run_comp (run_comp hr1 hr2) hr3, ht3⟩

private def coordTailLen (k : Fin 16) : Nat :=
  if k.val = 0 then 3 else if k.val = 1 then 4 else 1

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem coordFinalTail {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hbuf : d.buf < 2)
    (k : Fin 16) (j : Fin 4) (hj : ¬ j.val + 1 < 4) :
    Seg kernel asms L g (coordTailLen k) ((Site.coord k j).pc + 1)
      (factsFrom ((Flow.live ((Site.coord k j).pc + 1)).filter tracked.contains) (valueOf P L g d))
      (afterCoord k j).pc (facts P L g { d with site := afterCoord k j }) := by
  have hwin := sharedBase_lt hpre
  have hmod32 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 4294967296 = L.sharedBase + off := Nat.mod_eq_of_lt (by omega)
  have hmod64 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 18446744073709551616 = L.sharedBase + off :=
    Nat.mod_eq_of_lt (by omega)
  have hbuf32 : d.buf % 4294967296 = d.buf := Nat.mod_eq_of_lt (by omega)
  have hmad : d.buf * 36856 + (L.sharedBase + 8 * d.buf) =
      L.sharedBase + 36864 * d.buf := by omega
  simp only [afterCoord, hj, ↓reduceDIte]
  fin_cases k
  · intro u hu
    seg_fp hu using
      try tma_values
      all_goals
        nf_simp [hbuf32, Nat.add_assoc]
        simp (discharger := omega) only [hmod32, hmod64, hmad, Nat.add_assoc]
        all_goals omega
  · exact coordTailOne (d := d) hpre
  all_goals
    intro u hu
    seg_fp hu using
      try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
        sb, rawBase, issueDst]
      all_goals
        nf_simp [Nat.add_assoc]
        simp (discharger := omega) only [hmod32, hmod64, Nat.add_assoc]
        all_goals omega

/-- The fourth coordinate word writes the vector destinations and reaches the next load or issue. -/
theorem stepAt_coordLast {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {k : Fin 16} {j : Fin 4}
    (hd : d.site = .coord k j) (hj : ¬ j.val + 1 < 4) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hci : kernel.code[d.site.pc]? = some { guard := none, op := .mem (coordLoad k) } := by
    rw [hd]
    exact coordLoad_code k j
  obtain rfl := Option.some.inj (hc.symm.trans hci)
  obtain ⟨bs, he, hu⟩ := fires_coord hpre hd hat hinv hf
  rcases hrb : rebuild 3 bs with f | v
  · refine Or.inr ⟨by simp [next, hd, he, hrb], ?_⟩
    rw [Option.some.inj hu]
    exact Machine.dead_of_fault (f := f) (by simp [afterLoad, hrb])
  let dc := { d with cw := Function.update d.cw (coordPos k.val j.val) v }
  have hat' := coordFinal_at hd hj hat hrb (Option.some.inj hu)
  obtain ⟨t', hr, ht⟩ := coordFinalTail (d := dc) hpre hinv.buf_lt k j hj u hat'
  let d' := { dc with site := afterCoord k j }
  have hsub : d'.site.sub = 0 := by
    simp only [d', afterCoord, hj, ↓reduceDIte]
    split <;> rfl
  have hacc : accAt d' = [] := by
    simp only [d', afterCoord, hj, ↓reduceDIte]
    split <;> rfl
  have hi : Inv P L g d' :=
    inv_setSite (d := dc) (inv_cw hinv _) (by simp [dc, hd]) (by simp [dc, hd]) d'.site
      (by simp only [d', afterCoord, hj, ↓reduceDIte]; split <;> exact True.intro)
  refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr,
    good_of_at (d := d') ht hsub hacc hi⟩)
  simp [next, hd, he, hrb, d', dc]

/-- The decoded gather4 instruction for the given coordinate group. -/
def issueInstr (k : Fin 16) : Instr :=
  { guard := none,
    op := .cpTensor false false (issueRegs.getD k.val 0) 0 (.reg 3049)
      (.reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg)
      696 0 none .fourRows (some (.reg 3050)) }

theorem issueInstr_code (k : Fin 16) :
    kernel.code[(Site.issue k).pc]? = some (issueInstr k) := by
  fin_cases k
  · exact Flow.code_tensorCopy_12
  · exact Flow.code_tensorCopy_13
  · exact Flow.code_tensorCopy_14
  · exact Flow.code_tensorCopy_15
  · exact Flow.code_tensorCopy_16
  · exact Flow.code_tensorCopy_17
  · exact Flow.code_tensorCopy_18
  · exact Flow.code_tensorCopy_19
  · exact Flow.code_tensorCopy_20
  · exact Flow.code_tensorCopy_21
  · exact Flow.code_tensorCopy_22
  · exact Flow.code_tensorCopy_23
  · exact Flow.code_tensorCopy_24
  · exact Flow.code_tensorCopy_25
  · exact Flow.code_tensorCopy_26
  · exact Flow.code_tensorCopy_27

private theorem issueLive (k : Fin 16) :
    ([3049, 3050, 696, issueRegs.getD k.val 0] ++ (coordLoad k).regs).all
      ((Flow.live (Site.issue k).pc).filter tracked.contains).contains = true := by
  fin_cases k <;> decide +kernel

private theorem issueLive_mem (k : Fin 16) (r : Nat)
    (hr : r ∈ [3049, 3050, 696, issueRegs.getD k.val 0] ++ (coordLoad k).regs) :
    r ∈ (Flow.live (Site.issue k).pc).filter tracked.contains :=
  List.contains_iff_mem.mp (List.all_eq_true.mp (issueLive k) r hr)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem issueTail {d : D} (hwin : L.sharedBase + 222952 < 2 ^ 32) (hbuf : d.buf < 2)
    (k : Fin 16) :
    Seg kernel asms L g (if k.val < 14 then 0 else 1) ((Site.issue k).pc + 1)
      (factsFrom ((Flow.live (Site.issue k).pc).filter tracked.contains) (valueOf P L g d))
      (afterIssue k).pc (facts P L g { d with site := afterIssue k }) := by
  have hmod32 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 4294967296 = L.sharedBase + off := Nat.mod_eq_of_lt (by omega)
  have hmod64 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 18446744073709551616 = L.sharedBase + off :=
    Nat.mod_eq_of_lt (by omega)
  fin_cases k <;> intro u h <;> seg_fp h using
    try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
      sb, issueDst, rawBase]
    all_goals
      nf_simp [Nat.add_assoc]
      all_goals
        simp (discharger := omega) only [hmod32, hmod64, Nat.add_assoc]
        all_goals omega

/-- A gather4 issue completes on the current raw slot's barrier, then advances to the next
coordinate load, the last gather4 issue, or the raw-ready arrival. -/
theorem stepAt_issue {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) {k : Fin 16}
    (hd : d.site = .issue k) :
    (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hci : kernel.code[d.site.pc]? = some (issueInstr k) := by
    rw [hd]
    exact issueInstr_code k
  obtain rfl := Option.some.inj (hc.symm.trans hci)
  have h696 : 696 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    exact issueLive_mem k 696 (by simp)
  have hmreg : t.regs 696 = some (sb L (rawReadyOff d.buf)) := atD_reg hat h696
  have hwin := sharedBase_lt hpre
  have hbuf := hinv.buf_lt
  have hmlt : L.sharedBase + rawReadyOff d.buf < 2 ^ 32 := by unfold rawReadyOff; omega
  have hm := mbarLoc_b32 (L := L) (g := g) hmreg hmlt
    (sharedAddr_align hpre (by unfold rawReadyOff; omega))
  obtain ⟨a, s, he, hu, hs⟩ := fires_cpTensor_issue (A := asms) hf
  have hm' : s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ :=
    Except.ok.inj (hs.symm.trans hm)
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hnot : ∀ k' j', d.site ≠ .coord k' j' := by intro k' j'; simp [hd]
  have hu' : At u ((Site.issue k).pc + 1)
      (factsFrom ((Flow.live (Site.issue k).pc).filter tracked.contains) (valueOf P L g d)) := by
    rw [hu]
    have h := At.next (atD_at hat hsub hnot)
    simpa only [facts, hd] using h
  obtain ⟨t', hr, ht⟩ := issueTail hwin hbuf k u hu'
  let d' := { d with site := afterIssue k }
  have hsub' : d'.site.sub = 0 := by
    simp only [d', afterIssue]
    split
    · rfl
    split <;> rfl
  have hacc' : accAt d' = [] := by
    simp only [d', afterIssue]
    split
    · rfl
    split <;> rfl
  have hinv' : Inv P L g d' := inv_setSite hinv (by simp [hd]) (by simp [hd]) d'.site
    (by simp only [d', afterIssue]; split
        · exact True.intro
        split <;> exact True.intro)
  refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr,
    good_of_at (d := d') ht hsub' hacc' hinv'⟩)
  simp [next, hd, he, hm', d']

private theorem gather4Bytes (base numBlocks blockStride : Nat)
    (cls : TensorDescriptor.AllocationClass) :
    TensorTransfer.bytes (encodeKv base numBlocks blockStride cls).fourRows = 2304 := by
  simp [TensorTransfer.bytes, TensorDescriptor.Descriptor.fourRows, encodeKv, TensorTile.rows,
    TensorTile.rowsOf, TensorTile.count, TensorTile.step, TensorDescriptor.Format.bytes]

/-- A block past the main cache's blocks exists only when the extra cache is enabled. -/
theorem extra_active {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} (hinv : Inv P L g d)
    (hb : d.site ≠ .barrier) (he : d.site ≠ .exit) (hextra : ¬ d.block < numOrigBlocks d.len0) :
    P.extra_topk ≠ 0 := by
  intro hzero
  have hlen := extraLen_le hpre hinv.batch
  have hlen0 : d.len1 = 0 := by rw [hinv.len1]; omega
  rcases hinv.block_le with hb' | he' | hblock
  · exact hb hb'
  · exact he he'
  · have htotal : totalBlocks d.len0 d.len1 = numOrigBlocks d.len0 := by rw [hlen0]; rfl
    exact hextra (htotal ▸ hblock)

private theorem gatherMapBytes {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hinv : Inv P L g d)
    (hb : d.site ≠ .barrier) (he : d.site ≠ .exit) :
    (L.tensorMaps (P.param1Base + kvOff d)).map
      (fun m => TensorTransfer.bytes m.2.fourRows) = some 2304 := by
  unfold kvOff
  split
  · simp [hpre.mapKVBind, mapKv, gather4Bytes]
  · rename_i hmain
    simp [hpre.mapExtraKvBind.resolve_left (extra_active hpre hinv hb he hmain), mapExtraKv,
      gather4Bytes]

private theorem issueDst_value {d : D} (k : Fin 16) :
    valueOf P L g d (issueRegs.getD k.val 0) = sb L (issueDst d.buf k.val) := by
  fin_cases k <;> rfl

/-- A gather4 issue sends 2304 bytes to its four-row range in the raw ring and completes on that
raw slot's barrier. Its address is the selected main or extra KV descriptor. -/
theorem gather_issue_fields {mem0 : Mem0} {d : D} {t : TState} {e : Event} {o : Option TState}
    {a : Nat} {s : TensorCopy.Spec} {k : Fin 16} (hpre : Pre P L mem0) (hd : d.site = .issue k)
    (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hf : Fires d.site.pc (eventTmpl asms L g t (issueInstr k).op) e o)
    (he : e.kind = .tensorIssue a s) :
    a = P.param1Base + kvOff d ∧
    s.sharedBase = ⟨.shared, ctaOf L g, L.sharedBase + issueDst d.buf k.val⟩ ∧
    s.mbar = ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ ∧
    TensorTransfer.bytes s.descriptor = 2304 := by
  let dst := issueRegs.getD k.val 0
  let cs : List Opnd := .reg 691 :: ((coordRegs.drop (4 * k.val)).take 4).map Opnd.reg
  have hpol : 3050 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    exact issueLive_mem k 3050 (by simp)
  have hpolReg : t.regs 3050 = some (b64 1364590687093260288) := atD_reg hat hpol
  have hpolBits := readBits_b64 (L := L) (g := g) hpolReg (by decide)
  have ht : tensorTmpl L g t (issueInstr k).op =
      tensorTmpl L g t (.cpTensor false false dst 0 (.reg 3049) cs 696 0 none .fourRows) := by
    simp [issueInstr, dst, cs, tensorTmpl, cachePolicyRead, hpolBits, bind, Except.bind,
      pure, Except.pure]
  change Fires d.site.pc (tensorTmpl L g t (issueInstr k).op) e o at hf
  rw [ht] at hf
  have hcopy : tensorLoadCopy L g t false false dst 0 (.reg 3049) cs 696 0 .fourRows =
      .ok (a, s) := by
    rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t)
      (ca := false) (grp := false) (dst := dst) (off := 0) (map := .reg 3049)
      (cs := cs) (mb := 696) (moff := 0) (lm := .fourRows) with
      ⟨f, hub⟩ | ⟨a', s', hs⟩
    · rw [hub] at hf
      simp only [Fires] at hf
      rw [hf.1] at he
      cases he
    · rw [hs] at hf
      simp only [Fires] at hf
      have he' := congrArg Event.kind hf.1
      rw [he] at he'
      cases he'
      exact (tensorTmpl_unicast_issue hs).1
  obtain ⟨hmap, hm, m, hmapping, _, hdesc, _⟩ := tensorLoadCopy_ok hcopy
  obtain ⟨hdst, _, _⟩ := tensorLoadCopy_box hcopy
  have hmapLive : 3049 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    exact issueLive_mem k 3049 (by simp)
  have hmapRange : P.param1Base + kvOff d < 2 ^ 64 := by
    have hkv : kvOff d < 1024 := by unfold kvOff; split <;> decide
    have := hpre.param1Range
    omega
  have hmapReg : t.regs 3049 = some (b64 (P.param1Base + kvOff d)) := by
    have h := atD_reg hat hmapLive
    simpa only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, Nat.mod_eq_of_lt hmapRange]
      using h
  have hmapEval : tensorMapAddress L g t (.reg 3049) = .ok (P.param1Base + kvOff d) := by
    simp [tensorMapAddress, readValue, readReg, hmapReg, readBits_b64 hmapReg hmapRange,
      b64, toNat_ofNat_lt hmapRange, bind, Except.bind, pure, Except.pure]
  have ha : a = P.param1Base + kvOff d := Except.ok.inj (hmap.symm.trans hmapEval)
  have hbound := sharedBase_lt hpre
  have hbuf := hinv.buf_lt
  have hdstLive : dst ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    exact issueLive_mem k dst (by simp [dst])
  have hdstReg : t.regs dst = some (sb L (issueDst d.buf k.val)) := by
    exact (atD_reg hat hdstLive).trans (congrArg some (issueDst_value (d := d) k))
  have hdstRange : L.sharedBase + issueDst d.buf k.val < 2 ^ 32 := by
    have hk := k.isLt
    unfold issueDst rawBase
    omega
  have hdstEval : sharedEffAddr L g t false dst 0 =
      .ok ⟨.shared, ctaOf L g, L.sharedBase + issueDst d.buf k.val⟩ :=
    effAddr_b32 hdstReg hdstRange
  have hmLive : 696 ∈ (Flow.live d.site.pc).filter tracked.contains := by
    rw [hd]
    exact issueLive_mem k 696 (by simp)
  have hmReg : t.regs 696 = some (sb L (rawReadyOff d.buf)) := atD_reg hat hmLive
  have hmRange : L.sharedBase + rawReadyOff d.buf < 2 ^ 32 := by unfold rawReadyOff; omega
  have hmEval : mbarLoc L g t 696 0 =
      .ok ⟨.shared, ctaOf L g, L.sharedBase + rawReadyOff d.buf⟩ :=
    mbarLoc_b32 hmReg hmRange (sharedAddr_align hpre (by unfold rawReadyOff; omega))
  have hbytes := gatherMapBytes hpre hinv (by simp [hd]) (by simp [hd])
  rw [← ha, hmapping] at hbytes
  exact ⟨ha, Except.ok.inj (hdst.symm.trans hdstEval), Except.ok.inj (hm.symm.trans hmEval),
    by rw [hdesc]; exact Option.some.inj hbytes⟩

private def atFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) :
    List (Nat × Value) :=
  factsFrom ((Flow.live pc).filter tracked.contains) (valueOf P L g d)

private def advanceRaw (d : D) : D :=
  { d with buf := 1 - d.buf, rpar := if d.rpar = d.buf then 0 else 1 }

private def advanceRings (d : D) : D :=
  { advance d with block := d.block }

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem advanceRawPrefix_run {d : D} (hbuf : d.buf < 2) (hpar : d.rpar < 2) :
    Seg kernel asms L g 3 2309 (atFacts P L g d 2309) 2312
      ((53, .pred (decide (d.rpar ≠ d.buf))) :: atFacts P L g d 2312) := by
  rcases d with ⟨site, block, phase, par, buf, rpar, len0, len1, cw⟩
  change buf < 2 at hbuf
  change rpar < 2 at hpar
  interval_cases buf <;> interval_cases rpar <;> intro u hu <;>
    dsimp only [atFacts] at hu ⊢ <;> seg_fp hu using rfl

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem advanceRaw_run {d : D} (hbuf : d.buf < 2) (hpar : d.rpar < 2) :
    Seg kernel asms L g 5 2309 (atFacts P L g d 2309) 2314
      (atFacts P L g (advanceRaw d) 2314) := by
  intro u hu
  obtain ⟨t, r, h⟩ := advanceRawPrefix_run (d := d) hbuf hpar u hu
  obtain ⟨t', r', h'⟩ : ∃ t', run kernel asms L g 2 t = some t' ∧
      At t' 2314 (atFacts P L g (advanceRaw d) 2314) := by
    dsimp only [atFacts] at h ⊢
    simp only [ne_eq] at h
    by_cases hp : d.rpar = d.buf <;> simp [hp] at h <;> seg_fp h using
        tma_values
        all_goals
          try simp only [advanceRaw, hp, ↓reduceIte]
          all_goals first | rfl | (interval_cases d.buf <;> rfl)
  exact ⟨t', run_comp r r', h'⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem advanceIndexParity_run {d : D} (hphase : d.phase < 4) (hpar : d.par < 2) :
    Seg kernel asms L g 4 2314 (atFacts P L g (advanceRaw d) 2314) 2318
      (atFacts P L g { advanceRaw d with par := (advance d).par } 2318) := by
  rcases d with ⟨site, block, phase, par, buf, rpar, len0, len1, cw⟩
  change phase < 4 at hphase
  change par < 2 at hpar
  interval_cases phase <;> interval_cases par <;> intro u hu <;>
    dsimp only [atFacts] at hu ⊢ <;> seg_fp hu using
      try tma_values
      try simp only [advance]
      all_goals decide +kernel

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem advanceIndexPhase_run {d : D} (hphase : d.phase < 4) :
    Seg kernel asms L g 6 2318 (atFacts P L g { advanceRaw d with par := (advance d).par } 2318)
      2324 (atFacts P L g (advanceRings d) 2324) := by
  rcases d with ⟨site, block, phase, par, buf, rpar, len0, len1, cw⟩
  change phase < 4 at hphase
  interval_cases phase <;> intro u hu <;>
    dsimp only [atFacts] at hu ⊢ <;> seg_fp hu using
      try tma_values
      try simp only [advanceRaw, advanceRings, advance]
      all_goals decide +kernel

private theorem advanceCount_run {d : D} (hb : d.block < totalBlocks d.len0 d.len1)
    (ht : totalBlocks d.len0 d.len1 < 2 ^ 25) :
    Seg kernel asms L g 3 2324 (atFacts P L g (advanceRings d) 2324) 2327
      ((56, .pred (decide (d.block + 1 < totalBlocks d.len0 d.len1))) ::
        atFacts P L g (advance d) 2327) := by
  intro u hu
  let n := totalBlocks d.len0 d.len1
  let c := d.block + (2 ^ 32 - n)
  let c' := (d.block + 1 + (2 ^ 32 - n)) % 2 ^ 32
  have hc : c < 2 ^ 32 := by dsimp only [c, n]; omega
  have hc1 : c + 1 ≤ 2 ^ 32 := by omega
  have hc32 : c % 4294967296 = c := Nat.mod_eq_of_lt hc
  have hjoin : c + 1 = d.block + 1 + (2 ^ 32 - n) := by dsimp only [c]; omega
  have hc' : c' = (c + 1) % 2 ^ 32 := congrArg (· % (2 ^ 32)) hjoin.symm
  dsimp only [c, n] at hc32 hjoin
  have hc'32 : c' < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hb32 : d.block % 4294967296 = d.block := Nat.mod_eq_of_lt (by omega)
  have hb1_64 : (d.block + 1) % 18446744073709551616 = d.block + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hb1_32 : (d.block + 1) % 4294967296 = d.block + 1 := Nat.mod_eq_of_lt (by omega)
  have hcon : c' ≠ 0 ↔ d.block + 1 < n := by
    by_cases hlt : d.block + 1 < n
    · have hsmall : c + 1 < 2 ^ 32 := by dsimp only [c]; omega
      rw [hc', Nat.mod_eq_of_lt hsmall]
      simp [hlt]
    · have hfull : c + 1 = 2 ^ 32 := by dsimp only [c, n] at *; omega
      simp [hc', hfull, hlt]
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 2 u = some t1 ∧
      At t1 2326 (atFacts P L g (advance d) 2326) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using
      try tma_values
      all_goals norm_bits [advance, advanceRings, hc32, hjoin, hb32, hb1_32, hb1_64]
  have hcmp : PTX.compare .ne .b 32 (truncBits 32 (BitVec.ofNat 64 c'))
      (truncBits 32 (BitVec.ofInt 64 0)) =
      decide (d.block + 1 < n) := by
    rw [truncBits_ofNat hc'32 (by decide)]
    have hz : (truncBits 32 (BitVec.ofInt 64 0)).toNat = 0 := by decide
    have hn := toNat_ofNat_lt (show c' < 2 ^ 64 by omega)
    change (decide (((BitVec.ofNat 64 c').toNat : Int) ≠
      ((truncBits 32 (BitVec.ofInt 64 0)).toNat : Int)) = decide (d.block + 1 < n))
    rw [hn, hz, decide_eq_decide]
    exact (show (c' : Int) ≠ 0 ↔ c' ≠ 0 by omega).trans hcon
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2327 ((56, .pred (decide (d.block + 1 < n))) :: atFacts P L g (advance d) 2327) := by
    dsimp only [atFacts] at h1 ⊢
    seg_fp h1 using
      change (Value.pred (PTX.compare .ne .b 32 (truncBits 32 (BitVec.ofNat 64 c'))
        (truncBits 32 (BitVec.ofInt 64 0))) = .pred (decide (d.block + 1 < n)))
      rw [hcmp]
  exact ⟨t2, run_comp r1 r2, h2⟩

private theorem loopHead_run {d : D} (hwin : L.sharedBase + 222952 < 2 ^ 32)
    (hblk : d.block < 2 ^ 32) (hmain : numOrigBlocks d.len0 < 2 ^ 32) (hphase : d.phase < 4)
    (hpar : d.par < 2) :
    Seg kernel asms L g 9 2225 (atFacts P L g d 2225) 2234 (atFacts P L g d 2234) := by
  intro u hu
  have hcmp : PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 d.block))
      (truncBits 32 (BitVec.ofNat 64 (numOrigBlocks d.len0))) =
      decide (d.block < numOrigBlocks d.len0) := by
    rw [truncBits_ofNat hblk (by decide), truncBits_ofNat hmain (by decide)]
    simp [PTX.compare, toNat_ofNat_lt (show d.block < 2 ^ 64 by omega),
      toNat_ofNat_lt (show numOrigBlocks d.len0 < 2 ^ 64 by omega)]
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2226 (atFacts P L g d 2226) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using
      change (Value.pred (PTX.compare .lt .u 32 (truncBits 32 (BitVec.ofNat 64 d.block))
        (truncBits 32 (BitVec.ofNat 64 (numOrigBlocks d.len0)))) =
        .pred (decide (d.block < numOrigBlocks d.len0)))
      rw [hcmp]
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 3 t1 = some t2 ∧
      At t2 2229 (atFacts P L g d 2229) := by
    dsimp only [atFacts] at h1 ⊢
    seg_fp h1 using
      tma_values
      interval_cases d.par <;> decide +kernel
  have hmod32 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 4294967296 = L.sharedBase + off := Nat.mod_eq_of_lt (by omega)
  have hmod64 (off : Nat) (hoff : off ≤ 222952) :
      (L.sharedBase + off) % 18446744073709551616 = L.sharedBase + off :=
    Nat.mod_eq_of_lt (by omega)
  have hbase32 : L.sharedBase % 4294967296 = L.sharedBase := Nat.mod_eq_of_lt (by omega)
  have hbase64 : L.sharedBase % 18446744073709551616 = L.sharedBase := Nat.mod_eq_of_lt (by omega)
  have hslot32 : d.phase % 4294967296 = d.phase := Nat.mod_eq_of_lt (by omega)
  have hshift32 : (d.phase * 8) % 4294967296 = d.phase * 8 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 5 t2 = some t3 ∧
      At t3 2234 (atFacts P L g d 2234) := by
    dsimp only [atFacts] at h2 ⊢
    seg_fp h2 using
      tma_values
      all_goals
        nf_simp [hslot32, hshift32]
        all_goals
          simp (discharger := omega) only [hmod32, hmod64, hbase32, hbase64,
            Nat.add_zero, Nat.add_assoc]
          all_goals omega
  exact ⟨t3, run_comp (run_comp r1 r2) r3, h3⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- Releasing the index slot advances both rings or, on the last block, reaches the barrier. -/
theorem stepAt_coordFree {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .coordFree)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2308 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_5)
  have h773 : t.regs 773 = some (sb L (coordFreeOff d.phase)) :=
    atD_regAt hat hpc (by decide +kernel)
  have hwin := sharedBase_lt hpre
  have hphase := hinv.phase_lt
  have hbase : L.sharedBase + coordFreeOff d.phase < 2 ^ 32 := by
    unfold coordFreeOff
    omega
  have hm := mbarLoc_b32 (L := L) (g := g) h773 hbase
    (sharedAddr_align hpre (by unfold coordFreeOff; omega))
  have hzero : readBits L g t 32 (.imm 0) = .ok (truncBits 32 (BitVec.ofInt 64 0)) :=
    by simp [readBits, pure, Except.pure]
  have hone : readBits L g t 32 (.imm 1) = .ok (truncBits 32 (BitVec.ofInt 64 1)) :=
    by simp [readBits, pure, Except.pure]
  obtain ⟨rel, scope, he, hu⟩ := fires_arrive_next (cluster := false) hm hzero hone hf
  have hn : next P L g d e = some (some (afterFree d)) := by
    simp [next, hd, he, ctaOf]
  have hsub : d.site.sub = 0 := by rw [hd]; rfl
  have hnot : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hbar : d.site ≠ .barrier := by simp [hd]
  have hex : d.site ≠ .exit := by simp [hd]
  have hblock : d.block < totalBlocks d.len0 d.len1 := by
    rcases hinv.block_le with h | h | h
    · exact absurd h hbar
    · exact absurd h hex
    · exact h
  have htotal : totalBlocks d.len0 d.len1 < 2 ^ 25 := by
    rw [hinv.len0, hinv.len1]
    exact totalBlocks_lt hpre hinv.batch
  have hmain : numOrigBlocks d.len0 < 2 ^ 32 := by
    have hle : numOrigBlocks d.len0 ≤ totalBlocks d.len0 d.len1 := by
      unfold numOrigBlocks totalBlocks
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    omega
  have ht : At t 2308 (atFacts P L g d 2308) := by
    simpa only [atFacts, facts, hpc] using atD_at hat hsub hnot
  have huAt : At u 2309 (atFacts P L g d 2309) := by
    rw [Option.some.inj hu]
    have hlive : ((Flow.live 2309).filter tracked.contains).all
        ((Flow.live 2308).filter tracked.contains).contains = true := by decide +kernel
    have ht' := At.next ht
    refine ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ?_⟩
    exact holds_factsFrom_mono ht'.2.2.2.2 fun r hr =>
      List.contains_iff_mem.mp (List.all_eq_true.mp hlive r hr)
  obtain ⟨t1, r1, h1⟩ := advanceRaw_run hinv.buf_lt hinv.rpar_lt u huAt
  obtain ⟨t2, r2, h2⟩ := advanceIndexParity_run hphase hinv.par_lt t1 h1
  obtain ⟨t3, r3, h3⟩ := advanceIndexPhase_run hphase t2 h2
  obtain ⟨t4, r4, h4⟩ := advanceCount_run hblock htotal t3 h3
  have hr := run_comp (run_comp (run_comp r1 r2) r3) r4
  have hinv' := afterFree_inv hinv hbar hex
  by_cases hcont : d.block + 1 < totalBlocks d.len0 d.len1
  · rw [afterFree_eq_advance hcont] at hn hinv'
    have h4' : At t4 2327 ((56, .pred true) :: atFacts P L g (advance d) 2327) := by
      simpa [hcont] using h4
    obtain ⟨t5, r5, h5⟩ : ∃ t5, run kernel asms L g 1 t4 = some t5 ∧
        At t5 2225 (atFacts P L g (advance d) 2225) := by
      dsimp only [atFacts] at h4' ⊢
      seg_fp h4' using skip
    have hb' : (advance d).block < 2 ^ 32 := by simp only [advance]; omega
    obtain ⟨t6, r6, h6⟩ := loopHead_run hwin hb' hmain hinv'.phase_lt hinv'.par_lt t5 h5
    exact Or.inl (Or.inr ⟨advance d, t6, hn, run_rtg (run_comp (run_comp hr r5) r6),
      good_of_at (d := advance d) h6 rfl rfl hinv'⟩)
  · rw [afterFree_eq_barrier hcont] at hn hinv'
    have h4' : At t4 2327 ((56, .pred false) :: atFacts P L g (advance d) 2327) := by
      simpa [hcont] using h4
    obtain ⟨t5, r5, h5⟩ : ∃ t5, run kernel asms L g 3 t4 = some t5 ∧
        At t5 2330 (facts P L g (toBarrier d)) := by
      dsimp only [atFacts] at h4'
      seg_fp h4' using
        try tma_values
        all_goals rfl
    exact Or.inl (Or.inr ⟨toBarrier d, t5, hn, run_rtg (run_comp hr r5),
      good_of_at (d := toBarrier d) h5 rfl rfl hinv'⟩)

private def ncLength (base dst : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
    addr := ⟨.reg base 64, 0⟩, dsts := [some dst] }

private theorem fires_length {L : Launch} {g : Nat} {t u : TState} {e : Event}
    {base dst off : Nat} (hsub : t.sub = 0) (hreg : t.regs base = some (b64 off))
    (hword : off < 2 ^ 64) (halign : off % 4 = 0) (hnc : asms.any (·.ncLoads t.pc) = true)
    (hf : Fires t.pc (eventTmpl asms L g t (.mem (ncLength base dst))) e (some u)) :
    ∃ a bs, e = ⟨t.pc, .nc a bs⟩ ∧ u = afterLoad t [dst] bs := by
  have ht := loadTmpl_global_nc (A := asms) (L := L) (g := g) (t := t)
    (d := dst) (base := base) (w := 32) hsub hreg hword (by decide) halign hnc
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires t.pc (loadTmpl asms L g t .global true 32 [dst] base 0) e (some u) at hf
  rw [ht] at hf
  obtain ⟨bs, -, he, hu⟩ := hf
  exact ⟨_, bs, he, Option.some.inj hu⟩

private theorem toSigned32_small {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  have h32 : n < 2 ^ 32 := by omega
  have h64 : n < 2 ^ 64 := by omega
  unfold toSigned
  rw [toNat_ofNat_lt h64, Nat.mod_eq_of_lt h32]
  exact ite_eq_left hn

private theorem maxWord64 {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32 (if PTX.compare .gt .s 32 (truncBits 32 (BitVec.ofNat 64 n))
        (truncBits 32 (BitVec.ofInt 64 64)) then truncBits 32 (BitVec.ofNat 64 n)
      else truncBits 32 (BitVec.ofInt 64 64)) = b32 (max n 64) := by
  have h32 : n < 2 ^ 32 := by omega
  have hw : truncBits 32 (BitVec.ofInt 64 64) = BitVec.ofNat 64 64 := by decide
  rw [truncBits_ofNat h32 (by decide), hw]
  have hc : PTX.compare .gt .s 32 (BitVec.ofNat 64 n) (BitVec.ofNat 64 64) =
      decide (64 < n) := by
    change (decide (toSigned 32 (BitVec.ofNat 64 64) < toSigned 32 (BitVec.ofNat 64 n)) =
      decide (64 < n))
    rw [toSigned32_small (by decide), toSigned32_small hn, decide_eq_decide]
    exact Int.ofNat_lt
  rw [hc]
  by_cases h : 64 < n
  · simp [h, b32, max_eq_left (by omega : 64 ≤ n)]
  · simp [h, b32, max_eq_right (by omega : n ≤ 64)]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem tmaPadded_run {d : D} (hwin : L.sharedBase + 222952 < 2 ^ 32)
    (hlen : d.len1 + 63 < 2 ^ 31)
    (hpad : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31) (hd : d.site = .waitQ) :
    Seg kernel asms L g 13 2192 (atFacts P L g d 2192) 2205 (facts P L g d) := by
  intro u hu
  have hc0 : ceilToMultiple d.len0 topkBlock < 2 ^ 31 := by unfold origPadded at hpad; omega
  have hc1 : ceilToMultiple d.len1 topkBlock < 2 ^ 31 := by omega
  have heq : ceilToMultiple d.len1 topkBlock = (d.len1 + 63) / 64 * 64 := by
    unfold ceilToMultiple topkBlock
    omega
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2193 (atFacts P L g d 2193) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using
      exact maxWord64 hc0
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 5 t1 = some t2 ∧
      At t2 2198 ((673, b32 (d.len1 + 63)) :: (677, b32 (ceilToMultiple d.len1 topkBlock)) ::
        atFacts P L g d 2198) := by
    dsimp only [atFacts] at h1 ⊢
    seg_fp h1 using
      try simp only [hd]
      all_goals norm_signed [heq, hlen]
  obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧
      At t3 2201 (atFacts P L g d 2201) := by
    dsimp only [atFacts] at h2 ⊢
    seg_fp h2 using
      tma_values
      norm_bits []
  obtain ⟨t4, r4, h4⟩ : ∃ t4, run kernel asms L g 4 t3 = some t4 ∧
      At t4 2205 (facts P L g d) := by
    dsimp only [atFacts] at h3
    rw [facts, hd]
    seg_fp h3 using
      try tma_values
      all_goals norm_bits [Nat.add_zero, Nat.zero_add]
  exact ⟨t4, run_comp (run_comp (run_comp r1 r2) r3) r4, h4⟩

/-- With the extra-cache length read, the thread computes the padded counts and reaches the
Q-copy poll with the corresponding launch facts. -/
theorem stepAt_lenExtra {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .lenExtra)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2191 := by rw [hd]; rfl
  have htp : t.pc = 2191 := hat.1.trans hpc
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_18)
  rw [← htp] at hf
  have h3047 : t.regs 3047 = some (b64 ((paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)) :=
    atD_regAt hat hpc (by decide +kernel)
  have hs : t.sub = 0 := by rw [hat.2.1, code_sub, hd]; rfl
  obtain ⟨a, bs, he, hu⟩ := fires_length (dst := 2963) hs h3047 (Nat.mod_lt _ (by decide))
    (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g)
    (by rw [htp]; decide +kernel) hf
  rw [htp] at he
  rcases hrb : rebuild 3 bs with f | v
  · exact Or.inl (Or.inl (by simp [next, hd, he, hrb]))
  by_cases hv : v = b32 (P.extraTopkLen (eOf L g))
  · subst v
    let d' := { d with site := .waitQ }
    have hsub : d.site.sub = 0 := by rw [hd]; rfl
    have hnot : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
    have h486 : t.regs 486 = some (b32 (ceilToMultiple d.len0 topkBlock)) :=
      atD_regAt hat hpc (by decide +kernel)
    have h2990 : t.regs 2990 = some (.ptr 64 false (.param (param "1")) 0) :=
      atD_regAt hat hpc (by decide +kernel)
    have ht : At t 2191 (atFacts P L g d 2191) := by
      simpa only [atFacts, facts, hpc] using atD_at hat hsub hnot
    have hu' := hu.trans (afterLoad_ok (d := 2963) ht.2.1 ht.2.2.1 hrb)
    have h1 : At u 2192 (atFacts P L g d' 2192) := by
      rw [hu']
      change At _ 2192 [(486, b32 (ceilToMultiple d.len0 topkBlock)),
        (2963, b32 d.len1), (2990, .ptr 64 false (.param (param "1")) 0)]
      refine ⟨by simp [htp], rfl, rfl, ht.2.2.2.1, ?_⟩
      simp [setReg, h486, h2990, hinv.len1]
    have hpad : origPadded d'.len0 + ceilToMultiple d'.len1 topkBlock < 2 ^ 31 := by
      change origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31
      rw [hinv.len0, hinv.len1]
      exact hpre.paddedRange _ hinv.batch
    have hlen : d'.len1 + 63 < 2 ^ 31 := by
      have hb := extraLen_le hpre hinv.batch
      have hbound := hpre.extraTopkAdd63Lt
      change d.len1 + 63 < 2 ^ 31
      rw [hinv.len1]
      omega
    obtain ⟨t', hr, ht'⟩ := tmaPadded_run (sharedBase_lt hpre) hlen hpad rfl u h1
    have hi : Inv P L g d' := inv_setSite hinv (by simp [hd]) (by simp [hd]) .waitQ
    refine Or.inl (Or.inr ⟨d', t', ?_, run_rtg hr, good_of_at (d := d') ht' rfl rfl hi⟩)
    simp [next, hd, he, hrb, d', hinv.len1]
  · exact Or.inl (Or.inl (by simp [next, hd, he, hrb, hv]))

private theorem extraLen_of_null {mem0 : Mem0} (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hnull : paramWord L 144 8 = 0) :
    P.extraTopkLen (eOf L g) = P.extra_topk := by
  have hnone : P.extraTopkLenBase = none := by
    cases hp : P.extraTopkLenBase with
    | none => rfl
    | some x =>
      have hword := Thread.paramWord_144_some hpre hp
      rw [Nat.mod_eq_of_lt (hpre.extraTopkLenBaseLt x hp)] at hword
      have hpos := hpre.extraTopkLenNonNull x hp
      exact False.elim (Nat.ne_of_gt hpos (hword.symm.trans hnull))
  have hlen := hpre.paramExtraTopkLen
  rw [hnone] at hlen
  exact hlen.2 _ hb

private theorem mainLen_of_null {mem0 : Mem0} (hpre : Pre P L mem0) (hb : eOf L g < P.b)
    (hnull : paramWord L 80 8 = 0) :
    P.topkLen (eOf L g) = P.topk := by
  have hnone : P.topkLenBase = none := by
    cases hp : P.topkLenBase with
    | none => rfl
    | some x =>
      have hword := Thread.paramWord_80_some hpre hp
      rw [Nat.mod_eq_of_lt (hpre.topkLenBaseLt x hp)] at hword
      have hpos := hpre.topkLenNonNull x hp
      exact False.elim (Nat.ne_of_gt hpos (hword.symm.trans hnull))
  have hlen := hpre.paramTopkLen
  rw [hnone] at hlen
  exact hlen.2 _ hb

private def afterOrig (L : Launch) (d : D) : D :=
  { d with site := if paramWord L 144 8 = 0 then .waitQ else .lenExtra }

private theorem compare_pointer_zero {x : Nat} (hx : x < 2 ^ 64) :
    PTX.compare .eq .b 64 (truncBits 64 (BitVec.ofNat 64 x))
      (truncBits 64 (BitVec.ofInt 64 0)) = decide (x = 0) := by
  rw [truncBits_ofNat hx (by decide)]
  have hz : (truncBits 64 (BitVec.ofInt 64 0)).toNat = 0 := by decide
  change (decide (((BitVec.ofNat 64 x).toNat : Int) =
    ((truncBits 64 (BitVec.ofInt 64 0)).toNat : Int)) = decide (x = 0))
  rw [toNat_ofNat_lt hx, hz, decide_eq_decide]
  exact ⟨Int.ofNat.inj, congrArg Int.ofNat⟩

private theorem lenOrigRounded_run {d : D} (hlen : d.len0 + 63 < 2 ^ 31) :
    Seg kernel asms L g 6 2182 (atFacts P L g d 2182) 2188
      ((50, .pred (decide (paramWord L 144 8 = 0))) :: atFacts P L g d 2188) := by
  intro u hu
  let p := Value.pred (decide (paramWord L 144 8 = 0))
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2183 ((50, p) :: atFacts P L g d 2183) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using
      change (Value.pred (PTX.compare .eq .b 64
        (truncBits 64 (BitVec.ofNat 64 (paramWord L 144 8)))
        (truncBits 64 (BitVec.ofInt 64 0))) = p)
      rw [compare_pointer_zero (Thread.paramWord_lt L 144)]
  have hceil : ceilToMultiple d.len0 topkBlock = (d.len0 + 63) / 64 * 64 := by
    unfold ceilToMultiple topkBlock
    omega
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 5 t1 = some t2 ∧
      At t2 2188 ((50, p) :: atFacts P L g d 2188) := by
    dsimp only [atFacts] at h1 ⊢
    seg_fp h1 using
      tma_values
      norm_signed [hceil, hlen]
  exact ⟨t2, run_comp r1 r2, h2⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem lenOrigTail_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0)
    (hinv : d.len0 = P.topkLen (eOf L g) ∧ d.len1 = P.extraTopkLen (eOf L g) ∧ eOf L g < P.b)
    (hd : d.site = .lenOrig) {u : TState} (hu : At u 2182 (atFacts P L g d 2182)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' (afterOrig L d).site.pc (facts P L g (afterOrig L d)) := by
  have hlen0 : d.len0 + 63 < 2 ^ 31 := by
    have hmax := topkLen_le hpre hinv.2.2
    have hbound := hpre.topkAdd63Lt
    rw [hinv.1]
    omega
  have hlen1 : d.len1 + 63 < 2 ^ 31 := by
    have hmax := extraLen_le hpre hinv.2.2
    have hbound := hpre.extraTopkAdd63Lt
    rw [hinv.2.1]
    omega
  have hpad : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31 := by
    rw [hinv.1, hinv.2.1]
    exact hpre.paddedRange _ hinv.2.2
  have hword := Thread.paramWord_lt L 144
  obtain ⟨t2, r2, h2⟩ := lenOrigRounded_run hlen0 u hu
  by_cases hnull : paramWord L 144 8 = 0
  · have h2' : At t2 2188 ((50, .pred true) :: atFacts P L g d 2188) := by
      simpa [hnull] using h2
    obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 2192 (atFacts P L g d 2192) := by
      dsimp only [atFacts] at h2' ⊢
      seg_fp h2' using skip
    let d' := { d with site := Site.waitQ }
    have hlen : d.len1 = P.extra_topk := hinv.2.1.trans (extraLen_of_null hpre hinv.2.2 hnull)
    have hf : atFacts P L g d 2192 = atFacts P L g d' 2192 := by
      change [(486, b32 (ceilToMultiple d.len0 topkBlock)),
        (2963, b32 (match d.site with | .lenOrig => P.extra_topk | _ => d.len1)),
        (2990, .ptr 64 false (.param (param "1")) 0)] =
        [(486, b32 (ceilToMultiple d.len0 topkBlock)), (2963, b32 d.len1),
          (2990, .ptr 64 false (.param (param "1")) 0)]
      simp [hd, hlen]
    rw [hf] at h3
    obtain ⟨t4, r4, h4⟩ := tmaPadded_run (sharedBase_lt hpre) (d := d') hlen1 hpad rfl t3 h3
    have hafter : afterOrig L d = d' := by simp [afterOrig, hnull, d']
    rw [hafter]
    exact ⟨t4, run_rtg (run_comp (run_comp r2 r3) r4), h4⟩
  · have h2' : At t2 2188 ((50, .pred false) :: atFacts P L g d 2188) := by
      simpa [hnull] using h2
    let d' := { d with site := Site.lenExtra }
    have hbatch := hinv.2.2
    have hb := hpre.bLt
    have hcta32 : ctaidY L g < 2 ^ 32 := by change ctaidY L g < P.b at hbatch; omega
    obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 3 t2 = some t3 ∧
        At t3 2191 (facts P L g d') := by
      dsimp only [atFacts] at h2'
      seg_fp h2' using
        tma_values
        norm_bits [Nat.mod_eq_of_lt hcta32, Nat.mod_eq_of_lt hword, Nat.mul_comm]
    have hafter : afterOrig L d = d' := by simp [afterOrig, hnull, d']
    rw [hafter]
    exact ⟨t3, run_rtg (run_comp r2 r3), h3⟩

/-- The main-cache length read computes its padded count and tests the optional extra length. -/
theorem stepAt_lenOrig {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .lenOrig)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2181 := by rw [hd]; rfl
  have htp : t.pc = 2181 := hat.1.trans hpc
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_17)
  rw [← htp] at hf
  have h3045 : t.regs 3045 = some (b64 ((paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)) :=
    atD_regAt hat hpc (by decide +kernel)
  have hs : t.sub = 0 := by rw [hat.2.1, code_sub, hd]; rfl
  obtain ⟨a, bs, he, hu⟩ := fires_length (dst := 2962) hs h3045 (Nat.mod_lt _ (by decide))
    (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g)
    (by rw [htp]; decide +kernel) hf
  rw [htp] at he
  rcases hrb : rebuild 3 bs with f | v
  · exact Or.inl (Or.inl (by simp [next, hd, he, hrb]))
  by_cases hv : v = b32 (P.topkLen (eOf L g))
  · subst v
    have hsub : d.site.sub = 0 := by rw [hd]; rfl
    have hnot : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
    have ht : At t 2181 (atFacts P L g d 2181) := by
      simpa only [atFacts, facts, hpc] using atD_at hat hsub hnot
    have hu' := hu.trans (afterLoad_ok (d := 2962) ht.2.1 ht.2.2.1 hrb)
    have h1 : At u 2182 (atFacts P L g d 2182) := by
      refine ⟨by simp [hu', setReg, htp], by rw [hu'], by rw [hu'],
        by rw [hu']; exact ht.2.2.2.1, ?_⟩
      have hframe : ∀ r, r ∉ [2962] → u.regs r = t.regs r := by
        intro r hr
        simp only [List.mem_singleton] at hr
        simp [hu', setReg, Function.update_of_ne hr]
      have hregs := ht.2.2.2.2
      dsimp only [atFacts] at hregs ⊢
      frame_fp hregs, hframe
      change Holds u.regs [(2962, b32 d.len0)]
      rw [hu']
      simp [setReg, hinv.len0]
    obtain ⟨t', hr, ht'⟩ := lenOrigTail_run hpre ⟨hinv.len0, hinv.len1, hinv.batch⟩ hd h1
    have hhas := inv_setSite hinv (by simp [hd]) (by simp [hd]) (afterOrig L d).site
      (by unfold afterOrig; split <;> first | exact True.intro | assumption)
    have hi : Inv P L g (afterOrig L d) := by simpa only [afterOrig] using hhas
    have hzero : (afterOrig L d).site.sub = 0 := by unfold afterOrig; split <;> rfl
    have hacc : accAt (afterOrig L d) = [] := by unfold afterOrig; split <;> rfl
    refine Or.inl (Or.inr ⟨afterOrig L d, t', ?_, hr, good_of_at ht' hzero hacc hi⟩)
    simp [next, hd, he, hrb, afterOrig, hinv.len0]
  · exact Or.inl (Or.inl (by simp [next, hd, he, hrb, hv]))

private theorem intParam_supplied {L : Launch} {x off : Nat}
    (h : intBytes x off (param "0") L) : ParamSupplied L (param "0") off 4 :=
  fun k hk => ⟨_, h k hk⟩

private theorem tmaParam_run {mem0 : Mem0} {d : D} {pc w off dst : Nat} {ty : DType}
    (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off 2991 dst)⟩)
    (hPtr : 2991 ∈ (Flow.live pc).filter tracked.contains)
    (hsup : ParamSupplied L (param "0") off (w / 8)) (hsize : off + w / 8 ≤ 304)
    (halign : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (hVal : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g d dst)
    (hLive : ((Flow.live (pc + 1)).filter tracked.contains).all
      (fun r => r == dst || ((Flow.live pc).filter tracked.contains).contains r) = true)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hseg : Assumption.SegFreePc asms pc := by seg_free_pc) (hw : ty.width = w := by rfl)
    (hRule : (Thread.paramLoad ty off 2991 dst).rule = some .threadMove := by rfl) :
    Seg kernel asms L g 1 pc (atFacts P L g d pc) (pc + 1) (atFacts P L g d (pc + 1)) := by
  intro t h
  have hp : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) :=
    holds_mem h.2.2.2.2 (mem_factsFrom hPtr)
  have hLocal := Thread.asms_localRule_mem (L := L) (g := g) (t := t)
    (a := Thread.paramLoad ty off 2991 dst)
    (by rw [h.1]; exact h1) (by rw [h.1]; exact h2)
  have hexec := Thread.exec_ldParamReg (A := asms) hp hpre.param0Object ⟨by omega, hsize⟩
    halign hsup (Assumption.SegFreePc.of_eq h.1 hseg) hLocal hw hRule
  refine ⟨_, run_local hc rfl h hexec,
    ⟨by simp [PTX.next, setReg, h.1], h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩⟩
  refine holds_of_pointwise fun r hr => ?_
  have hcover := List.all_eq_true.mp hLive r hr
  simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hcover
  change Function.update t.regs dst
    (some (paramElem w w (paramNat L (param "0") off (w / 8)))) r = _
  by_cases hr' : r = dst
  · subst r
    rw [Function.update_self, hVal]
  · rw [Function.update_of_ne hr']
    exact holds_mem h.2.2.2.2 (mem_factsFrom (hcover.resolve_left hr'))

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem electBatch_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hb : ctaidY L g < P.b) :
    Seg kernel asms L g 3 2170 (atFacts P L g d 2170) 2173 (atFacts P L g d 2173) := by
  intro u hu
  have hB := hpre.bLt
  have hb32 : P.b < 2 ^ 32 := by omega
  have hV : paramElem 32 32 (paramNat L (param "0") 0 4) = valueOf P L g d 664 := by
    change b32 (Thread.paramWord L 0 4) = b32 P.b
    rw [Thread.paramWord_b hpre, Nat.mod_eq_of_lt hb32]
  obtain ⟨t1, r1, h1⟩ := tmaParam_run (d := d) (w := 32) hpre Flow.code_2170
    (by decide +kernel) (intParam_supplied hpre.paramB) (by decide) (by decide) hV
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by seg_free_pc) (by rfl)
    (by rfl) u hu
  have hca : ctaidY L g < 2 ^ 31 := lt_trans hb hB
  have hcmp : PTX.compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (ctaidY L g)))
      (truncBits 32 (BitVec.ofNat 64 P.b)) = false := by
    rw [truncBits_ofNat (by omega : ctaidY L g < 2 ^ 32) (by decide),
      truncBits_ofNat hb32 (by decide)]
    change (decide (toSigned 32 (BitVec.ofNat 64 P.b) ≤
      toSigned 32 (BitVec.ofNat 64 (ctaidY L g))) = false)
    rw [toSigned32_small hB, toSigned32_small hca, decide_eq_false_iff_not]
    omega
  obtain ⟨t2, r2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
      At t2 2172 ((48, .pred false) :: atFacts P L g d 2172) := by
    dsimp only [atFacts] at h1 ⊢
    seg_fp h1 using
      change (Value.pred (PTX.compare .ge .s 32
        (truncBits 32 (BitVec.ofNat 64 (ctaidY L g))) (truncBits 32 (BitVec.ofNat 64 P.b))) =
        .pred false)
      rw [hcmp]
  obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
      At t3 2173 (atFacts P L g d 2173) := by
    dsimp only [atFacts] at h2 ⊢
    seg_fp h2 using skip
  exact ⟨t3, run_comp (run_comp r1 r2) r3, h3⟩

private theorem electLengths_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0)
    (hd : d.site = .lenOrig) (hlen : d.len0 = P.topk) :
    Seg kernel asms L g 4 2173 (atFacts P L g d 2173) 2177 (atFacts P L g d 2177) := by
  intro u hu
  have hmain := hpre.topkAdd63Lt
  have hExtra := hpre.extraTopkAdd63Lt
  have hmain32 : P.topk < 2 ^ 32 := by omega
  have hextra32 : P.extra_topk < 2 ^ 32 := by omega
  obtain ⟨t1, r1, h1⟩ := tmaParam_run (d := d) (w := 64) hpre Flow.code_2173
    (by decide +kernel) (Thread.supplied_topk hpre) (by decide) (by decide) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by seg_free_pc) (by rfl)
    (by rfl) u hu
  have hv0 : paramElem 32 32 (paramNat L (param "0") 40 4) = valueOf P L g d 2962 := by
    change b32 (Thread.paramWord L 40 4) = b32 d.len0
    rw [Thread.paramWord_four hpre.paramTopk, Nat.mod_eq_of_lt hmain32, hlen]
  obtain ⟨t2, r2, h2⟩ := tmaParam_run (d := d) (w := 32) hpre Flow.code_2174
    (by decide +kernel) (intParam_supplied hpre.paramTopk) (by decide) (by decide) hv0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by seg_free_pc) (by rfl)
    (by rfl) t1 h1
  obtain ⟨t3, r3, h3⟩ := tmaParam_run (d := d) (w := 64) hpre Flow.code_2175
    (by decide +kernel) (Thread.supplied_extra hpre) (by decide) (by decide) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by seg_free_pc) (by rfl)
    (by rfl) t2 h2
  have hv1 : paramElem 32 32 (paramNat L (param "0") 120 4) = valueOf P L g d 2963 := by
    change b32 (Thread.paramWord L 120 4) =
      b32 (match d.site with | .lenOrig => P.extra_topk | _ => d.len1)
    rw [Thread.paramWord_four hpre.paramExtraTopk, Nat.mod_eq_of_lt hextra32, hd]
  obtain ⟨t4, r4, h4⟩ := tmaParam_run (d := d) (w := 32) hpre Flow.code_2176
    (by decide +kernel) (intParam_supplied hpre.paramExtraTopk) (by decide) (by decide) hv1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by seg_free_pc) (by rfl)
    (by rfl) t3 h3
  exact ⟨t4, run_comp (run_comp (run_comp r1 r2) r3) r4, h4⟩

private def electLengthData (P : Params) (d : D) : D :=
  { d with site := .lenOrig, len0 := P.topk }

private def afterElection (L : Launch) (d : D) : D :=
  { d with site := firstLenSite L }

private def electionFacts (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(460, b32 (ctaidY L g)), (662, b32 0), (663, b32 (2 ^ 32 - 1)),
    (2990, .ptr 64 false (.param (param "1")) 0),
    (2991, .ptr 64 false (.param (param "0")) 0)]

private theorem facts_2165 {d : D} :
    atFacts P L g d 2165 = electionFacts L g := by
  unfold atFacts
  rw [show (Flow.live 2165).filter tracked.contains =
    [460, 662, 663, 2990, 2991] from by decide +kernel]
  rfl

private theorem at_elected {d : D} {t u : TState} (hd : d.site = .elect)
    (hat : (code P L g).AtD d t)
    (hu : u = PTX.next (setReg (setReg t 4116 (b32 (PTX.laneOf L g))) 4117 (.pred true))) :
    At u 2166 ((4116, b32 (PTX.laneOf L g)) :: (4117, .pred true) ::
      atFacts P L g (electLengthData P d) 2165) := by
  have hnot : ∀ k j, d.site ≠ .coord k j := by intro k j; simp [hd]
  have hpc : d.site.pc = 2165 := by rw [hd]; rfl
  have ht0 : At t 2165 (atFacts P L g d 2165) := by
    simpa only [facts, atFacts, hpc] using atD_at hat (by rw [hd]; rfl) hnot
  rw [facts_2165] at ht0 ⊢
  rw [hu]
  refine ⟨by simp [PTX.next, setReg, ht0.1], ht0.2.1, ht0.2.2.1, ht0.2.2.2.1, ?_⟩
  simpa [PTX.next, setReg, holds_cons, b32, electionFacts] using ht0.2.2.2.2

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem electNull_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hinv : Inv P L g d)
    {u : TState} (hnull : paramWord L 80 8 = 0)
    (hu : At u 2178 ((49, .pred true) :: atFacts P L g (electLengthData P d) 2178)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' (afterElection L d).site.pc (facts P L g (afterElection L d)) := by
  let d0 := electLengthData P d
  let d' := { d with site := Site.lenOrig }
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2182 (atFacts P L g d0 2182) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using skip
  have hlen : P.topk = d.len0 := (hinv.len0.trans (mainLen_of_null hpre hinv.batch hnull)).symm
  have heq : d0 = d' := by simp [d0, d', electLengthData, hlen]
  rw [heq] at h1
  obtain ⟨t2, r2, h2⟩ := lenOrigTail_run (d := d') hpre ⟨hinv.len0, hinv.len1, hinv.batch⟩ rfl h1
  have hdata : afterElection L d = afterOrig L d' := by
    simp only [afterElection, d', afterOrig, firstLenSite, hnull, ↓reduceIte]
  rw [hdata]
  exact ⟨t2, (run_rtg r1).trans r2, h2⟩

private theorem electLoadOrig_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hinv : Inv P L g d)
    {u : TState} (hnull : paramWord L 80 8 ≠ 0)
    (hu : At u 2178 ((49, .pred false) :: atFacts P L g (electLengthData P d) 2178)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' (afterElection L d).site.pc (facts P L g (afterElection L d)) := by
  let d' := { d with site := Site.lenOrig }
  have hbatch : ctaidY L g < P.b := hinv.batch
  have hb := hpre.bLt
  have hcta32 : ctaidY L g < 2 ^ 32 := by omega
  have hword := Thread.paramWord_lt L 80
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 3 u = some t1 ∧
      At t1 2181 (facts P L g d') := by
    dsimp only [atFacts] at hu
    seg_fp hu using
      tma_values
      norm_bits [Nat.mod_eq_of_lt hcta32, Nat.mod_eq_of_lt hword, Nat.mul_comm]
  have hdata : afterElection L d = d' := by
    simp only [afterElection, firstLenSite, hnull, ↓reduceIte, d']
  rw [hdata]
  exact ⟨t1, run_rtg r1, h1⟩

private theorem electLengthChoice_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0)
    (hinv : Inv P L g d) {u : TState}
    (hu : At u 2177 (atFacts P L g (electLengthData P d) 2177)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' (afterElection L d).site.pc (facts P L g (afterElection L d)) := by
  let d0 := electLengthData P d
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2178 ((49, .pred (decide (paramWord L 80 8 = 0))) :: atFacts P L g d0 2178) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using
      change (Value.pred (PTX.compare .eq .b 64
        (truncBits 64 (BitVec.ofNat 64 (paramWord L 80 8))) (truncBits 64 (BitVec.ofInt 64 0))) =
        .pred (decide (paramWord L 80 8 = 0)))
      rw [compare_pointer_zero (Thread.paramWord_lt L 80)]
  by_cases hnull : paramWord L 80 8 = 0
  · have h1' : At t1 2178 ((49, .pred true) :: atFacts P L g d0 2178) := by
      simpa [hnull] using h1
    obtain ⟨t2, r2, h2⟩ := electNull_run hpre hinv hnull h1'
    exact ⟨t2, (run_rtg r1).trans r2, h2⟩
  · have h1' : At t1 2178 ((49, .pred false) :: atFacts P L g d0 2178) := by
      simpa [hnull] using h1
    obtain ⟨t2, r2, h2⟩ := electLoadOrig_run hpre hinv hnull h1'
    exact ⟨t2, (run_rtg r1).trans r2, h2⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem elected_start_run {mem0 : Mem0} {d : D} (hpre : Pre P L mem0) (hinv : Inv P L g d)
    {u : TState}
    (hu : At u 2166 ((4116, b32 (PTX.laneOf L g)) :: (4117, .pred true) ::
      atFacts P L g (electLengthData P d) 2165)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
      At t' (afterElection L d).site.pc (facts P L g (afterElection L d)) := by
  let d0 := electLengthData P d
  obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 4 u = some t1 ∧
      At t1 2170 (atFacts P L g d0 2170) := by
    dsimp only [atFacts] at hu ⊢
    seg_fp hu using skip
  have hb : ctaidY L g < P.b := hinv.batch
  obtain ⟨t2, r2, h2⟩ := electBatch_run hpre hb t1 h1
  obtain ⟨t3, r3, h3⟩ := electLengths_run hpre rfl rfl t2 h2
  obtain ⟨t4, r4, h4⟩ := electLengthChoice_run hpre hinv h3
  exact ⟨t4, (run_rtg (run_comp (run_comp r1 r2) r3)).trans r4, h4⟩

private theorem afterElection_good {d : D} {t : TState} (hd : d.site = .elect) (hinv : Inv P L g d)
    (ht : At t (afterElection L d).site.pc (facts P L g (afterElection L d))) :
    (code P L g).Good (some (afterElection L d)) t := by
  have hi : Inv P L g (afterElection L d) :=
    inv_setSite hinv (by simp [hd]) (by simp [hd]) (firstLenSite L)
      (by unfold firstLenSite; split
          · split <;> first | exact True.intro | assumption
          · assumption)
  have hs : (afterElection L d).site.sub = 0 := by
    simp only [afterElection, firstLenSite]
    split
    · split <;> rfl
    · rfl
  have ha : accAt (afterElection L d) = [] := by
    simp only [afterElection, firstLenSite]
    split
    · split <;> rfl
    · rfl
  exact good_of_at ht hs ha hi

/-- The election's leader reads the launch parameters and takes the first optional length load
or the Q-copy poll. The unelected lane leaves this role for the idle hand-off. -/
theorem stepAt_elect {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .elect)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hpc : d.site.pc = 2165 := by rw [hd]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2165)
  obtain ⟨mask, instanceId, leader, he, hu⟩ := fires_elect hf
  by_cases hleader : leader = PTX.laneOf L g
  · subst leader
    simp only [beq_self_eq_true] at hu
    have hu' := at_elected hd hat hu
    obtain ⟨t', hr, ht⟩ := elected_start_run hpre hinv hu'
    have hb : ctaidY L g < P.b := hinv.batch
    refine Or.inl (Or.inr ⟨afterElection L d, t', ?_, hr, afterElection_good hd hinv ht⟩)
    simp [next, hd, he, afterElection, hb]
  · exact Or.inl (Or.inl (by simp [next, hd, he, hleader]))

/-- The role's loop requires only the election and length-load steps to complete its site proof. -/
theorem steps_of_start {mem0 : Mem0} (hpre : Pre P L mem0)
    (helect : ∀ d, d.site = .elect → (code P L g).StepAt d)
    (horig : ∀ d, d.site = .lenOrig → (code P L g).StepAt d)
    (hextra : ∀ d, d.site = .lenExtra → (code P L g).StepAt d) :
    ∀ d, (code P L g).StepAt d := by
  intro d
  cases hd : d.site with
  | elect => exact helect d hd
  | lenOrig => exact horig d hd
  | lenExtra => exact hextra d hd
  | waitQ => exact stepAt_waitQ hpre d hd
  | waitLast => exact stepAt_waitLast hpre d hd
  | waitCoord => exact stepAt_waitCoord hpre d hd
  | waitFree => exact stepAt_waitFree hpre d hd
  | coord k j =>
    by_cases hj : j.val + 1 < 4
    · exact stepAt_coordMid hpre d hd hj
    · exact stepAt_coordLast hpre d hd hj
  | issue k => exact stepAt_issue hpre d hd
  | rawReady => exact stepAt_rawReady hpre d hd
  | coordFree => exact stepAt_coordFree hpre d hd
  | barrier => exact stepAt_barrier hpre d hd
  | exit => exact stepAt_exit d hd

/-- The per-site soundness obligations for the kernel's hand-off machine. -/
theorem steps {mem0 : Mem0} (hpre : Pre P L mem0) : ∀ d, (code P L g).StepAt d :=
  steps_of_start hpre (stepAt_elect hpre) (stepAt_lenOrig hpre) (stepAt_lenExtra hpre)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Tma
