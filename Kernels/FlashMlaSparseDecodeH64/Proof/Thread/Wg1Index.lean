-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SignedBits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Data.Indices
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.Code
public import Lemmas.Flow.Segment
public import Lemmas.Flow.Store
public import Lemmas.Flow.StoreBytes
public import Lemmas.Flow.StoreValue
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.Events
public import Lemmas.Flow.Next

@[expose] public section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! # `wg1Index`: the sparse-index producer of the FlashMLA sparse decode kernel

Warp 7 of warpgroup 1 (pcs 2332-2586, `kernel.cuh:535-616`, the "indices transformation warp")
turns one query row's sparse index array into the TMA gather coordinates and the valid-slot mask
of the kernel's four-slot ring (`NUM_INDEX_BUFS = 4`, `config.h:50`):

* it reads the row's two runtime lengths at pcs 2360 and 2365 and the row's index pairs at pcs
  2403, 2429, 2501 and 2517, all with `ld.global.nc` (the assumption A6 `ncReadOnly` covers
  the six sites, `Data/Sites.lean` `ncLoads`);
* for each block `b` of the row it computes, per lane and per pair `i`, the physical KV row of
  the index (`Data/Indices.rowOf`, `kernel.cuh:570-571,584`) and the slot's validity
  (`Data/Indices.kvSlotValid`, `kernel.cuh:582`); a block of the extra cache is rebased on the
  main cache's block count and uses the extra cache's page size and block stride
  (`kernel.cuh:555,560-563`);
* it writes the block's two rows into `tma_coord[phase][lane]` and the quad's validity byte into
  `is_token_valid[phase][lane/4]` (pcs 2471/2474 for the main cache and 2560/2563 for the extra
  cache, shared offsets 221728 and 221696 of `wksp_buf`), then arrives on
  `bar_valid_coord_ready[phase]` (2476/2565) after polling `bar_valid_coord_free[phase]`
  (2446/2534);
* it walks the main cache's `numOrigBlocks` blocks (pcs 2426-2494) and then the extra cache's
  blocks (pcs 2512-2582), prefetching the next block's index pair one iteration ahead, and leaves
  through `everyone_sync` (2585) to the program's `ret`.

The abstract states (`Site`) are the role's event instructions: the six `.nc` loads, the two
mbarrier polls, the four `shfl.bfly` reductions, the four shared stores, the two arrivals and the
final CTA barrier. The registers the role carries are functions of a small state (`D`): the ring
slot `phase` and its parity `par`, the block being processed and its cache tag via `Site.extra`,
the two index values of that block and of the block prefetched ahead, and the two lengths the
loads returned. `Inv` records the loop invariant; `table` gives every register the role tracks
its value in `D`.

The `.nc` loads are not ordinary memory reads: `Assumption.ncReadOnly` fixes their bytes to the
launch content, so a state continues only when a length load returns `P.topkLen` /
`P.extraTopkLen` of the thread's batch and an index load returns the row's index at the slot's
position (`slotIdx`); any other bytes are not followed (the prologue's rule for its warp-index
broadcast is the same one). Each `shfl.bfly` continues only when the received value is the one
the partner lane's own indices give (`laneWord`, `pairWord`), which is what the reduction of a
quad's four 2-bit masks produces.

## The entry interface

This file imports the prologue's machine (`Proof/Thread/Prologue.lean`) and reuses its launch
definitions (`ctaOf`, `tidOf`, `laneOf`, `warpOf`, `ctaidX`, `ctaidY`) and its value table
(`Proof.values`, `Proof.valueOf`). The prologue's own machine stops at each role's first event —
for warpgroup 1 that is its `setmaxnreg` at pc 1842 — and it has no hand-off state at pc 2332,
so its `EntryFacts` do not exist for this role. The role's start is therefore stated against the
explicit `Entry` structure: a thread state at pc 2332 whose `param_0` address, launch reads and
lane index are the prologue's values and whose warp index is 7 (warp 7 is this role). `Entry`
also carries the two facts the role needs that the prologue's tables do not state: its
`%ctaid.y` is a batch index of the kernel's grid and its `%ctaid.x` is a query index. A hand-off
the prologue might grow for pc 2332 would have to produce exactly `Entry`.

## Proof coverage

`start` follows the launch-dependent length pointer branches and produces `AtD` of `init`.
`steps` handles the length and index loads, both free polls, the two butterfly shuffles, the
coordinate words and the validity byte, publication to the ready barrier, and the final
named sync. The two cache loops share the same abstract transition and maintain `Inv` when
they advance the four-slot ring and switch from the main cache to the extra cache.

The load and coordinate proofs use `Data/Indices` to connect the concrete words with the
row indices. `coordValue_valid` gives `rowOf` for a valid slot. `coordValue_invalid` gives
the invalid marker otherwise. `validWord_leader` identifies the quad's stored byte and
`quadByte_eq_zero_iff` characterizes when all four lanes lack valid slots. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Wg1Index

/-- The assumptions the role is evaluated under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ## The thread's place in the launch

`Proof/Thread/Prologue.lean` defines a thread's CTA and thread index (`ctaOf`, `tidOf`,
`laneOf`, `warpOf`), the CTA's `%ctaid` coordinates (`ctaidX`, `ctaidY`) and the shared address
`sb` of a byte above the dynamic shared base; the role reuses them (they are in this
namespace, one level up). -/

/-- The batch whose sparse index row the thread's CTA reads (`%ctaid.y`). -/
def eOf (L : Launch) (g : Nat) : Nat := ctaidY L g

/-- The query whose sparse index row the thread's CTA reads (`%ctaid.x`). -/
def qOf (L : Launch) (g : Nat) : Nat := ctaidX L g

/-! ## The index arithmetic of the role -/

/-- The 32-bit pattern of an index, as the `s32` load of the index array returns it. -/
def ipat (z : Int) : Nat := i32Bits z

/-- `cvt.s32.s8`: the low 8 bits sign-extended to 32. -/
def sx8 (x : Nat) : Nat :=
  if x % 256 < 128 then x % 256 else x % 256 + (2 ^ 32 - 256)

/-- The index the `.nc` load of slot `(b, lane, i)` returns: the row's index at the slot's
position in its own cache's array (`Data/Indices.slotIndex`). -/
def slotIdx (P : Params) (L : Launch) (g b lane i : Nat) : Int :=
  slotIndex (P.topkLen (eOf L g)) (P.idx (eOf L g) (qOf L g)) (P.extraIdx (eOf L g) (qOf L g))
    b lane i

/-- The block stride in token rows of slot `(b, lane, i)`
(`cur_tma_coords_step_per_block / BYTES_PER_TOKEN`, `kernel.cuh:540-541,561`). -/
def slotStride (P : Params) (L : Launch) (g b : Nat) : Nat :=
  slotBlockStride (P.topkLen (eOf L g)) P.blockStride P.extraBlockStride b

/-- The tokens per page block of slot `(b, lane, i)` (`cur_block_size`, `kernel.cuh:560`). -/
def slotPg (P : Params) (L : Launch) (g b : Nat) : Nat :=
  slotPage (P.topkLen (eOf L g)) P.page P.extraPage b

/-- The `tma_coord` word of a slot as the code computes it: `(unsigned)idx / page` times the
block's row stride plus `idx % page` (`kernel.cuh:570,571,584`), on the hardware's 32-bit
pattern. Unlike `Data/Indices.rowOf` this is the hardware's value for the marker `-1` too; the
word is only stored for a valid slot (`coordValue`). -/
def rowBits (P : Params) (L : Launch) (g b lane i : Nat) : Nat :=
  ipat (slotIdx P L g b lane i) / slotPg P L g b * (slotStride P L g b / bytesPerToken) +
    ipat (slotIdx P L g b lane i) % slotPg P L g b

/-- The validity an index gives its slot, as the code's `cur_idx != -1 && abs_pos + i < len`
computes it (`Data/Indices.kvSlotValid`, `kernel.cuh:582`). -/
def validBit (P : Params) (L : Launch) (g b lane i : Nat) : Bool :=
  kvSlotValid (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b lane i
    (slotIdx P L g b lane i)

/-- The `tma_coord` word the code stores: the physical row of a valid slot, the `-1` marker
otherwise (`kernel.cuh:577-585`). -/
def coordValue (P : Params) (L : Launch) (g b lane i : Nat) : Nat :=
  if validBit P L g b lane i then rowBits P L g b lane i else 2 ^ 32 - 1

/-- Lane `l`'s two validity bits of block `b`, as the code's `selp 1` and `selp 2` compute
them (`kernel.cuh:577-583`). -/
def laneMask (P : Params) (L : Launch) (g b l : Nat) : Nat :=
  (if validBit P L g b l 0 then 1 else 0) + (if validBit P L g b l 1 then 2 else 0)

/-- Lane `l`'s mask shifted into its byte position (`<< 2 * (l % 4)`). -/
def laneByte (P : Params) (L : Launch) (g b l : Nat) : Nat :=
  laneMask P L g b l * 2 ^ (2 * (l % 4))

/-- The value of lane `l`'s register before the first shuffle: `cvt.s32.s8` of its shifted mask
(`%r606`). -/
def laneWord (P : Params) (L : Launch) (g b l : Nat) : Nat := sx8 (laneByte P L g b l)

/-- The value of lane `l`'s register before the second shuffle: `cvt.s32.s8` of the OR of its own
and its partner lane's words (`%r609`). -/
def pairWord (P : Params) (L : Launch) (g b l : Nat) : Nat :=
  sx8 (laneWord P L g b l ||| laneWord P L g b (l ^^^ 1))

/-- The validity byte of the quad of lanes `4q..4q+3`: the OR of the four lanes' shifted masks
(`%r508`, `kernel.cuh:578-583`). -/
def quadByte (P : Params) (L : Launch) (g b qb : Nat) : Nat :=
  laneByte P L g b qb ||| laneByte P L g b (qb + 1) ||| laneByte P L g b (qb + 2) |||
    laneByte P L g b (qb + 3)

/-! ## The sites

One state per event instruction of the role. `.pair extra first hi` is the `ld.global.nc.v2.s32`
that loads a block's index pair: `extra` selects the extra cache's array, `first` the row's
pre-loop load (2403, 2501) against the loop's one-ahead prefetch (2429, 2517), and `hi` the
second of the instruction's two 4-byte elements. `.coord extra hi` is the same for the two words
of the `st.shared.v2.b32` into `tma_coord`. -/

inductive Site where
  /-- The row's runtime main-cache length, `ld.global.nc` (2360). -/
  | lenOrig
  /-- The row's runtime extra-cache length, `ld.global.nc` (2365). -/
  | lenExtra
  /-- A block's index pair, `ld.global.nc.v2.s32` (2403, 2429, 2501, 2517). -/
  | pair (extra first hi : Bool)
  /-- The poll of `bar_valid_coord_free[phase]` (2446, 2534). -/
  | waitFree (extra : Bool)
  /-- The first `shfl.bfly` of the quad's validity bits (2464, 2553). -/
  | quad1 (extra : Bool)
  /-- The second `shfl.bfly` of the quad's validity bits (2467, 2556). -/
  | quad2 (extra : Bool)
  /-- The `st.shared.v2.b32` into `tma_coord` (2471, 2560). -/
  | coord (extra hi : Bool)
  /-- The `st.shared.b8` into `is_token_valid` (2474, 2563). -/
  | valid (extra : Bool)
  /-- The arrival on `bar_valid_coord_ready[phase]` (2476, 2565). -/
  | ready (extra : Bool)
  /-- The `barrier.sync` of `everyone_sync` (2585). -/
  | barrier
  deriving DecidableEq

/-- The program counter of a site. -/
def Site.pc : Site → Nat
  | .lenOrig => 2360
  | .lenExtra => 2365
  | .pair false true _ => 2403
  | .pair false false _ => 2429
  | .pair true true _ => 2501
  | .pair true false _ => 2517
  | .waitFree false => 2446
  | .waitFree true => 2534
  | .quad1 false => 2464
  | .quad1 true => 2553
  | .quad2 false => 2467
  | .quad2 true => 2556
  | .coord false _ => 2471
  | .coord true _ => 2560
  | .valid false => 2474
  | .valid true => 2563
  | .ready false => 2476
  | .ready true => 2565
  | .barrier => 2585

/-- The sub-step of a site: the second element of a two-element load. -/
def Site.sub : Site → Nat
  | .pair _ _ true => 1
  | .coord _ true => 1
  | _ => 0

/-- The cache tag of a site's block; `none` before a length is known. -/
def Site.extra : Site → Option Bool
  | .pair e _ _ => some e
  | .waitFree e => some e
  | .quad1 e => some e
  | .quad2 e => some e
  | .coord e _ => some e
  | .valid e => some e
  | .ready e => some e
  | .lenOrig | .lenExtra | .barrier => none

/-- Whether the site is one of a block's body: the pair is loaded, the slots are computed, and
the two shared stores and the arrival follow. -/
def Site.inBody : Site → Bool
  | .waitFree _ | .quad1 _ | .quad2 _ | .coord _ _ | .valid _ | .ready _ => true
  | _ => false

/-- Whether the state holds a loaded pair in its two index fields: the body sites and the loop's
prefetch site, whose pair belongs to the block the body processes. -/
def Site.hasPair : Site → Bool
  | .pair _ false _ => true
  | .waitFree _ | .quad1 _ | .quad2 _ | .coord _ _ | .valid _ | .ready _ => true
  | _ => false

/-- The registers of a site that its facts must not state. A two-element load writes its
destination registers at the site's own pc, so they are not live at that pc and its facts never
carry them: the list is empty. -/
def Site.pendingRegs : Site → List Nat
  | _ => []

/-! ## The abstract state and its invariant -/

/-- The role's state: the next event, the ring slot and its parity, the block whose slots the
body computes and that block's two index values, the pair prefetched for the next block, and the
two lengths the loads returned. `i0`/`i1` are the index array's `s32` values (`Int`), so `-1` is
the invalid marker. -/
structure D where
  site : Site
  /-- The block whose slots the body computes (`0 ≤ block < Data/Indices.totalBlocks`). -/
  block : Nat
  /-- The `tma_coord` ring slot (`%r2977`). -/
  phase : Nat
  /-- The ring's parity (`%rs456`). -/
  par : Nat
  /-- The first index of the current block (`%r2974`, `%r2982`). -/
  i0 : Int
  /-- The second index of the current block (`%r2973`, `%r2981`). -/
  i1 : Int
  /-- The first index of the block prefetched ahead. -/
  n0 : Int
  /-- The second index of the block prefetched ahead. -/
  n1 : Int
  /-- The row's main-cache length (`%r2968`). -/
  len0 : Nat
  /-- The row's extra-cache length (`%r2969`). -/
  len1 : Nat

/-- The accumulator of a state: at the second element of a pair load the first element's value is
in the accumulator (`afterLoad`), and the element's index is the state's first or prefetched index
(`next`). Every other site is at an instruction boundary with an empty accumulator. -/
def accOf (d : D) : List Value :=
  match d.site with
  | .pair _ true true => [b32 (ipat d.i0)]
  | .pair _ false true => [b32 (ipat d.n0)]
  | _ => []

/-- The shared byte offset of the `tma_coord` word pair of ring slot `phase` and the thread's
lane (`kernel.cuh:568,570`; `tma_coord` is at `wksp_buf + 221728`). -/
def coordOff (L : Launch) (g : Nat) (phase : Nat) : Nat :=
  221728 + 256 * phase + 8 * laneOf L g

/-- The shared byte offset of the validity byte of ring slot `phase` and the thread's quad
(`is_token_valid` is at `wksp_buf + 221696`). -/
def validOff (L : Launch) (g : Nat) (phase : Nat) : Nat :=
  221696 + 8 * phase + laneOf L g / 4

/-- The shared byte offset of `bar_valid_coord_ready[phase]` (`Data/Barriers.mbars`). -/
def readyOff (phase : Nat) : Nat := 222840 + 8 * phase

/-- The shared byte offset of `bar_valid_coord_free[phase]` (`Data/Barriers.mbars`). -/
def freeOff (phase : Nat) : Nat := 222872 + 8 * phase

/-- The loop position selects a valid pair address. At the second sub-step the saved low
word is the corresponding slot's index. -/
def pairInvariant (P : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  match d.site with
  | .pair extra first high =>
    (if first then
      if extra then d.block = numOrigBlocks d.len0 else True
    else
      d.block + 1 < (if extra then totalBlocks d.len0 d.len1 else numOrigBlocks d.len0)) ∧
    (if high then
      if first then d.i0 = slotIdx P L g d.block (laneOf L g) 0
      else d.n0 = slotIdx P L g (d.block + 1) (laneOf L g) 0
    else True)
  | _ => True

/-- **The role's loop invariant**: the ring slot and parity, the block and its cache tag, the two
index values as the row's index array gives them, and the two lengths as the row's runtime
lengths. The stored coordinates and validity bytes are functions of these fields (`coordValue`,
`quadByte`), and the shared destinations are the ring slot's (`coordOff`, `validOff`,
`readyOff`, `freeOff`). -/
structure Inv (P : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The ring slot is one of the four index buffers. -/
  phase : d.phase < 4
  /-- The ring parity is a bit. -/
  par : d.par < 2
  /-- The ring slot is the block's position in the ring. -/
  phase_block : d.site ≠ .barrier → d.phase = d.block % 4
  /-- The ring parity is the block's phase: the tail flips it when the slot wraps (pc 2481).
  At the final barrier the ring is no longer used and its fields are not constrained: the
  barrier's arrival flips the parity for the next block while the block stays the last one. -/
  par_block : d.site ≠ .barrier → d.par = d.block / 4 % 2
  /-- The row's pre-loop pair loads are block 0's: the code clears the ring slot and the counter
  before them, so only the row's first block reaches them. -/
  firstBlock : (d.site = .pair false true false ∨ d.site = .pair false true true) → d.block = 0
  /-- The first length is the row's runtime main-cache length. -/
  len0 : d.len0 = P.topkLen (eOf L g)
  /-- The second length is the row's runtime extra-cache length. -/
  len1 : d.len1 = P.extraTopkLen (eOf L g)
  /-- The block is one of the row's padded blocks. -/
  block : d.block < totalBlocks d.len0 d.len1
  /-- A main-cache site's block is a main-cache block. -/
  tagMain : d.site.extra = some false → d.block < numOrigBlocks d.len0
  /-- An extra-cache site's block is an extra-cache block. -/
  tagExtra : d.site.extra = some true → numOrigBlocks d.len0 ≤ d.block
  /-- The two index values are the row's indices at the block's slot positions. -/
  slot0 : d.site.hasPair = true → d.i0 = slotIdx P L g d.block (laneOf L g) 0
  slot1 : d.site.hasPair = true → d.i1 = slotIdx P L g d.block (laneOf L g) 1
  /-- The prefetched pair is the next block's, when the loop's head prefetches it: a main-cache
  body prefetches while there are main-cache blocks left, an extra-cache body while there are
  blocks left at all. -/
  pref0 : d.site.inBody = true → (match d.site.extra with
      | some false => d.block + 1 < numOrigBlocks d.len0
      | some true => d.block + 1 < totalBlocks d.len0 d.len1
      | none => False) → d.n0 = slotIdx P L g (d.block + 1) (laneOf L g) 0
  pref1 : d.site.inBody = true → (match d.site.extra with
      | some false => d.block + 1 < numOrigBlocks d.len0
      | some true => d.block + 1 < totalBlocks d.len0 d.len1
      | none => False) → d.n1 = slotIdx P L g (d.block + 1) (laneOf L g) 1
  /-- The row's length loads precede the block loop: their sites have not advanced the block
  counter, so the pre-loop pair loads that follow them are block 0's. -/
  blockZero : (d.site = .lenOrig ∨ d.site = .lenExtra) → d.block = 0
  /-- The index loads save the low half and never prefetch beyond the active cache. -/
  pairLoad : pairInvariant P L g d

/-- The first site of the role: the site of its first event under the parameters' length
pointers. A null length pointer reads the parameter's constant instead of the row's runtime
length, so the role's first event is then the next load. The code tests the pointer *words* for
null (`setp.eq.b64`, pcs 2356 and 2361); `Entry.ptrOrig` and `Entry.ptrExtra` tie those tests to
the parameters' `Option`s, which excludes the degenerate `some 0` binding. -/
def firstSite (P : Params) : Site :=
  if P.topkLenBase.isSome then .lenOrig
  else if P.extraTopkLenBase.isSome then .lenExtra
  else .pair false true false

/-- The initial state: the first site, block 0, ring slot 0 with parity 0, no indices, and the
two lengths the parameters give (a runtime length overrides its constant at the load). -/
def init (P : Params) (L : Launch) (g : Nat) : D where
  site := firstSite P
  block := 0
  phase := 0
  par := 0
  i0 := 0
  i1 := 0
  n0 := 0
  n1 := 0
  len0 := P.topkLen (eOf L g)
  len1 := P.extraTopkLen (eOf L g)

/-! ## The register table

The table covers the tracked live registers at the role's event sites. Its two index pairs
hold the current block and the look-ahead block. During a vector load, the first word stays
in the accumulator until the second element arrives. -/

/-- `cvt.s64.s32` of a 32-bit word, as the conversion rule computes it. -/
def cvtS32 (x : Nat) : Nat :=
  (toSigned 32 (truncBits 32 (BitVec.ofNat 64 x)) % 18446744073709551616).toNat

/-- `mul.wide.s32` of two 32-bit words, as the multiplication rule computes it. -/
def mulWideS32 (a b : Nat) : Nat :=
  ((toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) *
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 b))) % 18446744073709551616).toNat

/-- The byte offset of the CTA's main index row, as pcs 2385-2388 compute it
(`stride_indices_sq * %ctaid.x + stride_indices_b * %ctaid.y`). -/
def idxRowOff (_P : Params) (L : Launch) (g : Nat) : Nat :=
  (cvtS32 (Thread.paramWord L 176 4 * ctaidX L g % 4294967296) +
    cvtS32 (Thread.paramWord L 172 4 * ctaidY L g % 4294967296)) %
    18446744073709551616

/-- The byte address of the CTA's extra index row: its base plus four times the row offset,
as pcs 2389-2393 compute it. -/
def extraRowOff (_P : Params) (L : Launch) (g : Nat) : Nat :=
  (Thread.paramWord L 136 8 % 18446744073709551616 +
    ((cvtS32 (Thread.paramWord L 212 4 * ctaidX L g % 4294967296) % 18446744073709551616 +
        mulWideS32 (Thread.paramWord L 208 4) (ctaidY L g) % 18446744073709551616) %
      18446744073709551616 % 18446744073709551616 *
      (4 % 18446744073709551616 % 18446744073709551616) % 18446744073709551616)) %
    18446744073709551616

/-- The value of the extra-cache length register at state `d`: the parameter's constant until
the extra-cache length load at pc 2365 has fired, the state's length afterwards. The load's own
site still sees the constant (the load writes the register at its pc). -/
def len1Reg (P : Params) (d : D) : Nat :=
  match d.site with
  | .lenOrig | .lenExtra => P.extra_topk
  | _ => d.len1

/-- The value of the main loop's block-count register `%r2980` at state `d`. -/
def countReg (d : D) : Nat :=
  match d.site with
  | .pair true true _ => numOrigBlocks d.len0
  | .pair true false _ => d.block + 1
  | .waitFree true | .quad1 true | .quad2 true | .coord true _ | .valid true | .ready true =>
    d.block + 1
  | _ => numOrigBlocks d.len0

/-- Outside the two length sites the extra-cache length register holds the state's
extra-cache length. -/
theorem len1Reg_ne {P : Params} {d : D} (h : d.site ≠ .lenOrig) (h2 : d.site ≠ .lenExtra) :
    len1Reg P d = d.len1 := by
  cases hs : d.site <;> simp_all [len1Reg]

/-- At the main-cache length site the extra-cache length register still holds the parameter's
constant. -/
theorem len1Reg_lenOrig {P : Params} {d : D} (h : d.site = .lenOrig) :
    len1Reg P d = P.extra_topk := by
  unfold len1Reg
  rw [h]

/-- The block-count register of a main-cache pre-load state is the main cache's block count. -/
theorem countReg_pair_false {d : D} (h : d.site = .pair false true false) :
    countReg d = numOrigBlocks d.len0 := by
  unfold countReg
  rw [h]

/-! ## The words the body's tails form

The role's two caches index the same index array layout: block `b` of a cache has its lanes' pairs
at `indices_base + 4 * rowOffset + 8 * lane + 256 * b` of the main cache and
`extra_indices_base + 8 * lane + 256 * b` of the extra cache (`%rd3033`, `%rd4029`, `%rd3041`,
`%rd3043`). The validity reduction ORs a lane's word with its partner's and the quad's other pair
(`%r508`, `%r511`), and `accOf` carries the first element of a pair load. -/

/-- The main-cache index-pair address of block `b` (`%rd3033` at block 0, `%rd4029` advanced by
256 bytes per block, pcs 2399-2402, 2415-2419, 2489), in the form the code's `add.s64` chain
leaves it: the indices base plus four times the row offset, plus eight bytes per lane. -/
def pairAddr (P : Params) (L : Launch) (g b : Nat) : Nat :=
  ((Thread.paramWord L 72 8 % 2 ^ 64 + idxRowOff P L g % 2 ^ 64 * 4 % 2 ^ 64) % 2 ^ 64 +
    (2 * laneOf L g % 2 ^ 32 * 4 % 2 ^ 64)) + 256 * b

/-- The extra-cache index-pair address of block `b` of the extra cache (`%rd3041` at its first
block, `%rd3043` advanced by 256 bytes per block, pcs 2499-2500, 2515-2516, 2577). -/
def extraPairAddr (P : Params) (L : Launch) (g b : Nat) : Nat :=
  (extraRowOff P L g % 2 ^ 64 + (2 * laneOf L g % 2 ^ 32 * 4 % 2 ^ 64)) + 256 * b

/-- The word the first shuffle's partner ORs into the lane's byte (`%r608`, `%r647`): the partner
lane's sign-extended byte word and the lane's own byte. -/
def quadWord (P : Params) (L : Launch) (g b l : Nat) : Nat :=
  laneWord P L g b (l ^^^ 1) ||| laneByte P L g b l

/-- The word `st.shared.b8` stores as the quad's validity byte (`%r508`, `%r511`): the four lanes'
shifted masks. -/
def validWord (P : Params) (L : Launch) (g b l : Nat) : Nat :=
  quadWord P L g b l ||| pairWord P L g b (l ^^^ 2)

/-- The registers the role tracks. -/
def tracked : List Nat :=
  [503, 504, 456, 459, 460, 461, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500,
   501, 502, 505, 506, 507, 509, 510, 559, 560, 561, 562, 585, 586, 587, 588, 589, 591, 592,
   17, 568, 594, 598, 599, 600, 601, 602, 603, 604, 605, 612, 613, 614, 623, 624, 625, 626,
   627, 629, 630, 632, 636, 637, 638, 640, 641, 642, 643, 651, 652, 653, 2968, 2969, 2970, 2971,
   2972,
   2973,
   2974, 2977, 2978, 2979, 2980, 2981, 2982, 2991, 3009, 3010, 3011, 3012, 3023, 3024, 3025,
   3026,
   -- the body's tails: the validity reduction, the prefetched pair, the I/O addresses and the
   -- barrier's operands
   20, 35, 508, 511, 606, 608, 609, 644, 645, 647, 648, 659, 660,
   2975, 2976, 2983, 2984, 3013, 3014, 3033, 3041, 3043, 4029]

/-- The registers of state `d` with their values. -/
def table (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let lane := laneOf L g
  let numOrig := numOrigBlocks d.len0
  let total := totalBlocks d.len0 d.len1
  let pair0 := if d.site.hasPair then ipat d.i0 else 0
  let pair1 := if d.site.hasPair then ipat d.i1 else 0
  -- the prefetched pair of a body: the loop head read one block ahead only when a block follows
  let prefMain := d.block + 1 < numOrig
  let prefExtra := d.block + 1 < total
  let npair0 := if prefMain then ipat d.n0 else ipat d.i0
  let npair1 := if prefMain then ipat d.n1 else ipat d.i1
  let epair0 := if prefExtra then ipat d.n0 else ipat d.i0
  let epair1 := if prefExtra then ipat d.n1 else ipat d.i1
  [(459, b32 (ctaidX L g)), (460, b32 (ctaidY L g)), (461, b32 (tidOf L g)), (466, b32 lane),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (490, b32 (Thread.paramWord L 164 4)), (491, b32 (Thread.paramWord L 200 4)),
   (492, b32 (Thread.paramWord L 172 4)),
   (493, b32 (Thread.paramWord L 176 4 * ctaidX L g % 2 ^ 32)),
   (494, b32 (Thread.paramWord L 208 4)),
   (495, b32 (Thread.paramWord L 212 4 * ctaidX L g % 2 ^ 32)),
   (496, b32 (2 * lane)), (497, b32 (Thread.paramWord L 36 4)),
   (498, b32 (2 * (tidOf L g % 4))),
   (499, b32 (8 * lane)), (500, b32 (tidOf L g % 4)), (501, b32 (lane / 4)),
   (502, b32 (Thread.paramWord L 116 4)),
   (505, sb L (8 * lane)), (506, b32 (P.blockStride / bytesPerToken)),
   (507, sb L (8 * d.phase)), (510, sb L (8 * d.phase)),
   (509, b32 (P.extraBlockStride / bytesPerToken)),
   (559, b32 (Thread.paramWord L 0 4)), (560, b32 (Thread.paramWord L 176 4)),
   (561, b32 (Thread.paramWord L 212 4)), (562, b32 (2 * tidOf L g)),
   (2968, b32 d.len0),
   (568, b32 (origPadded d.len0)),
   (17, .pred false),
   (2969, b32 (len1Reg P d)),
   (456, .bits 16 (BitVec.ofNat 64 d.par)),
   (2970, b32 (d.block + (2 ^ 32 - numOrig))), (2971, b32 (2 * lane + 1 + 64 * d.block)),
   (2972, b32 (d.block + 1)), (2973, b32 pair1), (2974, b32 pair0),
   (2977, b32 d.phase), (2978, b32 (d.block + (2 ^ 32 - total))),
   (2979, b32 (64 + 2 * lane + 64 * (d.block - numOrig))),
   (2980, b32 (countReg d)),
   (2981, b32 pair1), (2982, b32 pair0),
   (585, sb L (freeOff d.phase)), (586, b32 (1 - d.par)), (587, b32 10000000),
   (588, b32 (2 * lane + 64 * d.block)), (589, b32 (ipat d.i0 / P.page)),
   (591, b32 (ipat d.i0 % P.page)),
   (592, b32 (ipat d.i1 / P.page)), (594, b32 (ipat d.i1 % P.page)),
   (598, b32 (if validBit P L g d.block lane 0 then 1 else 0)),
   (599, b32 (ipat d.i0 / P.page * (P.blockStride / bytesPerToken) + ipat d.i0 % P.page)),
   (600, b32 (coordValue P L g d.block lane 0)),
   (601, b32 (if validBit P L g d.block lane 1 then 2 else 0)),
   (602, b32 ((if validBit P L g d.block lane 1 then 2 else 0) |||
     (if validBit P L g d.block lane 0 then 1 else 0))),
   (603, b32 (ipat d.i1 / P.page * (P.blockStride / bytesPerToken) + ipat d.i1 % P.page)),
   (604, b32 (coordValue P L g d.block lane 1)),
   (605, b32 (laneByte P L g d.block lane)),
   -- the store address words hold the ring offset only: the fixed part is the store's immediate
   (612, sb L (8 * lane + 256 * d.phase)), (613, sb L (8 * d.phase + lane / 4)),
   (614, sb L (readyOff d.phase)),
   (623, sb L (freeOff d.phase)), (624, b32 (1 - d.par)), (625, b32 10000000),
   (626, b32 (2 * lane + 64 * (d.block - numOrig))),
   (627, b32 (ipat d.i0 / P.extraPage)), (629, b32 (ipat d.i0 % P.extraPage)),
   (630, b32 (ipat d.i1 / P.extraPage)), (632, b32 (ipat d.i1 % P.extraPage)),
   (636, b32 (if validBit P L g d.block lane 0 then 1 else 0)),
   (637, b32 (ipat d.i0 / P.extraPage * (P.extraBlockStride / bytesPerToken) +
     ipat d.i0 % P.extraPage)),
   (638, b32 (coordValue P L g d.block lane 0)),
   (640, b32 (if validBit P L g d.block lane 1 then 2 else 0)),
   (641, b32 ((if validBit P L g d.block lane 1 then 2 else 0) |||
     (if validBit P L g d.block lane 0 then 1 else 0))),
   (642, b32 (ipat d.i1 / P.extraPage * (P.extraBlockStride / bytesPerToken) +
     ipat d.i1 % P.extraPage)),
   (643, b32 (coordValue P L g d.block lane 1)),
   (651, sb L (8 * lane + 256 * d.phase)), (652, sb L (8 * d.phase + lane / 4)),
   (653, sb L (readyOff d.phase)),
   (503, b32 (totalBlocks d.len0 d.len1)), (504, b32 numOrig),
   (3009, b64 (Thread.paramWord L 80 8)), (3010, b64 (Thread.paramWord L 144 8)),
   (3011, b64 (Thread.paramWord L 72 8)), (3012, b64 (Thread.paramWord L 136 8)),
   (3023, b64 ((Thread.paramWord L 80 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (3024, b64 (4 * ctaidY L g)),
   (3025, b64 ((Thread.paramWord L 144 8 + 4 * ctaidY L g) % 2 ^ 64)),
   (3026, b64 (4 * ctaidY L g)),
   (3013, b64 (idxRowOff P L g)), (3014, b64 (extraRowOff P L g)),
   (3033, b64 (pairAddr P L g 0)),
   (4029, b64 (pairAddr P L g (d.block + 1))),
   (3041, b64 (extraPairAddr P L g 0)),
   (3043, b64 (extraPairAddr P L g (d.block + 1 - numOrig))),
   (20, .pred (tidOf L g % 4 != 0)), (35, .pred (tidOf L g % 4 != 0)),
   (606, b32 (laneWord P L g d.block lane)), (645, b32 (laneWord P L g d.block lane)),
   (644, b32 (laneByte P L g d.block lane)),
   (608, b32 (quadWord P L g d.block lane)), (647, b32 (quadWord P L g d.block lane)),
   (609, b32 (pairWord P L g d.block lane)), (648, b32 (pairWord P L g d.block lane)),
   (508, b32 (validWord P L g d.block lane)), (511, b32 (validWord P L g d.block lane)),
   (2975, b32 npair1), (2976, b32 npair0), (2983, b32 epair1), (2984, b32 epair0),
   (659, b32 12), (660, b32 384)]

/-- The value of a register at state `d`: the table's, else the zero word. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  ((table P L g d).lookup r).getD (b32 0)

/-- The facts of state `d`: the live registers the role tracks, minus those a two-element load
has not written yet, with their table values. -/
def facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsFrom ((Flow.live d.site.pc).filter fun r =>
    tracked.contains r && !d.site.pendingRegs.contains r) (valueOf P L g d)

/-- A concrete state of an abstract state: at the site's program counter and sub-step, with the
site's facts and the site's accumulator. -/
def AtD (P : Params) (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = accOf d ∧ t.fault = none ∧
    Holds t.regs (facts P L g d)

/-! ## The successor relation -/

/-- The site after the pair load of the row's first block: the head of the body's first
iteration prefetches block 1 when it exists. -/
def afterPairFirst (d : D) (extra : Bool) : Site :=
  if !extra ∧ 1 < numOrigBlocks d.len0 then .pair false false false
  else if extra ∧ numOrigBlocks d.len0 + 1 < totalBlocks d.len0 d.len1 then
    .pair true false false
  else .waitFree extra

/-- The state after a body's arrival: the next block's pair, prefetched one iteration ahead, or
the body of the next block, or the next part of the row, or the final barrier. -/
def afterReady (d : D) : D :=
  let b := d.block
  let numOrig := numOrigBlocks d.len0
  let total := totalBlocks d.len0 d.len1
  let d' : D :=
    { d with
      phase := (d.phase + 1) % 4
      par := if d.phase == 3 then 1 - d.par else d.par
      block := b + 1
      i0 := d.n0
      i1 := d.n1 }
  let pre : D := { d' with site := .pair true true false, i0 := 0, i1 := 0 }
  if b + 1 < numOrig then
    (if b + 2 < numOrig then { d' with site := .pair false false false }
     else { d' with site := .waitFree false })
  else if b + 1 < total then
    -- the last main-cache block's row continues with the extra cache's first pair whenever the
    -- row has extra blocks (pcs 2495-2501); the extra loop's own head prefetches one block ahead
    (if b + 1 = numOrig then pre
     else if b + 2 < total then { d' with site := .pair true false false }
     else { d' with site := .waitFree true })
  else { d' with site := .barrier, block := b }

/-- The abstract successor after event `e`.

A length load continues only on the row's runtime length and an index load only on the row's
index at the slot's position (`Assumption.ncReadOnly` fixes their bytes to the launch content);
the two shuffles continue only on the value the partner lane's indices give. A poll continues to
the body on success and stays at the poll otherwise. The two stores continue on a shared write of
the ring slot's word count at the ring slot's address. -/
def nextSite (P : Params) (L : Launch) (g : Nat) : Site → D → Event → Option (Option D)
  | s, d, e =>
    match s with
    | .lenOrig =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.topkLen (eOf L g)) then
            some (some
              { d with
                site := if P.extraTopkLenBase.isSome then .lenExtra else .pair false true false
                len0 := P.topkLen (eOf L g)
                len1 := P.extraTopkLen (eOf L g) })
          else some none
        | .error _ => some none
      | _ => none
    | .lenExtra =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (P.extraTopkLen (eOf L g)) then
            some (some
              { d with
                site := .pair false true false
                len1 := P.extraTopkLen (eOf L g) })
          else some none
        | .error _ => some none
      | _ => none
    | .pair extra first hi =>
      match e.kind with
      | .nc _ bs =>
        match rebuild 3 bs with
        | .ok v =>
          if v = b32 (ipat (slotIdx P L g
              (if first then d.block else d.block + 1) (laneOf L g) (if hi then 1 else 0))) then
            some (some (if !hi then
              { d with
                site := .pair extra first true
                i0 := if first then slotIdx P L g d.block (laneOf L g) 0 else d.i0
                n0 := if first then d.n0
                  else slotIdx P L g (d.block + 1) (laneOf L g) 0 }
              else if first then
                { d with
                  site := afterPairFirst d extra
                  i1 := slotIdx P L g d.block (laneOf L g) 1 }
              else
                { d with
                  site := .waitFree extra
                  n1 := slotIdx P L g (d.block + 1) (laneOf L g) 1 }))
          else some none
        | .error _ => some none
      | _ => none
    | .waitFree extra =>
      match e.kind with
      | .wait _ _ ok _ _ => some (some (if ok then { d with site := .quad1 extra } else d))
      | _ => none
    | .quad1 extra =>
      match e.kind with
      | .shfl _ _ _ _ recv ok =>
        if ok = true ∧ recv = b32 (laneWord P L g d.block (laneOf L g ^^^ 1)) then
          some (some { d with site := .quad2 extra })
        else some none
      | _ => none
    | .quad2 extra =>
      match e.kind with
      | .shfl _ _ _ _ recv ok =>
        if ok = true ∧ recv = b32 (pairWord P L g d.block (laneOf L g ^^^ 2)) then
          some (some { d with site := .coord extra false })
        else some none
      | _ => none
    | .coord extra hi =>
      match e.kind with
      | .wr a _ =>
        if a.loc = ⟨.shared, ctaOf L g, L.sharedBase + coordOff L g d.phase + 4 * d.site.sub⟩ ∧
            a.size = 4 then
          some (some (if !hi then
            { d with site := .coord extra true }
            else if laneOf L g % 4 = 0 then { d with site := .valid extra }
            else { d with site := .ready extra }))
        else some none
      | _ => none
    | .valid extra =>
      match e.kind with
      | .wr a _ =>
        if a.loc = ⟨.shared, ctaOf L g, L.sharedBase + validOff L g d.phase⟩ ∧ a.size = 1 then
          some (some { d with site := .ready extra })
        else some none
      | _ => none
    | .ready _ =>
      match e.kind with
      | .arrive _ _ _ _ _ => some (some (afterReady d))
      | _ => none
    | .barrier =>
      match e.kind with
      | .bar _ _ _ => some none
      | _ => none

/-- The abstract successor after event `e`, at the state's site. -/
def next (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  nextSite P L g d.site d e

/-- The role's code machine. -/
def code (P : Params) (L : Launch) (g : Nat) : Code kernel asms L g where
  D := D
  init := init P L g
  pc := fun d => d.site.pc
  facts := facts P L g
  sub := fun d => d.site.sub
  acc := accOf
  inv := Inv P L g
  next := next P L g

/-- The pcs of the role's event instructions, in program order. -/
def eventPcs : List Nat :=
  [2360, 2365, 2403, 2429, 2446, 2464, 2467, 2471, 2474, 2476, 2501, 2517, 2534, 2553, 2556,
   2560, 2563, 2565, 2585]

/-- Every pc of `eventPcs` holds an unguarded event instruction. -/
theorem eventPcs_ok :
    eventPcs.all (fun pc => match codeAt pc with
      | some i => !i.op.isLocal && i.guard.isNone
      | none => false) = true := by
  decide +kernel

/-- A site's pc is one of the role's event pcs. -/
theorem mem_eventPcs (s : Site) : s.pc ∈ eventPcs := by
  cases s with
  | pair e f h => cases e <;> cases f <;> cases h <;> decide
  | coord e h => cases e <;> cases h <;> decide
  | waitFree e => cases e <;> decide
  | quad1 e => cases e <;> decide
  | quad2 e => cases e <;> decide
  | valid e => cases e <;> decide
  | ready e => cases e <;> decide
  | lenOrig => decide
  | lenExtra => decide
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
    refine ⟨ins, h, hok.1, ?_⟩
    rw [hok.2]
    trivial

/-! ## The arithmetic bridges to `Data/Indices` -/

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
the code's `(unsigned)idx / page * (stride / 528) + idx % page`
(`kernel.cuh:570-571,584`) is `rowOf` of the row's index in the block's cache geometry. -/
theorem rowBits_eq_rowOf {P : Params} {L : Launch} {mem0 : Mem0} {g b lane i : Nat}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (_hblk : b < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hv : validBit P L g b lane i = true) :
    rowBits P L g b lane i =
      rowOf (slotStride P L g b) (slotPg P L g b) (slotIdx P L g b lane i) := by
  have hpos := slotPos_lt_slotLen_of_kvSlotValid hv
  have hne : slotIdx P L g b lane i ≠ -1 := (kvSlotValid_eq_true_iff.mp hv).1
  have htopk := topkLen_le hpre hb
  have hextra := extraLen_le hpre hb
  by_cases he : isExtraBlock b (P.topkLen (eOf L g)) = true
  · have hidx : slotIdx P L g b lane i =
        P.extraIdx (eOf L g) (qOf L g) (slotPos (P.topkLen (eOf L g)) b lane i) := by
      simp only [slotIdx, slotIndex, he, ite_true]
    have hlen' : slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b =
        P.extraTopkLen (eOf L g) := by simp [slotLen, he]
    have hlt : slotPos (P.topkLen (eOf L g)) b lane i < P.extra_topk := by omega
    obtain ⟨h0, h1⟩ := hpre.extraIdxRange (eOf L g) hb (qOf L g) hq _
      (by exact ⟨hlen' ▸ hpos, hidx ▸ hne⟩)
    have hbnd : (P.extraIdx (eOf L g) (qOf L g)
        (slotPos (P.topkLen (eOf L g)) b lane i)).toNat < 2 ^ 32 := by
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
    have hidx : slotIdx P L g b lane i =
        P.idx (eOf L g) (qOf L g) (slotPos (P.topkLen (eOf L g)) b lane i) := by
      simp only [slotIdx, slotIndex, hf, Bool.false_eq_true, ite_false]
    have hlen' : slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b =
        P.topkLen (eOf L g) := by simp [slotLen, hf]
    have hlt : slotPos (P.topkLen (eOf L g)) b lane i < P.topk := by omega
    obtain ⟨h0, h1⟩ := hpre.idxRange (eOf L g) hb (qOf L g) hq _
      (by exact ⟨hlen' ▸ hpos, hidx ▸ hne⟩)
    have hbnd : (P.idx (eOf L g) (qOf L g)
        (slotPos (P.topkLen (eOf L g)) b lane i)).toNat < 2 ^ 32 := by
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

/-! ## The validity byte -/

/-- A lane's two validity bits are two bits. -/
theorem laneMask_le (P : Params) (L : Launch) (g b l : Nat) : laneMask P L g b l ≤ 3 := by
  unfold laneMask
  split_ifs <;> omega

/-- A lane's shifted mask is a byte. -/
theorem laneByte_lt (P : Params) (L : Launch) (g b l : Nat) : laneByte P L g b l < 256 := by
  unfold laneByte
  have h3 := laneMask_le P L g b l
  have hs : 2 ^ (2 * (l % 4)) ≤ 64 := by
    have : l % 4 < 4 := Nat.mod_lt _ (by decide)
    have : 2 * (l % 4) ≤ 6 := by omega
    calc 2 ^ (2 * (l % 4)) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) this
      _ = 64 := by decide
  nlinarith

/-- The quad's byte is a byte. -/
theorem quadByte_lt (P : Params) (L : Launch) (g b qb : Nat) : quadByte P L g b qb < 256 := by
  unfold quadByte
  have h1 : laneByte P L g b qb < 2 ^ 8 := by simpa using laneByte_lt P L g b qb
  have h2 : laneByte P L g b (qb + 1) < 2 ^ 8 := by simpa using laneByte_lt P L g b (qb + 1)
  have h3 : laneByte P L g b (qb + 2) < 2 ^ 8 := by simpa using laneByte_lt P L g b (qb + 2)
  have h4 : laneByte P L g b (qb + 3) < 2 ^ 8 := by simpa using laneByte_lt P L g b (qb + 3)
  have := Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3) h4
  simpa using this

/-! ## The entry interface and the role's soundness -/

/-- The prologue's hand-off to the role: a thread state at pc 2332 whose registers are the
prologue's values. `Proof/Thread/Prologue.lean` stops at the first event of warpgroup 1
(pc 1842) and has no hand-off to pc 2332, so this is the interface the role's start needs.

`warp` is the prologue's warp-index broadcast (`%r6 = %tid.x >> 5`, register 464); warp 7 is
this role. `regs` are the launch reads the prologue's table gives (`%r1 = %ctaid.x`,
`%r2 = %ctaid.y`, `%r3 = %tid.x`, `%r8 = lane`) and the `param_0` address (register 2991).
The role computes its own mbarrier addresses (`freeOff`, `readyOff`) from `wksp_buf`.
`batch` and `query` are the CTA's place in the kernel's `(s_q, b, 1)` grid: they are what makes
the row the role reads the CTA's own, which is `Proof/Thread/Coords.lean`'s business. -/
structure Entry (P : Params) (L : Launch) (g : Nat) (t : TState) : Prop where
  /-- The thread is at pc 2332, before its first `ld.param.b32`. -/
  pc : t.pc = 2332
  /-- The state is at an instruction boundary. -/
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  /-- The thread is warp 7 of warpgroup 1. -/
  warp : t.regs 464 = some (b32 7)
  /-- The prologue's launch reads and `param_0`'s address at the prologue's own values. -/
  regs : Holds t.regs (factsFrom [459, 460, 461, 466, 2991]
      (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g))
  /-- The CTA is a batch index of the grid. -/
  batch : ctaidY L g < P.b
  /-- The CTA is a query index of the grid. -/
  query : ctaidX L g < P.s_q

/-- The launch facts the role's first event depends on beyond `Entry`: the code tests the
length *words* for null (`setp.eq.b64`, pcs 2356 and 2361) and its exit test compares the two
batch words as signed 32-bit (`setp.ge.s32`, pc 2333), while `Entry` states the parameters'
`Option`s and the unsigned batch bound. They hold for a launch whose length pointers are the
runtime ones and whose batch count fits 32 signed bits; `Proof/Thread/Coords.lean` is where such
launch facts belong. -/
structure LaunchTest (P : Params) (L : Launch) (g : Nat) : Prop where
  /-- The main-cache length word is null exactly when the parameter has no runtime length. -/
  ptrOrig : Thread.ptrIsNull L 80 = !P.topkLenBase.isSome
  /-- The extra-cache length word is null exactly when the parameter has no runtime length. -/
  ptrExtra : Thread.ptrIsNull L 144 = !P.extraTopkLenBase.isSome
  /-- The role's exit test is false: a CTA of the grid stays in the role. -/
  noExit : Thread.geBatch L g = false

/-- The role's soundness from its entry: the entry state reaches the initial abstract state and
every abstract state's event continues to its successor. -/
structure Sound (P : Params) (L : Launch) (g : Nat) : Prop where
  /-- Local instructions from the prologue's entry facts reach the first site's state. -/
  start : ∀ (mem0 : Mem0) (t : TState), Pre P L mem0 → Entry P L g t → LaunchTest P L g →
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g)
  /-- Every site's event reaches its successor's state (`Code.StepAt`), or the role's end. -/
  steps : ∀ d, (code P L g).StepAt d

/-- **The site obligation of every state** — the `site` half of `Code.StepAt`: every state sits
at an unguarded event instruction. -/
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

/-- `firstSite` reads no cache before a length is loaded. -/
theorem firstSite_extra (P : Params) :
    (firstSite P).extra = none ∨ (firstSite P).extra = some false := by
  by_cases h : P.topkLenBase.isSome
  · simp [firstSite, h, Site.extra]
  · by_cases h2 : P.extraTopkLenBase.isSome <;> simp [firstSite, h, h2, Site.extra]

/-- No pair is loaded at `firstSite`. -/
theorem firstSite_hasPair (P : Params) : (firstSite P).hasPair = false := by
  by_cases h : P.topkLenBase.isSome
  · simp [firstSite, h, Site.hasPair]
  · by_cases h2 : P.extraTopkLenBase.isSome <;> simp [firstSite, h, h2, Site.hasPair]

/-- `firstSite` is not a body site. -/
theorem firstSite_inBody (P : Params) : (firstSite P).inBody = false := by
  by_cases h : P.topkLenBase.isSome
  · simp [firstSite, h, Site.inBody]
  · by_cases h2 : P.extraTopkLenBase.isSome <;> simp [firstSite, h, h2, Site.inBody]

/-- The initial state's site is the role's first site. -/
theorem init_site (P : Params) (L : Launch) (g : Nat) : (init P L g).site = firstSite P := rfl

/-- The initial state is not in the extra cache. -/
theorem init_extra_ne (P : Params) (L : Launch) (g : Nat) :
    (init P L g).site.extra ≠ some true := by
  rw [init_site]
  rcases firstSite_extra P with h | h <;> rw [h] <;> simp

/-- The initial state holds no pair. -/
theorem init_not_pair (P : Params) (L : Launch) (g : Nat) :
    (init P L g).site.hasPair = false := by
  rw [init_site]
  exact firstSite_hasPair P

/-- The initial state is not a body site. -/
theorem init_not_body (P : Params) (L : Launch) (g : Nat) :
    (init P L g).site.inBody = false := by
  rw [init_site]
  exact firstSite_inBody P

/-- The initial state satisfies the invariant. -/
theorem init_inv (P : Params) (L : Launch) (g : Nat) : Inv P L g (init P L g) := by
  have hpos : 0 < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) :=
    totalBlocks_pos _ _
  refine ⟨by simp [init], by simp [init], ?_, ?_, fun _ => rfl, rfl, rfl, hpos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rfl
  · intro _
    simp [init]
  · intro _
    exact numOrigBlocks_pos _
  · intro h
    exact absurd h (init_extra_ne P L g)
  · intro h
    rw [init_not_pair] at h
    exact absurd h (by simp)
  · intro h
    rw [init_not_pair] at h
    exact absurd h (by simp)
  · intro h
    rw [init_not_body] at h
    exact absurd h (by simp)
  · intro h
    rw [init_not_body] at h
    exact absurd h (by simp)
  · intro _
    simp [init]
  · unfold pairInvariant
    rw [init_site]
    by_cases h0 : P.topkLenBase.isSome
    · simp [firstSite, h0]
    · by_cases h1 : P.extraTopkLenBase.isSome <;> simp [firstSite, h0, h1]

/-- `isExtraBlock b len = false` exactly for the main cache's blocks. -/
theorem isExtraBlock_false_iff {len b : Nat} :
    isExtraBlock b len = false ↔ b < numOrigBlocks len := by
  unfold isExtraBlock
  rw [decide_eq_false_iff_not]
  omega

/-- The arrival's ring slot: the next block's position. -/
theorem afterReady_phase_val {b phase : Nat} (hp : phase = b % 4) :
    (phase + 1) % 4 = (b + 1) % 4 := by
  subst hp
  have := Nat.mod_lt b (by decide : 0 < 4)
  omega

/-- The arrival's parity: it flips exactly when the ring slot wraps, which is when the block's
quarter changes. -/
theorem afterReady_par_val {b phase par : Nat} (hp : phase = b % 4) (hpar : par = b / 4 % 2)
    (_hpar2 : par < 2) :
    (if phase == 3 then 1 - par else par) = (b + 1) / 4 % 2 := by
  subst hp
  have hm := Nat.mod_lt b (by decide : 0 < 4)
  by_cases h3 : b % 4 = 3
  · rw [ite_eq_left (by simp [h3])]
    have hq : (b + 1) / 4 = b / 4 + 1 := by omega
    rw [hq, hpar]
    omega
  · rw [ite_eq_right (by simp [h3])]
    have hq : (b + 1) / 4 = b / 4 := by omega
    rw [hq, hpar]

/-- **The main-cache body's prefetch pair**: a `.ready false` state prefetches the next block
when the row has one. -/
theorem ready_pref_main {P : Params} {L : Launch} {g : Nat} {d : D}
    (h : Inv P L g d) (hd : d.site = .ready false)
    (hc : d.block + 1 < numOrigBlocks d.len0) :
    d.n0 = slotIdx P L g (d.block + 1) (laneOf L g) 0 ∧
      d.n1 = slotIdx P L g (d.block + 1) (laneOf L g) 1 := by
  have hinb : d.site.inBody = true := by rw [hd]; rfl
  have h0 := h.pref0 hinb
  have h1' := h.pref1 hinb
  rw [hd] at h0 h1'
  exact ⟨h0 hc, h1' hc⟩

/-- **The extra-cache body's prefetch pair**: a `.ready true` state prefetches the next block
when the row has one. -/
theorem ready_pref_extra {P : Params} {L : Launch} {g : Nat} {d : D}
    (h : Inv P L g d) (hd : d.site = .ready true)
    (hc : d.block + 1 < totalBlocks d.len0 d.len1) :
    d.n0 = slotIdx P L g (d.block + 1) (laneOf L g) 0 ∧
      d.n1 = slotIdx P L g (d.block + 1) (laneOf L g) 1 := by
  have hinb : d.site.inBody = true := by rw [hd]; rfl
  have h0 := h.pref0 hinb
  have h1' := h.pref1 hinb
  rw [hd] at h0 h1'
  exact ⟨h0 hc, h1' hc⟩

/-- **The arrival's hand-off preserves the loop invariant.** The body's last site is a
`.ready` state; `afterReady` advances the ring, the block and the index pair, and chooses one
of the loop's branch targets: the next block's prefetch, the body of the next block, the extra
cache's pre-load, the extra cache's body, or the final barrier. The two helpers
`ready_pref_main` and `ready_pref_extra` give the prefetched pair in the branches that use it. -/
theorem afterReady_inv {P : Params} {L : Launch} {g : Nat} {d : D} {extra : Bool}
    (hd : d.site = .ready extra) (h : Inv P L g d) :
    Inv P L g (afterReady d) := by
  have hne : d.site ≠ .barrier := by rw [hd]; intro hc; cases hc
  have hphase := h.phase_block hne
  have hpar := h.par_block hne
  have hphase_lt : (d.phase + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hpar_lt : (if d.phase == 3 then 1 - d.par else d.par) < 2 := by
    by_cases h3 : d.phase = 3
    · rw [ite_eq_left (by simp [h3])]; omega
    · rw [ite_eq_right (by simp [h3])]; omega
  have hphase' : (d.phase + 1) % 4 = (d.block + 1) % 4 :=
    afterReady_phase_val hphase
  have hpar' : (if d.phase == 3 then 1 - d.par else d.par) = (d.block + 1) / 4 % 2 :=
    afterReady_par_val hphase hpar h.par
  have hnumLe : numOrigBlocks d.len0 ≤ totalBlocks d.len0 d.len1 :=
    numOrigBlocks_le_totalBlocks _ _
  by_cases h1 : d.block + 1 < numOrigBlocks d.len0
  · have hw : extra = false := by
      cases extra
      · rfl
      · have ht := h.tagExtra (show d.site.extra = some true by rw [hd]; rfl)
        omega
    obtain ⟨hslot0, hslot1⟩ := ready_pref_main h (by rw [hd, hw]) h1
    by_cases h2 : d.block + 2 < numOrigBlocks d.len0
    · have ht : afterReady d =
          { d with
            phase := (d.phase + 1) % 4
            par := if d.phase == 3 then 1 - d.par else d.par
            block := d.block + 1
            i0 := d.n0
            i1 := d.n1
            site := .pair false false false } := by
        simp only [afterReady, ite_eq_left h1, ite_eq_left h2]
      rw [ht]
      exact ⟨hphase_lt, hpar_lt, fun _ => hphase', fun _ => hpar',
        (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1,
        lt_of_lt_of_le h1 hnumLe, fun _ => h1, (by intro he; cases he),
        fun _ => hslot0, fun _ => hslot1,
        (by intro hh; cases hh),
        (by intro hh; cases hh),
        (by intro hh; rcases hh with h | h <;> cases h), ⟨h2, trivial⟩⟩
    · have ht : afterReady d =
          { d with
            phase := (d.phase + 1) % 4
            par := if d.phase == 3 then 1 - d.par else d.par
            block := d.block + 1
            i0 := d.n0
            i1 := d.n1
            site := .waitFree false } := by
        simp only [afterReady, ite_eq_left h1, ite_eq_right h2]
      rw [ht]
      exact ⟨hphase_lt, hpar_lt, fun _ => hphase', fun _ => hpar',
        (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1,
        lt_of_lt_of_le h1 hnumLe, fun _ => h1, (by intro he; cases he),
        fun _ => hslot0, fun _ => hslot1,
        fun _ hc => False.elim (h2 hc), fun _ hc => False.elim (h2 hc),
        (by intro hh; rcases hh with h | h <;> cases h), trivial⟩
  · by_cases h2 : d.block + 1 < totalBlocks d.len0 d.len1
    · by_cases h3 : d.block + 1 = numOrigBlocks d.len0
      · have ht : afterReady d =
            { d with
              phase := (d.phase + 1) % 4
              par := if d.phase == 3 then 1 - d.par else d.par
              block := d.block + 1
              i0 := 0
              i1 := 0
              site := .pair true true false } := by
          simp only [afterReady, ite_eq_right h1, ite_eq_left h2, ite_eq_left h3]
        rw [ht]
        exact ⟨hphase_lt, hpar_lt, fun _ => hphase', fun _ => hpar',
          (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1, h2,
          (by intro he; cases he), fun _ => by rw [← h3],
          (by intro hh; cases hh),
          (by intro hh; cases hh),
          (by intro hh; cases hh),
          (by intro hh; cases hh),
        (by intro hh; rcases hh with h | h <;> cases h), ⟨h3, trivial⟩⟩
      · have hw : extra = true := by
          cases extra
          · have ht := h.tagMain (show d.site.extra = some false by rw [hd]; rfl)
            omega
          · rfl
        obtain ⟨hslot0, hslot1⟩ := ready_pref_extra h (by rw [hd, hw]) h2
        by_cases h4 : d.block + 2 < totalBlocks d.len0 d.len1
        · have ht : afterReady d =
              { d with
                phase := (d.phase + 1) % 4
                par := if d.phase == 3 then 1 - d.par else d.par
                block := d.block + 1
                i0 := d.n0
                i1 := d.n1
                site := .pair true false false } := by
            simp only [afterReady, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3, ite_eq_left h4]
          rw [ht]
          exact ⟨hphase_lt, hpar_lt, fun _ => hphase', fun _ => hpar',
            (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1, h2,
            (by intro he; cases he), fun _ => Nat.not_lt.mp h1,
            fun _ => hslot0, fun _ => hslot1,
            (by intro hh; cases hh),
            (by intro hh; cases hh),
        (by intro hh; rcases hh with h | h <;> cases h), ⟨h4, trivial⟩⟩
        · have ht : afterReady d =
              { d with
                phase := (d.phase + 1) % 4
                par := if d.phase == 3 then 1 - d.par else d.par
                block := d.block + 1
                i0 := d.n0
                i1 := d.n1
                site := .waitFree true } := by
            simp only [afterReady, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3,
              ite_eq_right h4]
          rw [ht]
          exact ⟨hphase_lt, hpar_lt, fun _ => hphase', fun _ => hpar',
            (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1, h2,
            (by intro he; cases he), fun _ => Nat.not_lt.mp h1,
            fun _ => hslot0, fun _ => hslot1,
            fun _ hc => False.elim (h4 hc), fun _ hc => False.elim (h4 hc),
            (by intro hh; rcases hh with h | h <;> cases h), trivial⟩
    · have ht : afterReady d =
          { d with
            phase := (d.phase + 1) % 4
            par := if d.phase == 3 then 1 - d.par else d.par
            block := d.block
            i0 := d.n0
            i1 := d.n1
            site := .barrier } := by
        simp only [afterReady, ite_eq_right h1, ite_eq_right h2]
      rw [ht]
      exact ⟨hphase_lt, hpar_lt, fun hc => False.elim (hc rfl), fun hc => False.elim (hc rfl),
        (by intro hc; rcases hc with h | h <;> cases h), h.len0, h.len1, h.block,
        (by intro he; cases he), (by intro he; cases he),
        (by intro hh; cases hh),
        (by intro hh; cases hh),
        (by intro hh; cases hh),
        (by intro hh; cases hh),
        (by intro hh; rcases hh with h | h <;> cases h), trivial⟩

/-! ## The entry run

The local prefix of the role (pcs 2332-2359) is the row's parameter loads and index-offset
arithmetic, the `%ctaid.y >= b` exit test (false for a CTA of the grid) and the
`topk_length_ptr == 0` test. Its end state is the initial abstract state of the machine. -/

/-- The prefix state: `init` with the two length registers still holding the parameters'
constants (the runtime lengths are what the first site's loads return). -/
def preD (P : Params) (L : Launch) (g : Nat) : D :=
  { init P L g with len0 := P.topk, len1 := P.extra_topk }

/-- The registers live at `pc` that the role tracks, minus those a pending load has not
written. -/
def liveAt (pc : Nat) (pen : List Nat) : List Nat :=
  (Flow.live pc).filter fun r => tracked.contains r && !pen.contains r

/-- The tracked registers live at `pc`. -/
def preLive (pc : Nat) : List Nat := (Flow.live pc).filter tracked.contains

/-- The facts of the entry prefix at `pc`: the tracked live registers, at the prefix table's
values. -/
def preFacts (P : Params) (L : Launch) (g : Nat) (pc : Nat) : List (Nat × Value) :=
  factsFrom (preLive pc) (valueOf P L g (preD P L g))

/-- The facts of state `d` at an arbitrary program counter. -/
def atFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) : List (Nat × Value) :=
  factsFrom (liveAt pc d.site.pendingRegs) (valueOf P L g d)

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "idx_values" : tactic =>
  `(tactic| simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some])

/-- The table's values with further definitions unfolded, for an equality of two table
values. -/
syntax "idx_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| idx_simp $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some, $extra,*])

/-- Idempotence of the 64-bit truncation. -/
theorem mod64_idem (a : Nat) : a % 18446744073709551616 % 18446744073709551616 =
    a % 18446744073709551616 := Nat.mod_mod_of_dvd a (dvd_refl 18446744073709551616)

/-- Idempotence of the 32-bit truncation. -/
theorem mod32_idem (a : Nat) : a % 4294967296 % 4294967296 = a % 4294967296 :=
  Nat.mod_mod_of_dvd a (dvd_refl 4294967296)

/-- A 32-bit truncation survives the 64-bit one. -/
theorem mod32_mod64 (a : Nat) : a % 4294967296 % 18446744073709551616 = a % 4294967296 :=
  Nat.mod_eq_of_lt (by have := Nat.mod_lt a (by decide : 0 < 4294967296); omega)

/-- A 64-bit truncation is a 32-bit one after the 32-bit truncation. -/
theorem mod64_mod32 (a : Nat) : a % 18446744073709551616 % 4294967296 = a % 4294967296 :=
  Nat.mod_mod_of_dvd a (by decide)

/-- A 32-bit product of truncated factors is the truncation of the product. -/
theorem mul_mod_combine32 (a b : Nat) :
    a % 4294967296 * (b % 4294967296) % 4294967296 = a * b % 4294967296 := by
  conv_rhs => rw [Nat.mul_mod]

/-- Evaluate a segment of index arithmetic: the table's stated values, the integer normal form,
the truncations of products, and linear arithmetic over the launch's bounded coordinates. -/
syntax "idx_bits" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| idx_bits $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      (try idx_values)
      (try nf_simp [$extra,*])
      (try simp only [mul_mod_combine32, mod32_idem, mod32_mod64, mod64_mod32, mod64_idem,
        pairAddr, extraPairAddr, ctaidY, $extra,*])
      try omega))

/-- Adding the table-value fact of one written register, at the next instruction. -/
theorem at_set_table {t t' : TState} {pc d : Nat} {val : Nat → Value} {live live' : List Nat}
    {F : List (Nat × Value)}
    (h : At t pc F) (hpc : t'.pc = pc + 1) (hsub : t'.sub = t.sub) (hacc : t'.acc = t.acc)
    (hf : t'.fault = t.fault)
    (hd : t'.regs d = some (val d)) (hfr : ∀ x, x ≠ d → t'.regs x = t.regs x)
    (hF : ∀ x ∈ live, (x, val x) ∈ F)
    (hl : ∀ x ∈ live', x ∈ d :: live) :
    At t' (pc + 1) (factsFrom live' val) := by
  refine ⟨hpc, hsub.trans h.2.1, hacc.trans h.2.2.1, hf.trans h.2.2.2.1, ?_⟩
  refine holds_of_pointwise fun x hx => ?_
  by_cases hxd : x = d
  · rw [hxd]; exact hd
  · rw [hfr x hxd]
    rcases List.mem_cons.mp (hl x hx) with hxl | hxl
    · exact absurd hxl hxd
    · exact holds_mem h.2.2.2.2 (hF x hxl)

/-- Dropping a fact and keeping the rest of a table. -/
theorem at_of_cons {t : TState} {pc r : Nat} {v : Value} {live live' : List Nat}
    {val : Nat → Value} (h : At t pc ((r, v) :: factsFrom live val))
    (hsub : ∀ x ∈ live', x ∈ live) : At t pc (factsFrom live' val) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, holds_factsFrom_mono h.2.2.2.2.2 hsub⟩

/-- An `ld.param` of one register of `param_0` through the pointer register 2991, from any
fact list that holds the table's values on `live`, reaching the next instruction's table. -/
theorem ld_obj_at {P : Params} {L : Launch} {g : Nat} {t : TState} {pc w off d r : Nat}
    {ty : DType} {F : List (Nat × Value)} {live live' : List Nat} {val : Nat → Value}
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off r d)⟩)
    (hrp : t.regs r = some (.ptr 64 false (.param (param "0")) 0))
    (hobj : L.paramObjects (param "0") = some (scalarsParam, P.param0Base))
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h : At t pc F)
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = val d)
    (hF : ∀ x ∈ live, (x, val x) ∈ F)
    (hl : ∀ x ∈ live', x ∈ d :: live)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc)
    (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off r d).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (factsFrom live' val) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (Thread.paramLoad ty off r d)) = none := by
    intro b hb
    exact Thread.asms_localRule_mem (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) b hb
  refine ⟨PTX.next (setReg t d (paramElem w w (paramNat L (param "0") off (w / 8)))),
    run_local hc rfl h (Thread.exec_ldParamReg hrp hobj ⟨by omega, hsze⟩ hal hsup
      (Assumption.SegFreePc.of_eq h.1 hsf) hL hw hr), ?_⟩
  refine at_set_table (pc := pc) (d := d) (val := val) (live := live) (live' := live') h
    (by simp [PTX.next, setReg, h.1]) rfl rfl rfl ?_ ?_ hF hl
  · simp [PTX.next, setReg, hv]
  · intro x hx
    simp [PTX.next, setReg, Function.update_of_ne hx]

/-- Adding the table-value facts of two written registers, at the next instruction. -/
theorem at_set2_table {t t' : TState} {pc d0 d1 : Nat} {val : Nat → Value}
    {live live' : List Nat} {F : List (Nat × Value)}
    (h : At t pc F) (hpc : t'.pc = pc + 1) (hsub : t'.sub = t.sub) (hacc : t'.acc = t.acc)
    (hf : t'.fault = t.fault)
    (hd0 : t'.regs d0 = some (val d0)) (hd1 : t'.regs d1 = some (val d1))
    (hfr : ∀ x, x ≠ d0 → x ≠ d1 → t'.regs x = t.regs x)
    (hF : ∀ x ∈ live, (x, val x) ∈ F)
    (hl : ∀ x ∈ live', x ∈ d0 :: d1 :: live) :
    At t' (pc + 1) (factsFrom live' val) := by
  refine ⟨hpc, hsub.trans h.2.1, hacc.trans h.2.2.1, hf.trans h.2.2.2.1, ?_⟩
  refine holds_of_pointwise fun x hx => ?_
  by_cases hx0 : x = d0
  · rw [hx0]; exact hd0
  · by_cases hx1 : x = d1
    · rw [hx1]; exact hd1
    · rw [hfr x hx0 hx1]
      rcases List.mem_cons.mp (hl x hx) with h0 | h'
      · exact absurd h0 hx0
      · rcases List.mem_cons.mp h' with h1 | h'
        · exact absurd h1 hx1
        · exact holds_mem h.2.2.2.2 (hF x h')

/-- A guarded branch on a fact of an arbitrary fact list, taken or not. -/
theorem bra_at {t : TState} {pc target p : Nat} {pick : Bool} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc F) (hp : (p, .pred pick) ∈ F)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (if pick then target else pc + 1) F := by
  refine run_bra hc pick h (holds_mem h.2.2.2.2 hp) ?_ hsf
  intro a ha
  exact Thread.asms_localRule_bra (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha

/-! ### The entry prefix -/

/-- The entry state's facts at pc 2332. -/
theorem entry_atFacts (P : Params) (L : Launch) (g : Nat) {t : TState}
    (hentry : Entry P L g t) : At t 2332 (preFacts P L g 2332) := by
  have hlive : preLive 2332 = [459, 460, 461, 466, 2991] := by decide +kernel
  have hv : ∀ r ∈ [459, 460, 461, 466, 2991],
      t.regs r = some (valueOf P L g (preD P L g) r) := by
    intro r hr
    have hm : t.regs r = some (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g r) :=
      holds_mem hentry.regs (mem_factsFrom
        (val := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g) hr)
    simp only [_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
      _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simpa [valueOf, table, preD, init, PTX.Flow.lookupLit] using hm
  refine ⟨hentry.pc, hentry.sub, hentry.acc, hentry.fault, ?_⟩
  rw [preFacts, hlive]
  exact ⟨hv 459 (by simp), hv 460 (by simp), hv 461 (by simp), hv 466 (by simp),
    hv 2991 (by simp), trivial⟩

/-- The idle role's exit test, at the role's own launch coordinates. -/
theorem thread_geBatch_eq (L : Launch) (g : Nat) :
    Thread.geBatch L g =
      compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (ctaidY L g)))
        (truncBits 32 (BitVec.ofNat 64 (Thread.paramWord L 0 4))) := by
  simp [Thread.geBatch, Thread.ctaidY, Thread.ctaOf, ctaidY, ctaOf]

section
variable {P : Params} {L : Launch}

/-- The parameter's main-cache length constant, as the entry prefix loads it. -/
theorem paramElem_topk {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramElem 32 32 (paramNat L (param "0") 40 4) = b32 P.topk := by
  have h := Thread.paramWord_four (L := L) (off := 40) (x := P.topk)
    (fun k hk => hpre.paramTopk k hk)
  simp only [Thread.paramWord] at h
  have hlt : P.topk < 2 ^ 32 := by have := hpre.topkAdd63Lt; omega
  rw [paramElem_of_ne (by decide), h, Nat.mod_eq_of_lt hlt]
  rfl

/-- The parameter's extra-cache length constant, as the entry prefix loads it. -/
theorem paramElem_extraTopk {mem0 : Mem0} (hpre : Pre P L mem0) :
    paramElem 32 32 (paramNat L (param "0") 120 4) = b32 P.extra_topk := by
  have h := Thread.paramWord_four (L := L) (off := 120) (x := P.extra_topk)
    (fun k hk => hpre.paramExtraTopk k hk)
  simp only [Thread.paramWord] at h
  have hlt : P.extra_topk < 2 ^ 32 := by have := hpre.extraTopkAdd63Lt; omega
  rw [paramElem_of_ne (by decide), h, Nat.mod_eq_of_lt hlt]
  rfl

/-- An `ld.param` of one register of `param_0` through the pointer register 2991, from the
prefix facts, reaching the next instruction's prefix facts. -/
theorem pre_obj_at {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {pc w off d : Nat}
    {ty : DType} (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off 2991 d)⟩)
    (h : At t pc (preFacts P L g pc)) (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsze : off + w / 8 ≤ 304) (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g (preD P L g) d)
    (hmem : (2991 : Nat) ∈ preLive pc) (hl : ∀ x ∈ preLive (pc + 1), x ∈ d :: preLive pc)
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites) (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off 2991 d).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (preFacts P L g (pc + 1)) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g (preD P L g))
      (r := 2991) hmem)
    simpa [preFacts, valueOf, table, preD, init, PTX.Flow.lookupLit, Option.getD_some] using hm
  exact ld_obj_at (P := P) (L := L) (g := g) (pc := pc) (w := w) (off := off) (d := d)
    (r := 2991) (ty := ty) (live := preLive pc) (live' := preLive (pc + 1))
    (val := valueOf P L g (preD P L g)) hc h2991 hpre.param0Object hsup hsze hal h hv
    (fun x hx => mem_factsFrom hx) hl (hsf := by seg_free_pc) h1 h2 hw hr
end

/-- Two-element `ld.param` of `param_0` through the pointer register 2991: `d0` receives the
first element, `d1` the second. -/
theorem exec_ldParamReg2 {A : List Assumption} {L : Launch} {g w off r d0 d1 : Nat}
    {t : TState} {p : String} {ty : DType} {decl : ParamObjectDecl} {base : Nat}
    (hrp : t.regs r = some (.ptr 64 false (.param p) 0))
    (hobj : L.paramObjects p = some (decl, base))
    (hbound : 0 ≤ (off : Int) ∧ off + w / 8 * 2 ≤ decl.bytes)
    (halign : 0 < w / 8 * 2 ∧ off % (w / 8 * 2) = 0 ∧ decl.alignment % (w / 8 * 2) = 0)
    (hsup : ParamSupplied L p off (w / 8 * 2))
    (hA : Assumption.SegFreePc A t.pc := by seg_free)
    (hL : ∀ b ∈ A, b.localRule L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg r 64, (off : Int)⟩, dsts := [some d0, some d1] }) = none)
    (hw : ty.width = w := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg r 64, (off : Int)⟩, dsts := [some d0, some d1] } =
      some .threadMove := by rfl) :
    execLocalA A L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg r 64, (off : Int)⟩, dsts := [some d0, some d1] }) =
      .ok (PTX.next (loadParamRegs L w w p t off [d0, d1])) := by
  subst hw
  have ho : (off : Int).toNat = off := Int.toNat_natCast off
  have hpo : paramObjectOf L t r (off : Int) (ty.width / 8 * 2) = .ok p :=
    Thread.paramObjectOf_ok hrp hobj hbound.1 (by simpa using hbound.2)
      (by simpa using halign.1) (by simpa using halign.2.1) (by simpa using halign.2.2)
  have hsup' : ParamSupplied L p off (ty.width / 8 * [d0, d1].length) := by simpa using hsup
  have hregs : ([some d0, some d1].filterMap id) = [d0, d1] := rfl
  rw [hA.exec rfl, execLocalRule_of_none hL, execLocal_mem hr]
  simp only [execMove, MemAccess.regs, hregs, hpo, bind, Except.bind, ho]
  rw [loadParamObject_eq (ds := [d0, d1]) (t := t) (off := off) hsup']
  rfl

section
variable {P : Params} {L : Launch} {g : Nat}

/-- A two-element `ld.param` of `param_0` through register 2991, from the prefix facts. -/
theorem pre_obj2_at {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {pc w off d0 d1 : Nat}
    {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg 2991 64, (off : Int)⟩, dsts := [some d0, some d1] }⟩)
    (h : At t pc (preFacts P L g pc)) (hsup : ParamSupplied L (param "0") off (w / 8 * 2))
    (hsze : off + w / 8 * 2 ≤ 304)
    (hal : 0 < w / 8 * 2 ∧ off % (w / 8 * 2) = 0 ∧ (8 : Nat) % (w / 8 * 2) = 0)
    (hv0 : paramElem w w (paramNat L (param "0") off (w / 8)) = valueOf P L g (preD P L g) d0)
    (hv1 : paramElem w w (paramNat L (param "0") (off + w / 8) (w / 8)) =
      valueOf P L g (preD P L g) d1) (hne : d0 ≠ d1) (hmem : (2991 : Nat) ∈ preLive pc)
    (hl : ∀ x ∈ preLive (pc + 1), x ∈ d0 :: d1 :: preLive pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (hw : ty.width = w := by rfl)
    (hr : MemAccess.rule
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg 2991 64, (off : Int)⟩, dsts := [some d0, some d1] } =
      some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (preFacts P L g (pc + 1)) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g (preD P L g))
      (r := 2991) hmem)
    simpa [preFacts, valueOf, table, preD, init, PTX.Flow.lookupLit, Option.getD_some] using hm
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem
      { kind := .load, space := some .param, sem := .weak, elem := ty, vec := 2, ext := .same,
        addr := ⟨.reg 2991 64, (off : Int)⟩, dsts := [some d0, some d1] }) = none := by
    intro b hb
    exact Thread.asms_localRule_mem (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) b hb
  refine ⟨PTX.next (loadParamRegs L w w (param "0") t off [d0, d1]),
    run_local hc rfl h (exec_ldParamReg2 h2991 hpre.param0Object ⟨by omega, hsze⟩ hal hsup
      (Assumption.SegFreePc.of_eq h.1 (by seg_free_pc)) hL hw hr), ?_⟩
  refine at_set2_table (pc := pc) (d0 := d0) (d1 := d1) (val := valueOf P L g (preD P L g))
    (live := preLive pc) (live' := preLive (pc + 1)) h
    (by show t.pc + 1 = pc + 1; rw [h.1]) rfl rfl rfl ?_ ?_ ?_
    (fun x hx => mem_factsFrom hx) hl
  · simp only [loadParamRegs, PTX.next, setReg]
    rw [Function.update_of_ne hne, Function.update_self, hv0]
  · simp only [loadParamRegs, PTX.next, setReg]
    rw [Function.update_self, hv1]
  · intro x hx0 hx1
    simp only [loadParamRegs, PTX.next, setReg]
    rw [Function.update_of_ne hx1, Function.update_of_ne hx0]

/-- A masked value keeps only its low bits: `a &&& b = (a % 2 ^ k) &&& b` for `b < 2 ^ k`. -/
theorem and_mod_two_pow (a b k : Nat) (hb : b < 2 ^ k) :
    a &&& b = (a % 2 ^ k) &&& b := by
  calc a &&& b = a &&& ((2 ^ k - 1) &&& b) := by
        rw [Nat.and_comm (2 ^ k - 1) b, Nat.and_two_pow_sub_one_of_lt_two_pow hb]
    _ = (a &&& (2 ^ k - 1)) &&& b := (Nat.and_assoc a (2 ^ k - 1) b).symm
    _ = (a % 2 ^ k) &&& b := by rw [Nat.and_two_pow_sub_one_eq_mod]

/-- The low two bits of `2 * t`, masked by six: `(2 t) &&& 6 = 2 (t % 4)`. -/
theorem land6_two_mul (t : Nat) : 2 * t &&& 6 = 2 * (t % 4) := by
  have hb : 6 < 2 ^ 3 := by decide
  rw [and_mod_two_pow (2 * t) 6 3 hb, show (2 : Nat) ^ 3 = 8 from by decide]
  have h2 : 2 * t % 8 = 2 * (t % 4) := by omega
  rw [h2]
  have h := Nat.mod_lt t (by decide : 0 < 4)
  interval_cases t % 4 <;> decide

/-- Two adjacent integer fields supply eight bytes. -/
theorem supplied_two {L : Launch} {off x y : Nat}
    (h1 : ∀ k < 4, L.paramBytes (param "0") (off + k) = some (leByte x k))
    (h2 : ∀ k < 4, L.paramBytes (param "0") (off + 4 + k) = some (leByte y k)) :
    ParamSupplied L (param "0") off 8 := by
  intro k hk
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · exact ⟨_, h1 k hk4⟩
  · have hk' : k - 4 < 4 := by omega
    exact ⟨leByte y (k - 4), by
      rw [show off + k = off + 4 + (k - 4) by omega]
      exact h2 (k - 4) hk'⟩

/-- The same mask with the doubling written on the right. -/
theorem land6_mul_comm (t : Nat) : t * 2 &&& 6 = 2 * (t % 4) := by
  rw [Nat.mul_comm t 2, land6_two_mul]

/-- A mask of three reads the same bits through a 32-bit truncation, as a four-way modulus. -/
theorem and3_mod32 (a : Nat) : a % 4294967296 &&& 3 = a % 4 := by
  calc a % 4294967296 &&& 3 = a &&& 3 := (and_mod_two_pow a 3 32 (by decide)).symm
    _ = a % 4 := by simpa using Nat.and_two_pow_sub_one_eq_mod a 2

/-- A 32-bit truncation does not change the low two bits. -/
theorem mod32_mod4 (a : Nat) : a % 4294967296 % 4 = a % 4 :=
  Nat.mod_mod_of_dvd a (by decide)

/-- A mask of six reads the same bits through a 32-bit truncation. -/
theorem and6_mod32 (a : Nat) : a % 4294967296 &&& 6 = a &&& 6 :=
  (and_mod_two_pow a 6 32 (by decide)).symm

/-- **The common entry prefix**: the parameter loads and index-offset arithmetic from the
first length load to the null test of the main-cache length pointer (pc 2357). -/
theorem entry_prefix (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) {t : TState} (h : At t 2335 (preFacts P L g 2335)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2357 ((15, .pred (Thread.ptrIsNull L 80)) :: preFacts P L g 2357) := by
  obtain ⟨t1, r1, h1⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2335) (w := 32) (off := 164) (d := 490) (ty := .int .b 32) Flow.code_2335
    h (fun k hk => ⟨_, hpre.paramStrideKvBlock k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t2, r2, h2⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2336) (w := 32) (off := 200) (d := 491) (ty := .int .b 32) Flow.code_2336
    h1 (fun k hk => ⟨_, hpre.paramStrideExtraKvBlock k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t3, r3, h3⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2337) (w := 64) (off := 80) (d := 3009) (ty := .int .b 64) Flow.code_2337
    h2 (Thread.supplied_topk hpre) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t4, r4, h4⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2338) (w := 32) (off := 40) (d := 2968) (ty := .int .b 32) Flow.code_2338
    h3 (fun k hk => ⟨_, hpre.paramTopk k hk⟩) (by decide) (by decide)
    (by rw [paramElem_topk hpre]; idx_values; rfl) (by decide +kernel) (by lit_mem)
    (by decide) (by decide)
  obtain ⟨t5, r5, h5⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2339) (w := 64) (off := 144) (d := 3010) (ty := .int .b 64) Flow.code_2339
    h4 (Thread.supplied_extra hpre) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t6, r6, h6⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2340) (w := 32) (off := 120) (d := 2969) (ty := .int .b 32) Flow.code_2340
    h5 (fun k hk => ⟨_, hpre.paramExtraTopk k hk⟩) (by decide) (by decide)
    (by rw [paramElem_extraTopk hpre]
        idx_values
        simp only [preD, init]
        cases firstSite P <;> simp [len1Reg]) (by decide +kernel) (by lit_mem)
    (by decide) (by decide)
  obtain ⟨t7, r7, h7⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2341) (w := 64) (off := 72) (d := 3011) (ty := .int .b 64) Flow.code_2341
    h6 (fun k hk => ⟨_, hpre.paramIndices k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t8, r8, h8⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2342) (w := 32) (off := 172) (d := 492) (ty := .int .b 32) Flow.code_2342
    h7 (fun k hk => ⟨_, hpre.paramStrideIndicesB k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨t9, r9, h9⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2343) (w := 32) (off := 176) (d := 560) (ty := .int .b 32) Flow.code_2343
    h8 (fun k hk => ⟨_, hpre.paramStrideIndicesSq k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨ta, ra, ha⟩ : ∃ t', run kernel asms L g 1 t9 = some t' ∧
      At t' 2345 (preFacts P L g 2345) := by
    seg_fp h9 using idx_bits
  obtain ⟨tb, rb, hb⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2345) (w := 64) (off := 136) (d := 3012) (ty := .int .b 64) Flow.code_2345
    ha (fun k hk => ⟨_, hpre.paramExtraIndices k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨tc, rc, hc⟩ := pre_obj2_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2346) (w := 32) (off := 208) (d0 := 494) (d1 := 561) (ty := .int .b 32)
    Flow.code_2346 hb (supplied_two hpre.paramStrideExtraIndicesB hpre.paramStrideExtraIndicesSq)
    (by decide) (by decide) (by idx_values; rfl) (by idx_values; rfl) (by decide)
    (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨td, rd, hd⟩ : ∃ t', run kernel asms L g 1 tc = some t' ∧
      At t' 2348 (preFacts P L g 2348) := by
    seg_fp hc using idx_bits
  obtain ⟨te, re, he⟩ : ∃ t', run kernel asms L g 1 td = some t' ∧
      At t' 2349 (preFacts P L g 2349) := by
    seg_fp hd using idx_bits [laneOf]
  obtain ⟨tf, rf, hf⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2349) (w := 32) (off := 36) (d := 497) (ty := .int .b 32) Flow.code_2349
    he (fun k hk => ⟨_, hpre.paramPage k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨tg, rg, hg⟩ : ∃ t', run kernel asms L g 5 tf = some t' ∧
      At t' 2355 (preFacts P L g 2355) := by
    seg_fp hf using
      (have htid : Proof.tidOf L g < 2 ^ 32 := Proof.tidOf_lt hpre g
       idx_bits [laneOf, land6_mul_comm, mod32_mod4, and6_mod32, and3_mod32])
  obtain ⟨th, rh, hh⟩ := pre_obj_at (P := P) (L := L) (g := g) (mem0 := mem0) hpre
    (pc := 2355) (w := 32) (off := 116) (d := 502) (ty := .int .b 32) Flow.code_2355
    hg (fun k hk => ⟨_, hpre.paramExtraPage k hk⟩) (by decide) (by decide)
    (by idx_values; rfl) (by decide +kernel) (by lit_mem) (by decide) (by decide)
  obtain ⟨ti, ri, hi⟩ : ∃ t', run kernel asms L g 1 th = some t' ∧
      At t' 2357 ((15, .pred (Thread.ptrIsNull L 80)) :: preFacts P L g 2357) := by
    seg_fp hh using (simp only [Thread.ptrIsNull, Option.getD_some])
  have hc := run_comp r1 r2
  have hc := run_comp hc r3
  have hc := run_comp hc r4
  have hc := run_comp hc r5
  have hc := run_comp hc r6
  have hc := run_comp hc r7
  have hc := run_comp hc r8
  have hc := run_comp hc r9
  have hc := run_comp hc ra
  have hc := run_comp hc rb
  have hc := run_comp hc rc
  have hc := run_comp hc rd
  have hc := run_comp hc re
  have hc := run_comp hc rf
  have hc := run_comp hc rg
  have hc := run_comp hc rh
  have hc := run_comp hc ri
  exact ⟨ti, run_rtg hc, hi⟩

theorem entry_lengths_both {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} (hlt : LaunchTest P L g)
    (htopk : P.topkLenBase.isSome = true) (h : At t 2335 (preFacts P L g 2335)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2360 (preFacts P L g 2360) := by
  obtain ⟨ti, ri, hi⟩ := entry_prefix P L g hpre h
  have hptr : Thread.ptrIsNull L 80 = false := by rw [hlt.ptrOrig, htopk]; rfl
  obtain ⟨tj, rj, hj⟩ := bra_at (pc := 2357) (target := 2361) (p := 15)
    (pick := Thread.ptrIsNull L 80) Flow.code_2357 hi (by simp) (by decide) (by decide)
  rw [hptr] at hj
  simp only [Bool.false_eq_true, ite_false] at hj
  have hk : At tj 2358 (preFacts P L g 2358) := at_of_cons hj (by lit_mem)
  obtain ⟨tl, rl, hl⟩ : ∃ t', run kernel asms L g 2 tj = some t' ∧
      At t' 2360 (preFacts P L g 2360) := by
    seg_fp hk using idx_bits
  have hc := Relation.ReflTransGen.trans ri (run_rtg rj)
  exact ⟨tl, Relation.ReflTransGen.trans hc (run_rtg rl), hl⟩

/-- The parameter's main-cache length is its constant when the length pointer is null. -/
theorem topkLen_eq_topk {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (h : P.topkLenBase = none) {e : Nat} (he : e < P.b) : P.topkLen e = P.topk := by
  have hp := hpre.paramTopkLen
  rw [h] at hp
  exact hp.2 e he

/-- The prefix facts at the extra-cache length load are the initial state's facts. -/
theorem preFacts_lenExtra (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) (hnone : P.topkLenBase = none) (he : eOf L g < P.b)
    (hsite : firstSite P = .lenExtra) {t : TState}
    (h : At t 2365 (preFacts P L g 2365)) : At t 2365 (facts P L g (init P L g)) := by
  have hl : facts P L g (init P L g) = preFacts P L g 2365 := by
    have hpend : (init P L g).site.pendingRegs = [] := rfl
    have hpc : (init P L g).site.pc = 2365 := by simp [init, hsite, Site.pc]
    have hlist : preLive 2365 =
        [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 2968,
          3011, 3012, 3025] := by decide +kernel
    have hv : ∀ r ∈ preLive 2365,
        valueOf P L g (init P L g) r = valueOf P L g (preD P L g) r := by
      intro r hr
      rw [hlist] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (idx_simp [init, preD, hsite, len1Reg, ↓reduceIte, reduceCtorEq, or_false]; done)
          | (idx_simp [init, preD, hsite, len1Reg, ↓reduceIte, reduceCtorEq, or_false];
             rw [topkLen_eq_topk hpre hnone he])
    rw [facts, hpc]
    rw [show (List.filter
          (fun r => tracked.contains r && !(init P L g).site.pendingRegs.contains r)
          (Flow.live 2365)) = preLive 2365 from by rw [hpend]; decide +kernel]
    rw [preFacts]
    exact List.map_congr_left fun a ha => by rw [hv a ha]
  rw [hl]
  exact h

/-- **The entry prefix when the main-cache length pointer is null**: the null branch, the
extra-cache length pointer's test and the extra length address reach the extra-cache length
load at pc 2365. -/
theorem entry_null_tail (P : Params) (L : Launch) (g : Nat)
    (hlt : LaunchTest P L g) (hnone : P.topkLenBase = none)
    (hsome : P.extraTopkLenBase.isSome = true) {t : TState}
    (h : At t 2357 ((15, .pred (Thread.ptrIsNull L 80)) :: preFacts P L g 2357)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2365 (preFacts P L g 2365) := by
  have hptr : Thread.ptrIsNull L 80 = true := by rw [hlt.ptrOrig, hnone]; rfl
  obtain ⟨t1, r1, h1⟩ := bra_at (pc := 2357) (target := 2361) (p := 15)
    (pick := Thread.ptrIsNull L 80) Flow.code_2357 h (by simp) (by decide) (by decide)
  rw [hptr] at h1
  simp only [ite_true] at h1
  have h1' : At t1 2361 (preFacts P L g 2361) := at_of_cons h1 (by lit_mem)
  obtain ⟨t2, r2, h2⟩ : ∃ t', run kernel asms L g 1 t1 = some t' ∧
      At t' 2362 ((16, .pred (Thread.ptrIsNull L 144)) :: preFacts P L g 2362) := by
    seg_fp h1' using (simp only [Thread.ptrIsNull, Option.getD_some])
  have hptr2 : Thread.ptrIsNull L 144 = false := by rw [hlt.ptrExtra, hsome]; rfl
  obtain ⟨t3, r3, h3⟩ := bra_at (pc := 2362) (target := 2366) (p := 16)
    (pick := Thread.ptrIsNull L 144) Flow.code_2362 h2 (by simp) (by decide) (by decide)
  rw [hptr2] at h3
  simp only [Bool.false_eq_true, ite_false] at h3
  have h3' : At t3 2363 (preFacts P L g 2363) := at_of_cons h3 (by lit_mem)
  obtain ⟨t4, r4, h4⟩ : ∃ t', run kernel asms L g 2 t3 = some t' ∧
      At t' 2365 (preFacts P L g 2365) := by
    seg_fp h3' using idx_bits
  exact ⟨t4, Relation.ReflTransGen.trans
    (run_rtg (run_comp (run_comp r1 r2) r3)) (run_rtg r4), h4⟩

/-- The prefix facts at the main-cache length load are the initial state's facts. -/
theorem preFacts_lenOrig (P : Params) (L : Launch) (g : Nat)
    (hsite : firstSite P = .lenOrig) {t : TState}
    (h : At t 2360 (preFacts P L g 2360)) : At t 2360 (facts P L g (init P L g)) := by
  have hl : facts P L g (init P L g) = preFacts P L g 2360 := by
    have hpend : (init P L g).site.pendingRegs = [] := rfl
    have hpc : (init P L g).site.pc = 2360 := by simp [init, hsite, Site.pc]
    have hlist : preLive 2360 =
        [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 2969,
          3010, 3011, 3012, 3023] := by decide +kernel
    have hv : ∀ r ∈ preLive 2360,
        valueOf P L g (init P L g) r = valueOf P L g (preD P L g) r := by
      intro r hr
      rw [hlist] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        idx_simp [init, preD, hsite, len1Reg, ↓reduceIte, reduceCtorEq, or_false]
    rw [facts, hpc]
    rw [show (List.filter
          (fun r => tracked.contains r && !(init P L g).site.pendingRegs.contains r)
          (Flow.live 2360)) = preLive 2360 from by rw [hpend]; decide +kernel]
    rw [preFacts]
    exact List.map_congr_left fun a ha => by rw [hv a ha]
  rw [hl]
  exact h

/-- The first parameter load of the entry prefix: `%r559 = b` at pc 2332. -/
theorem entry_2332 (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) {t : TState} (h : At t 2332 (preFacts P L g 2332)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 2333 (preFacts P L g 2333) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have hm := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g (preD P L g))
      (r := 2991) (by decide +kernel))
    simpa [preFacts, valueOf, table, preD, init, PTX.Flow.lookupLit, Option.getD_some] using hm
  exact ld_obj_at (P := P) (L := L) (g := g) (pc := 2332) (w := 32) (off := 0) (d := 559)
    (r := 2991) (ty := .int .b 32) (live := preLive 2332) (live' := preLive 2333)
    (val := valueOf P L g (preD P L g)) Flow.code_2332 h2991 hpre.param0Object
    (fun k hk => ⟨_, hpre.paramB k hk⟩) (by decide) (by decide) h rfl
    (fun x hx => mem_factsFrom hx) (by lit_mem) (by decide) (by decide)

/-- The exit test of pc 2333, with its predicate fact. -/
theorem entry_2333 (P : Params) (L : Launch) (g : Nat) {t : TState}
    (h : At t 2333 (preFacts P L g 2333)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' 2334 ((14, .pred (Thread.geBatch L g)) :: preFacts P L g 2334) := by
  seg_fp h using (rw [thread_geBatch_eq]; simp only [Option.getD_some])

/-- The exit branch of pc 2334: a CTA of the grid does not take it. -/
theorem entry_2334 (P : Params) (L : Launch) (g : Nat) {t : TState} (hlt : LaunchTest P L g)
    (h : At t 2334 ((14, .pred (Thread.geBatch L g)) :: preFacts P L g 2334)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 2335 (preFacts P L g 2335) := by
  obtain ⟨t', hr, h'⟩ := bra_at (pc := 2334) (target := 3611) (p := 14)
    (pick := Thread.geBatch L g) Flow.code_2334 h (by simp) (by decide) (by decide)
  rw [hlt.noExit] at h'
  simp only [Bool.false_eq_true, ite_false] at h'
  exact ⟨t', hr, at_of_cons h' (by lit_mem)⟩

/-- **The role's run from its entry, main-cache length pointer present**: the local prefix
reaches the main-cache length load at pc 2360, the machine's initial state. -/
theorem start_lenOrig (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) (hlt : LaunchTest P L g) (hsite : firstSite P = .lenOrig)
    {t : TState} (hentry : Entry P L g t) (htopk : P.topkLenBase.isSome = true) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' := by
  obtain ⟨t1, r1, h1⟩ := entry_2332 P L g hpre (entry_atFacts P L g hentry)
  obtain ⟨t2, r2, h2⟩ := entry_2333 P L g h1
  obtain ⟨t3, r3, h3⟩ := entry_2334 P L g hlt h2
  obtain ⟨t4, r4, h4⟩ := entry_lengths_both (P := P) (L := L) (g := g) hpre hlt htopk h3
  have h4' : At t4 2360 (facts P L g (init P L g)) := preFacts_lenOrig P L g hsite h4
  refine ⟨t4, Relation.ReflTransGen.trans
    (run_rtg (run_comp (run_comp r1 r2) r3)) r4, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, h4'.2.2.2.2⟩
  · show t4.pc = (init P L g).site.pc
    rw [show (init P L g).site.pc = 2360 by simp [init, hsite, Site.pc]]
    exact h4'.1
  · rw [show (code P L g).sub (init P L g) = 0 by simp [code, init, hsite, Site.sub]]
    exact h4'.2.1
  · rw [show (code P L g).acc (init P L g) = [] by simp [code, accOf, init, hsite]]
    exact h4'.2.2.1
  · show t4.fault = none
    exact h4'.2.2.2.1

/-- **The role's run from its entry, main-cache length pointer null and extra-cache length
pointer present**: the local prefix reaches the extra-cache length load at pc 2365, the
machine's initial state. -/
theorem start_lenExtra (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) (hlt : LaunchTest P L g) (hsite : firstSite P = .lenExtra)
    {t : TState} (hentry : Entry P L g t) (hnone : P.topkLenBase = none)
    (hsome : P.extraTopkLenBase.isSome = true) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' := by
  obtain ⟨t1, r1, h1⟩ := entry_2332 P L g hpre (entry_atFacts P L g hentry)
  obtain ⟨t2, r2, h2⟩ := entry_2333 P L g h1
  obtain ⟨t3, r3, h3⟩ := entry_2334 P L g hlt h2
  obtain ⟨t4, r4, h4⟩ := entry_prefix P L g hpre h3
  obtain ⟨t5, r5, h5⟩ := entry_null_tail P L g hlt hnone hsome h4
  have h5' : At t5 2365 (facts P L g (init P L g)) :=
    preFacts_lenExtra P L g hpre hnone hentry.batch hsite h5
  have r14 : Relation.ReflTransGen (Tau kernel asms L g) t t4 :=
    Relation.ReflTransGen.trans (run_rtg (run_comp (run_comp r1 r2) r3)) r4
  refine ⟨t5, Relation.ReflTransGen.trans r14 r5, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, h5'.2.2.2.2⟩
  · show t5.pc = (init P L g).site.pc
    rw [show (init P L g).site.pc = 2365 by simp [init, hsite, Site.pc]]
    exact h5'.1
  · rw [show (code P L g).sub (init P L g) = 0 by simp [code, init, hsite, Site.sub]]
    exact h5'.2.1
  · rw [show (code P L g).acc (init P L g) = [] by simp [code, accOf, init, hsite]]
    exact h5'.2.2.1
  · show t5.fault = none
    exact h5'.2.2.2.1

/-! ## The null-length branch: the padded block counts

When both length pointers are null the role takes the branch at pc 2362 into the `ku::ceil`
arithmetic of pcs 2366-2384: the two padded block counts `%r503 = totalBlocks` and
`%r2980 = numOrigBlocks`, computed on 32-bit signed words. The lengths are the row's runtime
lengths, which the parameters bound (`topkLen_le`, `extraLen_le`), so every intermediate word is
a small nonnegative 32-bit integer and the signed shifts are the sign corrections of a
nonnegative value. -/

/-- The low 32 bits read as a signed integer, for a small nonnegative word. -/
theorem toSigned_b32 {x : Nat} (hx : x % 2 ^ 32 < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 x) = ((x % 2 ^ 32 : Nat) : Int) := by
  have hmod : x % 2 ^ 64 % 2 ^ 32 = x % 2 ^ 32 :=
    Nat.mod_mod_of_dvd x (by decide)
  simp only [toSigned, BitVec.toNat_ofNat, hmod]
  rw [show (2 : Nat) ^ (32 - 1) = 2 ^ 31 by decide]
  rw [ite_eq_left (by omega)]

/-- The `ku::ceil` mask on a 32-bit word: `x & -64 = x / 64 * 64` (`(x + 63) & -64`). -/
theorem and_neg64_of_lt {x : Nat} (h : x < 2 ^ 32) :
    x &&& 4294967232 = x / 64 * 64 := by
  have hm : (4294967232 : Nat) = (2 ^ 32 : Nat) - 64 := by decide
  rw [hm]
  have hdiv : (x &&& ((2 ^ 32 : Nat) - 64)) / 64 = x / 64 := by
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.and_div_two_pow]
    have hm : ((2 ^ 32 : Nat) - 2 ^ 6) / 2 ^ 6 = 2 ^ 26 - 1 := by decide
    rw [hm, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : (x &&& ((2 ^ 32 : Nat) - 64)) % 64 = 0 := by
    rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.and_mod_two_pow]
    have hm : ((2 ^ 32 : Nat) - 2 ^ 6) % 2 ^ 6 = 0 := by decide
    rw [hm, Nat.and_zero]
  have hx : x % 64 + 64 * (x / 64) = x := Nat.mod_add_div x 64
  omega

/-- `ku::ceil(n, 64)` is the mask of `n + 63`, for a small `n`. -/
theorem ceilToMultiple_eq_mask {n : Nat} (h : n + 63 < 2 ^ 32) :
    ceilToMultiple n topkBlock = (n + 63) &&& 4294967232 := by
  have hx : n + 64 - 1 = n + 63 := by omega
  unfold ceilToMultiple topkBlock
  rw [hx, and_neg64_of_lt h]

/-- `orig_topk_padded` is `max(ku::ceil(n, 64), 64)`, for a small `n`. -/
theorem origPadded_eq_mask {n : Nat} (h : n + 63 < 2 ^ 32) :
    origPadded n = max ((n + 63) &&& 4294967232) 64 := by
  unfold origPadded
  rw [ceilToMultiple_eq_mask h]
  rfl

/-- A sum of two multiples of 64 divides termwise. -/
theorem div64_add {a b : Nat} (ha : a % 64 = 0) (hb : b % 64 = 0) :
    (a + b) / 64 = a / 64 + b / 64 := by
  obtain ⟨ka, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨kb, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  rw [← Nat.mul_add]
  simp

theorem origPadded_mod64 (n : Nat) : origPadded n % 64 = 0 := by
  have h := ceilToMultiple_mod n topkBlock
  unfold origPadded
  simp only [topkBlock] at h ⊢
  rcases Nat.le_total (ceilToMultiple n 64) 64 with hle | hle
  · rw [Nat.max_eq_right hle, Nat.mod_self]
  · rw [Nat.max_eq_left hle]
    exact h

theorem ceilToMultiple_mod64 (n : Nat) : ceilToMultiple n topkBlock % 64 = 0 :=
  ceilToMultiple_mod n topkBlock

/-- The padded sum's block count: `(origPadded len0 + ceil(extraLen)) / 64` is
`totalBlocks len0 extraLen`. -/
theorem totalBlocks_eq_counts (len0 len1 : Nat) :
    (origPadded len0 + ceilToMultiple len1 topkBlock) / 64 =
      totalBlocks len0 len1 := by
  rw [div64_add (origPadded_mod64 len0) (ceilToMultiple_mod64 len1), totalBlocks_eq]
  rfl

/-- The padded main count's block count. -/
theorem numOrigBlocks_eq_counts (len0 : Nat) : origPadded len0 / 64 = numOrigBlocks len0 := rfl

/-- A sum of two small 32-bit words, as the instructions compute it. -/
theorem add_bits {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a + b < 2 ^ 32) :
    BitVec.ofNat 64 ((a % 4294967296 + b % 4294967296) % 18446744073709551616 % 4294967296) =
      BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A difference of two small 32-bit words as the instructions compute it, on 32 bits. -/
theorem sub_bits {c b : Nat} (hc : c < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 64 ((4294967296 + c % 4294967296 + (18446744073709551616 - b % 4294967296)) %
        18446744073709551616 % 4294967296) =
      BitVec.ofNat 64 ((4294967296 + c - b) % 4294967296) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A sum with a wrapped difference cancels the difference when the operands are small. -/
theorem add_sub_bits {A b c : Nat} (hb : b ≤ A) (hc : c ≤ b) (hA : A < 2 ^ 32) :
    BitVec.ofNat 64 ((A % 4294967296 +
        (4294967296 + c - b) % 4294967296 % 4294967296) % 18446744073709551616 % 4294967296) =
      BitVec.ofNat 64 (A + c - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- `ku::ceil(n, 64)` as the quotient of `n + 63`. -/
theorem ceilToMultiple_eq_div {n : Nat} (h : n + 63 < 2 ^ 32) :
    ceilToMultiple n topkBlock = (n + 63) / 64 * 64 := by
  rw [ceilToMultiple_eq_mask h, and_neg64_of_lt h]

/-- The two caches' block count as the sum of their quotients. -/
theorem totalBlocks_eq_div {len0 len1 : Nat} (_h0 : len0 + 63 < 2 ^ 32)
    (h1 : len1 + 63 < 2 ^ 32) :
    totalBlocks len0 len1 = origPadded len0 / 64 + (len1 + 63) / 64 := by
  rw [← totalBlocks_eq_counts,
    div64_add (origPadded_mod64 len0) (ceilToMultiple_mod64 len1), ceilToMultiple_eq_div h1]
  simp

/-- A signed shift of a small nonnegative word, as the instructions compute it. -/
theorem shr_s_val {x s : Nat} (hx : x < 2 ^ 31) (hs : s ≤ 32) :
    (toSigned 32 (BitVec.ofNat 64 x) / 2 ^ min s 32 % 18446744073709551616).toNat %
        4294967296 =
      x / 2 ^ s := by
  have hx32 : x % 2 ^ 32 < 2 ^ 31 := by
    rw [Nat.mod_eq_of_lt (by omega)]; exact hx
  rw [toSigned_b32 hx32]
  rw [show x % 2 ^ 32 = x from Nat.mod_eq_of_lt (by omega)]
  rw [show min s 32 = s from by omega]
  rw [show ((2 : Int) ^ s) = ((2 ^ s : Nat) : Int) from (Nat.cast_pow 2 s).symm]
  rw [← Int.natCast_div]
  have hlt : x / 2 ^ s < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self x _) (by omega)
  have hlt64 : x / 2 ^ s < 2 ^ 64 := by omega
  have h0 : (0 : Int) ≤ ((x / 2 ^ s : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 : ((x / 2 ^ s : Nat) : Int) < 18446744073709551616 := by
    exact_mod_cast hlt64
  rw [show (((x / 2 ^ s : Nat) : Int) % 18446744073709551616) = ((x / 2 ^ s : Nat) : Int) from
    Int.emod_eq_of_lt h0 h1]
  simp only [Int.toNat_natCast]
  exact Nat.mod_eq_of_lt hlt

/-- The signed 31-bit shift of a small word is zero. -/
theorem shr_s_val31 {x : Nat} (hx : x < 2 ^ 31) :
    (toSigned 32 (BitVec.ofNat 64 x) / 2 ^ min 31 32 % 18446744073709551616).toNat %
        4294967296 =
      x / 2 ^ 31 :=
  shr_s_val hx (by decide)

/-- The signed 6-bit shift of a small word is its sixty-fourth part. -/
theorem shr_s_val6 {x : Nat} (hx : x < 2 ^ 31) :
    (toSigned 32 (BitVec.ofNat 64 x) / 2 ^ min 6 32 % 18446744073709551616).toNat %
        4294967296 =
      x / 64 := by
  have h := shr_s_val (s := 6) hx (by decide)
  simpa using h

/-- An unsigned shift of a small 32-bit word, as the instructions compute it. -/
theorem shr_u_val {x s : Nat} (hx : x < 2 ^ 32) :
    x % 4294967296 / 2 ^ s % 4294967296 = x / 2 ^ s := by
  rw [show x % 4294967296 = x from Nat.mod_eq_of_lt hx]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self x _) hx)

/-- A signed `gt` of two small nonnegative 32-bit words is the `Nat` comparison. -/
theorem compare_gt_b32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (ha' : a < 2 ^ 31) (hb' : b < 2 ^ 31) :
    PTX.compare .gt .s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a > b) := by
  rw [show PTX.compare .gt .s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      decide (a % 2 ^ 32 > b % 2 ^ 32) from by
    unfold PTX.compare
    dsimp only
    rw [toSigned_b32 (by omega), toSigned_b32 (by omega)]
    simp only [Int.ofNat_lt]]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `max.s32` of two small nonnegative 32-bit words is the `Nat` maximum. -/
theorem max_bits {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (ha' : a < 2 ^ 31) (hb' : b < 2 ^ 31) :
    (if PTX.compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
        IType.s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true then
      BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (max a b) := by
  have hm : (IntOp.max false == IntOp.max false) = true := by decide
  rw [hm]
  simp only [↓reduceIte]
  rw [compare_gt_b32 ha hb ha' hb']
  by_cases h : a > b
  · rw [ite_eq_left (by simpa using h), show max a b = a from by omega]
  · rw [ite_eq_right (by simpa using h), show max a b = b from by omega]

/-- A signed `lt` of two small nonnegative 32-bit words is the `Nat` comparison. -/
theorem compare_lt_b32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (ha' : a < 2 ^ 31) (hb' : b < 2 ^ 31) :
    PTX.compare .lt .s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [show PTX.compare .lt .s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) =
      decide (a % 2 ^ 32 < b % 2 ^ 32) from by
    unfold PTX.compare
    dsimp only
    rw [toSigned_b32 (by omega), toSigned_b32 (by omega)]
    simp only [Int.ofNat_lt]]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-- `min.s32` of two small nonnegative 32-bit words is the `Nat` minimum. -/
theorem min_bits {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (ha' : a < 2 ^ 31) (hb' : b < 2 ^ 31) :
    (if PTX.compare (if (IntOp.min false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
        IType.s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true then
      BitVec.ofNat 64 a else BitVec.ofNat 64 b) = BitVec.ofNat 64 (min a b) := by
  have hm : (IntOp.min false == IntOp.max false) = false := by decide
  rw [hm]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [compare_lt_b32 ha hb ha' hb']
  by_cases h : a < b
  · rw [ite_eq_left (by simpa using h), show min a b = a from by omega]
  · rw [ite_eq_right (by simpa using h), show min a b = b from by omega]

/-- The block-0 predicate `%r504 < 1` is false: a row has at least one main-cache block. -/
theorem pair_min_pred {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (ha' : a < 2 ^ 31) (hb' : b < 2 ^ 31) (hM : min a b < 2 ^ 32)
    (hab : a ≤ b) (ha1 : 1 ≤ a) :
    PTX.compare Cmp.lt IType.s 32
      (truncBits 32
        (if PTX.compare (if (IntOp.min false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
            IType.s 32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = true then
          BitVec.ofNat 64 a else BitVec.ofNat 64 b)) (BitVec.ofNat 64 1) = false := by
  rw [min_bits ha hb ha' hb']
  rw [show truncBits 32 (BitVec.ofNat 64 (min a b)) = BitVec.ofNat 64 (min a b) from by
    simp only [truncBits, BitVec.toNat_ofNat]
    congr 1
    omega]
  rw [show min a b = a from by omega]
  rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  rw [compare_lt_b32 ha (by decide) ha' (by decide)]
  simp only [decide_eq_false_iff_not]
  omega

/-- The `ku::ceil` of a 32-bit word as the decoded instructions compute it: the signed shift
correction of `n + 63` and the mask, as a `Nat` value. -/
theorem ceil_val (n : Nat) (hn : n + 63 < 2 ^ 31) :
    (((n + 63) % 4294967296 +
        (toSigned 32 (BitVec.ofNat 64 ((n + 63) % 4294967296)) / 2 ^ min 31 32 %
          18446744073709551616).toNat % 4294967296 / 67108864 % 4294967296) %
        4294967296 &&& 4294967232)
      = (n + 63) / 64 * 64 := by
  have hn32 : n + 63 < 2 ^ 32 := by omega
  have hmod : (n + 63) % 4294967296 = n + 63 := Nat.mod_eq_of_lt hn32
  have hx : (n + 63) % 2 ^ 32 < 2 ^ 31 := by
    rw [show 2 ^ 32 = 4294967296 from rfl, hmod]; omega
  rw [show min 31 32 = 31 from rfl]
  rw [hmod]
  have hts : toSigned 32 (BitVec.ofNat 64 (n + 63)) = (((n + 63) % 2 ^ 32 : Nat) : Int) :=
    toSigned_b32 hx
  rw [show 2 ^ 32 = 4294967296 from rfl, hmod] at hts
  rw [hts]
  have hdiv : ((n + 63 : Nat) : Int) / 2 ^ 31 = 0 := by
    rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
  rw [hdiv]
  norm_num
  rw [hmod, and_neg64_of_lt hn32]

/-- The same as a 32-bit word. -/
theorem ceil_bits (n : Nat) (hn : n + 63 < 2 ^ 31) :
    BitVec.ofNat 64
      ((((n + 63) % 4294967296 +
        (toSigned 32 (BitVec.ofNat 64 ((n + 63) % 4294967296)) / 2 ^ min 31 32 %
          18446744073709551616).toNat % 4294967296 / 67108864 % 4294967296) %
        4294967296 &&& 4294967232) % 4294967296) =
      BitVec.ofNat 64 ((n + 63) / 64 * 64) := by
  rw [ceil_val n hn]
  congr 1
  exact Nat.mod_eq_of_lt (by
    have := Nat.div_mul_le_self (n + 63) 64
    omega)

/-- The `max(ku::ceil(n, 64), 64)` instruction's value is `origPadded n`, with the ceiling
already reduced to `(n + 63) / 64 * 64`. -/
theorem origPadded_bits (n : Nat) (hn : n + 63 < 2 ^ 31) :
    (if PTX.compare (if (IntOp.max false == IntOp.max false) = true then Cmp.gt else Cmp.lt)
        IType.s 32 (BitVec.ofNat 64 ((n + 63) / 64 * 64)) (BitVec.ofNat 64 64) = true then
      BitVec.ofNat 64 ((n + 63) / 64 * 64) else BitVec.ofNat 64 64) =
      BitVec.ofNat 64 (origPadded n) := by
  have hn32 : n + 63 < 2 ^ 32 := by omega
  have ha : (n + 63) / 64 * 64 < 2 ^ 32 := by
    have := Nat.div_mul_le_self (n + 63) 64
    omega
  have ha' : (n + 63) / 64 * 64 < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.div_mul_le_self (n + 63) 64) (by omega)
  refine Eq.trans (max_bits (a := (n + 63) / 64 * 64) (b := 64) ha (by decide) ha'
    (by decide)) ?_
  rw [show max ((n + 63) / 64 * 64) 64 = origPadded n from by
    rw [origPadded_eq_mask hn32, and_neg64_of_lt hn32]]

/-- The table's facts at `pc` on the registers the role tracks there, without the pending-load
filter (`preLive`): the fact list a segment's `seg_fp` reads, since a pending load's registers
are known only through explicit facts. -/
def liveFacts (P : Params) (L : Launch) (g : Nat) (d : D) (pc : Nat) : List (Nat × Value) :=
  factsFrom (preLive pc) (valueOf P L g d)

/-- At a site with no pending load, the state's facts are the live facts at its pc. -/
theorem facts_eq_liveFacts {d : D} (hpend : d.site.pendingRegs = []) :
    facts P L g d = liveFacts P L g d d.site.pc := by
  rw [facts, liveFacts, hpend]
  congr 1
  simp only [preLive]
  apply List.filter_congr
  intro r _
  simp

/-- The main-cache padded count (pcs 2366-2371) is `origPadded len0`. -/
theorem pair_padded_main {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {d : D}
    (_hd : d.site = .pair false true false) (hlen0 : d.len0 ≤ P.topk)
    (hlen0mod : d.len0 % 4294967296 = d.len0) (h : At t 2366 (liveFacts P L g d 2366)) :
    ∃ t', run kernel asms L g 6 t = some t' ∧
      At t' 2372 (liveFacts P L g d 2372) := by
  have h63 : d.len0 + 63 < 2 ^ 31 := by have := hpre.topkAdd63Lt; omega
  seg_fp h using idx_bits [toSigned_b32, ceil_bits, origPadded_bits, h63, hlen0mod]

/-- The extra-cache padded count (pcs 2372-2376) is `ceilToMultiple len1 64`. -/
theorem pair_padded_extra {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {d : D}
    (hd : d.site = .pair false true false) (hlen1 : d.len1 ≤ P.extra_topk)
    (hlen1mod : d.len1 % 4294967296 = d.len1) (h : At t 2372 (liveFacts P L g d 2372)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧
      At t' 2377 ((573, b32 ((d.len1 + 63) / 64 * 64)) ::
        (569, b32 (d.len1 + 63)) :: liveFacts P L g d 2377) := by
  have hne : d.site ≠ .lenOrig := by rw [hd]; intro h; exact absurd h (by decide)
  have h63 : d.len1 + 63 < 2 ^ 31 := by have := hpre.extraTopkAdd63Lt; omega
  have hne2 : d.site ≠ .lenExtra := by rw [hd]; decide
  seg_fp h using idx_bits [toSigned_b32, ceil_val, h63, hlen1mod, len1Reg_ne hne hne2]

/-- The two caches' block counts (pcs 2377-2384) are `totalBlocks` and `numOrigBlocks`. -/
theorem pair_counts_blocks {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {d : D}
    (hd : d.site = .pair false true false) (hlen0 : d.len0 ≤ P.topk) (hlen1 : d.len1 ≤ P.extra_topk)
    (hpad : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 31)
    (h : At t 2377 ((573, b32 ((d.len1 + 63) / 64 * 64)) ::
      (569, b32 (d.len1 + 63)) :: liveFacts P L g d 2377)) :
    ∃ t', run kernel asms L g 8 t = some t' ∧ At t' 2385 (liveFacts P L g d 2385) := by
  have h1' : d.len1 + 63 < 2 ^ 31 := by have := hpre.extraTopkAdd63Lt; omega
  have h0' : d.len0 + 63 < 2 ^ 31 := by have := hpre.topkAdd63Lt; omega
  have hb32 : d.len1 + 63 < 2 ^ 32 := by omega
  have ho31 : origPadded d.len0 < 2 ^ 31 := by omega
  have ho32 : origPadded d.len0 < 2 ^ 32 := by omega
  have hc32 : (d.len1 + 63) / 64 * 64 < 2 ^ 32 := by
    have := Nat.div_mul_le_self (d.len1 + 63) 64
    omega
  have hcle : (d.len1 + 63) / 64 * 64 ≤ d.len1 + 63 := Nat.div_mul_le_self _ _
  have hsum : d.len1 + 63 + origPadded d.len0 < 2 ^ 32 := by omega
  have hsum2 : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 32 := by omega
  -- 2377: `%r574 = %r569 + %r568`
  obtain ⟨t1, r1, h1'⟩ : ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' 2378 ((574, b32 (d.len1 + 63 + origPadded d.len0)) ::
        (573, b32 ((d.len1 + 63) / 64 * 64)) :: (569, b32 (d.len1 + 63)) ::
        liveFacts P L g d 2378) := by
    seg_fp h using idx_bits [add_bits, hb32, ho32, hsum]
  -- 2378: `%r575 = %r573 - %r569`
  obtain ⟨t2, r2, h2'⟩ : ∃ t', run kernel asms L g 1 t1 = some t' ∧
      At t' 2379
        ((575, b32 ((4294967296 + (d.len1 + 63) / 64 * 64 - (d.len1 + 63)) % 4294967296)) ::
        (574, b32 (d.len1 + 63 + origPadded d.len0)) ::
        (573, b32 ((d.len1 + 63) / 64 * 64)) :: (569, b32 (d.len1 + 63)) ::
        liveFacts P L g d 2379) := by
    seg_fp h1' using idx_bits [sub_bits, hb32, hc32]
  -- 2379: `%r576 = %r574 + %r575`
  obtain ⟨t3, r3, h3'⟩ : ∃ t', run kernel asms L g 1 t2 = some t' ∧
      At t' 2380 ((576, b32 (origPadded d.len0 + (d.len1 + 63) / 64 * 64)) ::
        (575, b32 ((4294967296 + (d.len1 + 63) / 64 * 64 - (d.len1 + 63)) % 4294967296)) ::
        (574, b32 (d.len1 + 63 + origPadded d.len0)) :: liveFacts P L g d 2380) := by
    have hA : d.len1 + 63 ≤ d.len1 + 63 + origPadded d.len0 := by omega
    seg_fp h2' using idx_bits [add_sub_bits, hA, hcle, hsum]
  -- 2380: `%r577 = %r576 >> 31` (signed)
  obtain ⟨t4, r4, h4'⟩ : ∃ t', run kernel asms L g 1 t3 = some t' ∧
      At t' 2381 ((577, b32 0) ::
        (576, b32 (origPadded d.len0 + (d.len1 + 63) / 64 * 64)) ::
        liveFacts P L g d 2381) := by
    have h576 : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 31 := by omega
    have hmod576 : (origPadded d.len0 + (d.len1 + 63) / 64 * 64) % 4294967296 =
        origPadded d.len0 + (d.len1 + 63) / 64 * 64 := Nat.mod_eq_of_lt (by omega)
    have hz : (origPadded d.len0 + (d.len1 + 63) / 64 * 64) / 2 ^ 31 = 0 :=
      Nat.div_eq_of_lt h576
    seg_fp h3' using idx_bits [shr_s_val31, h576, hmod576, hz]
  -- 2381: `%r578 = %r577 >> 26` (unsigned)
  obtain ⟨t5, r5, h5'⟩ : ∃ t', run kernel asms L g 1 t4 = some t' ∧
      At t' 2382 ((578, b32 0) :: (577, b32 0) ::
        (576, b32 (origPadded d.len0 + (d.len1 + 63) / 64 * 64)) ::
        liveFacts P L g d 2382) := by
    seg_fp h4' using idx_bits [shr_u_val]
  -- 2382: `%r579 = %r576 + %r578`
  obtain ⟨t6, r6, h6'⟩ : ∃ t', run kernel asms L g 1 t5 = some t' ∧
      At t' 2383 ((579, b32 (origPadded d.len0 + (d.len1 + 63) / 64 * 64)) ::
        liveFacts P L g d 2383) := by
    seg_fp h5' using idx_bits [add_bits, hsum2]
  -- 2383: `%r503 = %r579 >> 6` (signed)
  obtain ⟨t7, r7, h7'⟩ : ∃ t', run kernel asms L g 1 t6 = some t' ∧
      At t' 2384 (liveFacts P L g d 2384) := by
    have htot : totalBlocks d.len0 d.len1 =
        origPadded d.len0 / 64 + (d.len1 + 63) / 64 :=
      totalBlocks_eq_div (by omega) hb32
    have hcmod : ((d.len1 + 63) / 64 * 64) % 64 = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 64 ((d.len1 + 63) / 64))
    have hdiv : (origPadded d.len0 + (d.len1 + 63) / 64 * 64) / 64 =
        origPadded d.len0 / 64 + (d.len1 + 63) / 64 := by
      rw [div64_add (a := origPadded d.len0) (b := (d.len1 + 63) / 64 * 64)
        (origPadded_mod64 _) hcmod]
      simp
    have h576 : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 31 := by omega
    have hmod576 : (origPadded d.len0 + (d.len1 + 63) / 64 * 64) % 4294967296 =
        origPadded d.len0 + (d.len1 + 63) / 64 * 64 := Nat.mod_eq_of_lt (by omega)
    have hsmall : (origPadded d.len0 / 64 + (d.len1 + 63) / 64) % 18446744073709551616 =
        origPadded d.len0 / 64 + (d.len1 + 63) / 64 := Nat.mod_eq_of_lt (by omega)
    seg_fp h6' using
      (try simp only [List.append, List.cons_append, List.nil_append])
      (try repeat' (first | exact trivial |
        (refine PTX.Proof.holds_cons_of rfl ?_ ?_)))
      (try rw [hdiv, ← htot])
      (try idx_bits [shr_s_val6, h576, hmod576, hsmall])
  -- 2384: `%r2980 = %r568 >> 6` (unsigned)
  obtain ⟨t8, r8, h8'⟩ : ∃ t', run kernel asms L g 1 t7 = some t' ∧
      At t' 2385 (liveFacts P L g d 2385) := by
    have hcf : countReg d = numOrigBlocks d.len0 := countReg_pair_false hd
    have hmod : origPadded d.len0 % 4294967296 = origPadded d.len0 := Nat.mod_eq_of_lt ho32
    have hmod64 : origPadded d.len0 / 64 % 18446744073709551616 = origPadded d.len0 / 64 :=
      Nat.mod_eq_of_lt (by omega)
    have hfin : origPadded d.len0 % 18446744073709551616 / 64 % 18446744073709551616 =
        numOrigBlocks d.len0 := by
      rw [show origPadded d.len0 % 18446744073709551616 = origPadded d.len0 from
        Nat.mod_eq_of_lt (by omega)]
      rw [hmod64]
      exact numOrigBlocks_eq_counts d.len0
    have hmod568 : origPadded d.len0 % 4294967296 = origPadded d.len0 := hmod
    seg_fp h7' using idx_bits [shr_u_val, hcf, hfin, ho32, hmod568]
  refine ⟨t8, ?_, h8'⟩
  exact run_comp (run_comp (run_comp (run_comp (run_comp (run_comp (run_comp r1 r2) r3) r4)
    r5) r6) r7) r8
end

/-- The `seg_fp` value tactic: unfold an appended fact list, split the facts of a `Holds` goal,
and close each register-value equation by the index normal form. -/
macro "seg_vals" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    (try simp only [List.append, List.cons_append, List.nil_append])
    (try (repeat' (first | exact trivial | (refine PTX.Proof.holds_cons_of rfl ?_ ?_))))
    all_goals (try idx_bits [$ls,*])))

section
variable {P : Params} {L : Launch}

/-- The index-pair addresses of the null branch (pcs 2385-2397): the CTA's two row offsets, the
current block count, and the block-0 predicate. -/
theorem pair_addresses {g : Nat} {t : TState} {d : D} (hd : d.site = .pair false true false)
    (h0 : d.len0 + 63 < 2 ^ 32) (h1 : d.len1 + 63 < 2 ^ 32)
    (hpad : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 31)
    (h : At t 2385 (liveFacts P L g d 2385)) :
    ∃ t', run kernel asms L g 13 t = some t' ∧
      At t' 2398 ((3013, b64 (idxRowOff P L g)) :: (3014, b64 (extraRowOff P L g)) ::
        (17, .pred false) :: liveFacts P L g d 2398) := by
  have hcf : countReg d = numOrigBlocks d.len0 := countReg_pair_false hd
  have htot : totalBlocks d.len0 d.len1 = origPadded d.len0 / 64 + (d.len1 + 63) / 64 :=
    totalBlocks_eq_div h0 h1
  have hsum31 : origPadded d.len0 / 64 + (d.len1 + 63) / 64 < 2 ^ 31 := by
    have h0' := Nat.div_le_self (origPadded d.len0) 64
    omega
  have hsum32 : origPadded d.len0 / 64 + (d.len1 + 63) / 64 < 2 ^ 32 := by
    omega
  have hnum32 : numOrigBlocks d.len0 < 2 ^ 32 := by
    have h1 : numOrigBlocks d.len0 ≤ totalBlocks d.len0 d.len1 := numOrigBlocks_le_totalBlocks _ _
    rw [htot] at h1
    omega
  have hnummod : numOrigBlocks d.len0 % 4294967296 = numOrigBlocks d.len0 :=
    Nat.mod_eq_of_lt hnum32
  have hsummod : (origPadded d.len0 / 64 + (d.len1 + 63) / 64) % 4294967296 =
      origPadded d.len0 / 64 + (d.len1 + 63) / 64 := Nat.mod_eq_of_lt hsum32
  have hle : numOrigBlocks d.len0 ≤ origPadded d.len0 / 64 + (d.len1 + 63) / 64 := by
    rw [← htot]
    exact numOrigBlocks_le_totalBlocks _ _
  have hpos : 1 ≤ numOrigBlocks d.len0 := numOrigBlocks_pos _
  have hnum31 : numOrigBlocks d.len0 < 2 ^ 31 := by
    rw [← numOrigBlocks_eq_counts]
    have := Nat.div_le_self (origPadded d.len0) 64
    omega
  have hM : min (numOrigBlocks d.len0) (origPadded d.len0 / 64 + (d.len1 + 63) / 64) < 2 ^ 32 := by
    omega
  have hpair : d.site.hasPair = false := by rw [hd]; rfl
  seg_fp h using
    (try idx_bits [hcf, htot, cvtIntBits, intBits, intSat, intOf, cvtS32,
      idxRowOff, extraRowOff, mulWideS32, Bool.not_false, Bool.not_true, mod32_idem,
      Nat.mod_mod, Nat.mul_mod, cvtS32, min_bits, pair_min_pred,
      hnummod, hsummod, hle, hpos, hnum32, hsum32, htot, hM, hnum31, hsum31, hpair,
      (show (2 : Nat) ^ 32 = 4294967296 from rfl),
      (show (2 : Nat) ^ 64 = 18446744073709551616 from rfl)])
    (try exact pair_min_pred hnum32 hsum32 hnum31 hsum31 hM hle hpos)
    (try exact min_bits hnum32 hsum32 hnum31 hsum31)
    (try exact (min_bits hnum32 hsum32 hnum31 hsum31).trans (by
      rw [show min (numOrigBlocks d.len0) (origPadded d.len0 / 64 + (d.len1 + 63) / 64) =
          numOrigBlocks d.len0 from by omega]))

/-- The block-0 branch at pc 2398 is not taken: a row has at least one main-cache block. -/
theorem pair_branch {P : Params} {L : Launch} {g : Nat} {t : TState}
    (h : At t 2398 ((3013, b64 (idxRowOff P L g)) :: (3014, b64 (extraRowOff P L g)) ::
      (17, .pred false) :: liveFacts P L g d 2398)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' 2399 ((3013, b64 (idxRowOff P L g)) :: (3014, b64 (extraRowOff P L g)) ::
        (17, .pred false) :: liveFacts P L g d 2398) := by
  obtain ⟨t', hr, h'⟩ := bra_at (pc := 2398) (target := 2404) (p := 17)
    (pick := false) Flow.code_2398 h (by simp) (by decide) (by decide)
  exact ⟨t', hr, h'⟩

/-- The pair-load address of block 0 (pcs 2399-2402). -/
theorem pair_load_addr {g : Nat} {mem0 : Mem0} (_hpre : Pre P L mem0) {t : TState} {d : D}
    (_hd : d.site = .pair false true false)
    (h : At t 2399 ((3013, b64 (idxRowOff P L g)) :: (3014, b64 (extraRowOff P L g)) ::
      (17, .pred false) :: liveFacts P L g d 2398)) :
    ∃ t', run kernel asms L g 4 t = some t' ∧ At t' 2403 (liveFacts P L g d 2403) := by
  seg_fp h using seg_vals [show (liveFacts P L g d 2398).length = (liveFacts P L g d 2398).length
    from rfl]

/-- **The null-branch tail**: the `ku::ceil` counts, the two index-row offsets and the pair-load
address of block 0 (pcs 2366-2402) take the initial state to the pair load at pc 2403. -/
theorem pairTail {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) {t : TState} {d : D}
    (hd : d.site = .pair false true false) (hlen0 : d.len0 ≤ P.topk) (hlen1 : d.len1 ≤ P.extra_topk)
    (hpad : origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31)
    (h : At t 2366 (liveFacts P L g d 2366)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2403 (liveFacts P L g d 2403) := by
  have h0 : d.len0 + 63 < 2 ^ 32 := by have := hpre.topkAdd63Lt; omega
  have h1 : d.len1 + 63 < 2 ^ 32 := by have := hpre.extraTopkAdd63Lt; omega
  have hpad' : origPadded d.len0 + (d.len1 + 63) / 64 * 64 < 2 ^ 31 := by
    have hp : ceilToMultiple d.len1 topkBlock = (d.len1 + 63) / 64 * 64 := by
      unfold ceilToMultiple topkBlock
      omega
    rwa [hp] at hpad
  have hlen0mod : d.len0 % 4294967296 = d.len0 :=
    Nat.mod_eq_of_lt (by omega)
  have hlen1mod : d.len1 % 4294967296 = d.len1 :=
    Nat.mod_eq_of_lt (by omega)
  obtain ⟨t1, r1, ht1⟩ := pair_padded_main hpre hd hlen0 hlen0mod h
  obtain ⟨t2, r2, h2⟩ := pair_padded_extra hpre hd hlen1 hlen1mod ht1
  obtain ⟨t3, r3, h3⟩ := pair_counts_blocks hpre hd hlen0 hlen1 hpad' h2
  obtain ⟨t4, r4, h4⟩ := pair_addresses hd h0 h1 hpad' h3
  obtain ⟨t5, r5, h5⟩ := pair_branch h4
  obtain ⟨t6, r6, h6⟩ := pair_load_addr hpre hd h5
  refine ⟨t6, run_rtg (run_comp (run_comp (run_comp (run_comp (run_comp r1 r2) r3) r4) r5)
    r6), h6⟩

/-- **The entry prefix when both length pointers are null**: the null branch at 2357, the
extra-cache length pointer's test at 2361 and the taken branch at 2362 reach the `ku::ceil`
arithmetic at pc 2366. -/
theorem entry_null_tail_both (P : Params) (L : Launch) (g : Nat)
    (hlt : LaunchTest P L g) (hnone : P.topkLenBase = none)
    (hnone2 : P.extraTopkLenBase = none) {t : TState}
    (h : At t 2357 ((15, .pred (Thread.ptrIsNull L 80)) :: preFacts P L g 2357)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2366 (preFacts P L g 2366) := by
  have hptr : Thread.ptrIsNull L 80 = true := by
    rw [hlt.ptrOrig, hnone]; rfl
  obtain ⟨t1, r1, h1⟩ := bra_at (pc := 2357) (target := 2361) (p := 15)
    (pick := Thread.ptrIsNull L 80) Flow.code_2357 h (by simp) (by decide) (by decide)
  rw [hptr] at h1
  simp only [ite_true] at h1
  have h1' : At t1 2361 (preFacts P L g 2361) := at_of_cons h1 (by lit_mem)
  obtain ⟨t2, r2, h2⟩ : ∃ t', run kernel asms L g 1 t1 = some t' ∧
      At t' 2362 ((16, .pred (Thread.ptrIsNull L 144)) :: preFacts P L g 2362) := by
    seg_fp h1' using (simp only [Thread.ptrIsNull, Option.getD_some])
  have hptr2 : Thread.ptrIsNull L 144 = true := by
    rw [hlt.ptrExtra, hnone2]; rfl
  obtain ⟨t3, r3, h3⟩ := bra_at (pc := 2362) (target := 2366) (p := 16)
    (pick := Thread.ptrIsNull L 144) Flow.code_2362 h2 (by simp) (by decide) (by decide)
  rw [hptr2] at h3
  simp only [ite_true] at h3
  refine ⟨t3, Relation.ReflTransGen.trans (run_rtg (run_comp r1 r2)) (run_rtg r3), ?_⟩
  exact at_of_cons h3 (by lit_mem)

/-- The parameter's extra-cache length is its constant when that length pointer is null. -/
theorem extraTopkLen_eq_extraTopk {mem0 : Mem0} (hpre : Pre P L mem0)
    (h : P.extraTopkLenBase = none) {e : Nat} (he : e < P.b) :
    P.extraTopkLen e = P.extra_topk := by
  have hp := hpre.paramExtraTopkLen
  rw [h] at hp
  exact hp.2 e he

/-- **The role's run from its entry, both length pointers null**: the local prefix reaches the
`ku::ceil` arithmetic at pc 2366, and the null-branch tail reaches the pair load at pc 2403, the
machine's initial state. -/
theorem start_nullBoth (P : Params) (L : Launch) (g : Nat) {mem0 : Mem0}
    (hpre : Pre P L mem0) (hlt : LaunchTest P L g)
    (hsite : firstSite P = .pair false true false) {t : TState} (hentry : Entry P L g t)
    (hnone : P.topkLenBase = none) (hnone2 : P.extraTopkLenBase = none) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' := by
  obtain ⟨t1, r1, h1⟩ := entry_2332 P L g hpre (entry_atFacts P L g hentry)
  obtain ⟨t2, r2, h2⟩ := entry_2333 P L g h1
  obtain ⟨t3, r3, h3⟩ := entry_2334 P L g hlt h2
  obtain ⟨t4, r4, h4⟩ := entry_prefix P L g hpre h3
  obtain ⟨t5, r5, h5⟩ := entry_null_tail_both P L g hlt hnone hnone2 h4
  have hl0 := topkLen_eq_topk (P := P) (L := L) (mem0 := mem0) hpre hnone hentry.batch
  have hl1 := extraTopkLen_eq_extraTopk (P := P) (L := L) (mem0 := mem0) hpre hnone2 hentry.batch
  have hpreD : preD P L g = init P L g := by
    unfold preD init
    dsimp only
    simp only [eOf]
    rw [hl0, hl1]
  have h5' : At t5 2366 (liveFacts P L g (init P L g) 2366) := by
    rw [liveFacts, ← hpreD]
    exact h5
  have hd : (init P L g).site = .pair false true false := by
    rw [init_site]
    exact hsite
  have hL0 : (init P L g).len0 ≤ P.topk := by
    show P.topkLen (eOf L g) ≤ P.topk
    exact topkLen_le hpre hentry.batch
  have hL1 : (init P L g).len1 ≤ P.extra_topk := by
    show P.extraTopkLen (eOf L g) ≤ P.extra_topk
    exact extraLen_le hpre hentry.batch
  obtain ⟨t6, r6, h6⟩ := pairTail hpre hd hL0 hL1 (hpre.paddedRange _ hentry.batch) h5'
  have hpend : (init P L g).site.pendingRegs = [] := by
    rfl
  have r14 : Relation.ReflTransGen (Tau kernel asms L g) t t4 :=
    Relation.ReflTransGen.trans (run_rtg (run_comp (run_comp r1 r2) r3)) r4
  refine ⟨t6, Relation.ReflTransGen.trans (Relation.ReflTransGen.trans r14 r5) r6, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t6.pc = (init P L g).site.pc
    rw [show (init P L g).site.pc = 2403 by simp [init, hsite, Site.pc]]
    exact h6.1
  · rw [show (code P L g).sub (init P L g) = 0 by simp [code, init, hsite, Site.sub]]
    exact h6.2.1
  · rw [show (code P L g).acc (init P L g) = [] by simp [code, accOf, init, hsite]]
    exact h6.2.2.1
  · show t6.fault = none
    exact h6.2.2.2.1
  · change Holds t6.regs (facts P L g (init P L g))
    rw [facts_eq_liveFacts hpend]
    rw [show (init P L g).site.pc = 2403 by simp [init, hsite, Site.pc]]
    exact h6.2.2.2.2

/-- **The role's run from its entry**: the three branches of the two length pointers. -/
theorem start (P : Params) (L : Launch) (g : Nat) :
    ∀ (mem0 : Mem0) (t : TState), Pre P L mem0 → Entry P L g t → LaunchTest P L g →
      ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
        (code P L g).AtD (init P L g) t' := by
  intro mem0 t hpre hentry hlt
  rcases hb : P.topkLenBase with _ | x
  · rcases hb2 : P.extraTopkLenBase with _ | y
    · have hsite : firstSite P = .pair false true false := by simp [firstSite, hb, hb2]
      exact start_nullBoth P L g hpre hlt hsite hentry hb hb2
    · have hsite : firstSite P = .lenExtra := by simp [firstSite, hb, hb2]
      exact start_lenExtra P L g hpre hlt hsite hentry hb (by simp [hb2])
  · have hsite : firstSite P = .lenOrig := by simp [firstSite, hb]
    exact start_lenOrig P L g hpre hlt hsite hentry (by simp [hb])

/-! ## Reading a state's facts -/

/-- The role's own `AtD` is the machine's: the code's fields are the state's site, sub-step,
accumulator and facts. -/
theorem atD_code {g : Nat} {d : D} {t : TState} :
    (code P L g).AtD d t ↔ AtD P L g d t :=
  Iff.rfl

/-- A tracked register live at the state's site holds the table's value. -/
theorem AtD.reg {g : Nat} {d : D} {t : TState} (h : AtD P L g d t) {r : Nat}
    (hm : r ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  have hm' : r ∈ (Flow.live d.site.pc).filter
      (fun r => tracked.contains r && !d.site.pendingRegs.contains r) := by
    simpa [Site.pendingRegs] using hm
  have hh := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) hm')
  simpa [facts] using hh

/-- What one site's step owes: the event continues to the successor's concrete state, or to the
role's end, or to the machine's pending fault. -/
def Step (P : Params) (L : Launch) (g : Nat) (d : D) (u : TState) (e : Event) : Prop :=
  (next P L g d e = some none ∨ ∃ d' t', next P L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ (code P L g).Good (some d') t') ∨
    (next P L g d e = none ∧ Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u)

/-! ### Inverting the events -/

theorem asms_ncLoads_2360 : asms.any (·.ncLoads 2360) = true := by decide +kernel

theorem asms_ncLoads_2365 : asms.any (·.ncLoads 2365) = true := by decide +kernel

theorem asms_ncLoads_2403 : asms.any (·.ncLoads 2403) = true := by decide +kernel

theorem asms_ncLoads_2429 : asms.any (·.ncLoads 2429) = true := by decide +kernel

theorem asms_ncLoads_2501 : asms.any (·.ncLoads 2501) = true := by decide +kernel

theorem asms_ncLoads_2517 : asms.any (·.ncLoads 2517) = true := by decide +kernel

/-- A weak global `.nc` load that fires is a `readNC` event whose bytes its continuation
reassembles. The location is carried but not computed: `next` reads only the bytes, so the
access's alignment is not needed. -/
theorem fires_nc_load {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {a : MemAccess}
    {e : Event} {base w : Nat} (hk : a.kind = .load) (hnc : a.nc = true)
    (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some .global)
    (hb : a.addr.base = .reg base w) (hsw : a.sem = .weak)
    (hnl : A.any (·.ncLoads t.pc) = true)
    (hf : Fires t.pc (eventTmpl A L g t (.mem a)) e (some u)) :
    ∃ loc bs, e = ⟨t.pc, .nc loc bs⟩ ∧ u = afterLoad t a.regs bs := by
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) hr hs hb hk hsw] at hf
  unfold loadTmpl at hf
  split at hf
  · simp only [Fires] at hf
    exact absurd hf.2 (by simp)
  · rename_i a' heff
    rw [hnc] at hf
    have hcond : (Space.global = Space.global ∧ (A.any fun x => x.ncLoads t.pc) = true) :=
      ⟨rfl, hnl⟩
    rw [ite_eq_left hcond] at hf
    obtain ⟨bs, -, he, hu⟩ := hf
    exact ⟨_, bs, he, Option.some.inj hu⟩

/-- The access of a two-element `.nc` load of `s32` indices through `base`. -/
def ncPair (base d0 d1 : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, scope := none, elem := .int .s 32,
    vec := 2, ext := .same, nc := true, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg base 64, off := 0 }, dsts := [some d0, some d1], srcs := [],
    mmio := false }

/-- The state after the first element of a two-element load: the second element is next, and the
first element's value is in the accumulator. -/
theorem afterLoad_first {t : TState} {d0 d1 : Nat} {bs : List (Option Byte)} {v : Value}
    (hs : t.sub = 0) (hacc : t.acc = []) (hrb : rebuild 3 bs = .ok v) :
    afterLoad t [d0, d1] bs = { t with sub := 1, acc := [v] } := by
  rw [afterLoad, hrb, hs, hacc]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceIte, List.nil_append]

/-- The state after the second element of a two-element load: the two destinations receive the
two elements and execution continues after the load. -/
theorem afterLoad_second {t : TState} {d0 d1 : Nat} {bs : List (Option Byte)} {v v0 : Value}
    (hs : t.sub = 1) (hacc : t.acc = [v0]) (hrb : rebuild 3 bs = .ok v) :
    afterLoad t [d0, d1] bs =
      { setRegs t [d0, d1] (t.acc ++ [v]) with pc := t.pc + 1, sub := 0, acc := [] } := by
  rw [afterLoad, hrb, hs, hacc]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte]

/-! ## The sites' steps

A site's step is its event's template from the state's facts, the local instructions the event is
followed by, and the successor's facts. The two event-only sites come first: the named barrier,
whose arrival ends the role, and the first element of a two-element pair load, which writes no
register and leaves the accumulator holding the element it read. -/

/-- **The named barrier's step**: `barrier.sync 12, 384` over the whole CTA ends the role. -/
theorem step_barrier {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} (hd : d.site = .barrier)
    {t u : TState} {e : Event} {ins : Instr} (hat : AtD P L g d t) (_hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step P L g d u e := by
  have hpc : d.site.pc = 2585 := by rw [hd]; rfl
  rw [hpc] at hc
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_13)
  rw [hpc] at hf
  have h659 : t.regs 659 = some (b32 12) := AtD.reg hat (by rw [hpc]; decide +kernel)
  have h660 : t.regs 660 = some (b32 384) := AtD.reg hat (by rw [hpc]; decide +kernel)
  have h12 : readBits L g t 32 (.reg 659) = .ok (BitVec.ofNat 64 12) :=
    readBits_b32 h659 (by decide)
  have h384 : readBits L g t 32 (.reg 660) = .ok (BitVec.ofNat 64 384) :=
    readBits_b32 h660 (by decide)
  have hev : eventTmpl asms L g t (.barSyncN (.reg 659) (.reg 660) false) =
      .bar 12 (PTX.next t) none .sync := by
    simp only [eventTmpl, barTmpl, h12, h384, BitVec.toNat_ofNat,
      show (12 : Nat) < 2 ^ 64 by omega, show (384 : Nat) < 2 ^ 64 by omega, Nat.mod_eq_of_lt,
      show ¬ (16 ≤ 12) by omega, ↓reduceIte, show (384 : Nat) % 32 = 0 by decide, hpre.block,
      show (BarMode.sync = BarMode.arrive) = False by decide, false_implies, true_and, or_true,
      reduceCtorEq]
  rw [hev] at hf
  obtain ⟨he, -⟩ := hf
  refine Or.inl (Or.inl ?_)
  simp only [next, nextSite, he, hd]

/-! ## The length loads

The role's first two events are the row's runtime lengths: `Assumption.ncReadOnly` fixes the
bytes of the `ld.global.nc` at pcs 2360 and 2365 to the row's lengths. The main-cache load
continues to the extra-cache load when that parameter pointer is present and otherwise takes
the null branch at pc 2362 into the pre-loop pair arithmetic (`pairTail`). `LaunchTest` ties
the pointer *words* the branch tests to the parameters' `Option`s; the two length steps take it
as a launch fact, as the role's entry run does. -/

/-- The main-cache length load's access: an `s32` word through `%rd3023` into `%r2968`. -/
abbrev ncLenOrig : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
    addr := { base := .reg 3023 64, off := 0 }, dsts := [some 2968] }

/-- The extra-cache length load's access: an `s32` word through `%rd3025` into `%r2969`. -/
abbrev ncLenExtra : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
    addr := { base := .reg 3025 64, off := 0 }, dsts := [some 2969] }

/-- **A scalar `.nc` load's continuation**: after the bytes rebuild to the successor table's
value of the destination, the thread is at the next instruction with the successor's facts. -/
theorem at_afterLoad_table {t u : TState} {pc d : Nat} {v : Value} {val val' : Nat → Value}
    (h : At t pc (factsFrom (preLive pc) val))
    (hu : u = { setReg t d v with pc := t.pc + 1, sub := 0, acc := [] })
    (hv : val' d = v)
    (heq : ∀ r ∈ preLive (pc + 1), r ≠ d → val' r = val r)
    (hl : ∀ r ∈ preLive (pc + 1), r = d ∨ r ∈ preLive pc) :
    At u (pc + 1) (factsFrom (preLive (pc + 1)) val') := by
  obtain ⟨hpc, -, -, hf, hholds⟩ := h
  subst hu
  refine ⟨?_, rfl, rfl, ?_, ?_⟩
  · simp [hpc]
  · simpa [setReg] using hf
  · refine holds_of_pointwise fun r hr => ?_
    by_cases hrd : r = d
    · subst hrd
      simp only [setReg, Function.update_self, hv]
    · simp only [setReg, Function.update_of_ne hrd]
      rw [heq r hr hrd]
      rcases hl r hr with h' | h'
      · exact absurd h' hrd
      · exact holds_mem hholds (mem_factsFrom h')

/-- A concrete state at a site's own program counter with its live facts is a concrete state of
the abstract state, when the site is at an instruction boundary with an empty accumulator (as
every site of this role is). -/
theorem atD_of_liveFacts {g : Nat} {d : D} {t : TState} {pc : Nat} (hpc : d.site.pc = pc)
    (hsub : d.site.sub = 0) (hacc : accOf d = [])
    (h : At t pc (factsFrom (preLive pc) (valueOf P L g d))) : AtD P L g d t := by
  obtain ⟨hpc', hsub', hacc', hf, hholds⟩ := h
  refine ⟨?_, ?_, ?_, hf, ?_⟩
  · rw [hpc]; exact hpc'
  · rw [hsub]; exact hsub'
  · rw [hacc]; exact hacc'
  · rw [facts_eq_liveFacts (d := d) (by rfl), hpc]
    exact hholds

/-- The live registers of the main-cache length load's continuation and of the load's site. -/
theorem preLive_2361_sub : ∀ r ∈ preLive 2361, r = 2968 ∨ r ∈ preLive 2360 := by
  have h1 : preLive 2361 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
    499, 500, 501, 502, 2968, 2969, 3010, 3011, 3012] := by decide +kernel
  have h2 : preLive 2360 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
    499, 500, 501, 502, 2969, 3010, 3011, 3012, 3023] := by decide +kernel
  intro r hr
  rw [h1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [h2]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The live registers of the extra-cache length load's continuation and of the load's site. -/
theorem preLive_2366_sub : ∀ r ∈ preLive 2366, r = 2969 ∨ r ∈ preLive 2365 := by
  have h1 : preLive 2366 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
    499, 500, 501, 502, 2968, 2969, 3011, 3012] := by decide +kernel
  have h2 : preLive 2365 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
    499, 500, 501, 502, 2968, 3011, 3012, 3025] := by decide +kernel
  intro r hr
  rw [h1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [h2]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem length_continue_inv {g : Nat} {d : D} {s : Site} (h : Inv P L g d)
    (hd : d.site = .lenOrig ∨ d.site = .lenExtra) (hs : s = .lenExtra ∨ s = .pair false true false)
    : Inv P L g { d with site := s } := by
  have hne : d.site ≠ .barrier := by rcases hd with hd | hd <;> simp [hd]
  have hz : d.block = 0 := h.blockZero hd
  refine ⟨h.phase, h.par, fun _ => h.phase_block hne, fun _ => h.par_block hne,
    fun _ => hz, h.len0, h.len1, h.block, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => hz, ?_⟩
  · intro hm
    rw [show ({ d with site := s } : D).block = 0 from hz]
    exact numOrigBlocks_pos d.len0
  all_goals rcases hs with rfl | rfl <;> simp [Site.extra, Site.hasPair, Site.inBody, pairInvariant]

private theorem lenOrig_after_branch {mem0 : Mem0} {g : Nat} {d : D} {u : TState} {e : Event}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hlt : LaunchTest P L g) (hinv : Inv P L g d)
    (hd : d.site = .lenOrig)
    (hn : next P L g d e = some (some
      { d with site := if P.extraTopkLenBase.isSome then .lenExtra else .pair false true false }))
    (hu : At u 2361 (liveFacts P L g d 2361)) : Step P L g d u e := by
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 u = some t1 ∧
      At t1 2362 ((16, .pred (Thread.ptrIsNull L 144)) :: liveFacts P L g d 2362) := by
    seg_fp hu using (simp only [Thread.ptrIsNull, Option.getD_some])
  obtain ⟨t2, hr2, h2⟩ := bra_at (pc := 2362) (target := 2366) (p := 16)
    (pick := Thread.ptrIsNull L 144) Flow.code_2362 h1 (by simp) (by decide) (by decide)
  cases hm : P.extraTopkLenBase with
  | none =>
    let d' := { d with site := Site.pair false true false }
    have hptr : Thread.ptrIsNull L 144 = true := by rw [hlt.ptrExtra, hm]; rfl
    rw [hptr] at h2
    simp only [ite_true] at h2
    have h2' : At t2 2366 (liveFacts P L g d 2366) := at_of_cons h2 (by lit_mem)
    have hlen : d.len1 = P.extra_topk := hinv.len1.trans (extraTopkLen_eq_extraTopk hpre hm hbatch)
    have hpair : At t2 2366 (liveFacts P L g d' 2366) := by
      apply at_congr h2'
      intro r hr
      rw [show preLive 2366 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
          499, 500, 501, 502, 2968, 2969, 3011, 3012] from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | rfl
        | (change b32 (len1Reg P d) = b32 (len1Reg P d')
           rw [len1Reg_lenOrig hd]
           exact congrArg b32 hlen.symm)
    have hlen0 : d'.len0 ≤ P.topk := by
      change d.len0 ≤ _
      rw [hinv.len0]
      exact topkLen_le hpre hbatch
    have hlen1 : d'.len1 ≤ P.extra_topk := by
      change d.len1 ≤ _
      rw [hlen]
    have hpad : origPadded d'.len0 + ceilToMultiple d'.len1 topkBlock < 2 ^ 31 := by
      change origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31
      rw [hinv.len0, hinv.len1]
      exact hpre.paddedRange _ hbatch
    obtain ⟨t3, hr3, h3⟩ := pairTail hpre (d := d') rfl hlen0 hlen1 hpad hpair
    have ha : (code P L g).AtD d' t3 := atD_code.mpr
      (atD_of_liveFacts (d := d') (pc := 2403) rfl rfl rfl h3)
    refine .inl (.inr ⟨d', t3, ?_, (run_rtg (run_comp hr1 hr2)).trans hr3, ha,
      length_continue_inv hinv (.inl hd) (.inr rfl)⟩)
    simpa [hm, d'] using hn
  | some base =>
    let d' := { d with site := Site.lenExtra }
    have hptr : Thread.ptrIsNull L 144 = false := by rw [hlt.ptrExtra, hm]; rfl
    rw [hptr] at h2
    simp only [Bool.false_eq_true, ite_false] at h2
    have h2' : At t2 2363 (liveFacts P L g d 2363) := at_of_cons h2 (by lit_mem)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 2365 (liveFacts P L g d' 2365) := by
      seg_fp h2' using idx_bits
    have ha : (code P L g).AtD d' t3 := atD_code.mpr
      (atD_of_liveFacts (d := d') (pc := 2365) rfl rfl rfl h3)
    refine .inl (.inr ⟨d', t3, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3), ha,
      length_continue_inv hinv (.inl hd) (.inl rfl)⟩)
    simpa [hm, d'] using hn

/-- The main-cache length read, followed by the extra read or the padded main-cache loop. -/
theorem step_lenOrig {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (hlt : LaunchTest P L g) {d : D} (hd : d.site = .lenOrig) {t u : TState} {e : Event}
    {ins : Instr} (hat : AtD P L g d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step P L g d u e := by
  have hpc : d.site.pc = 2360 := by rw [hd]; rfl
  have htp : t.pc = 2360 := hat.1.trans hpc
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2360)
  rw [← htp] at hf
  obtain ⟨loc, bs, he, hu⟩ := fires_nc_load (a := ncLenOrig) rfl rfl rfl rfl rfl rfl
    (by rw [htp]; exact asms_ncLoads_2360) hf
  rw [htp] at he
  rcases hrb : rebuild 3 bs with f | v
  · exact .inl (.inl (by simp [next, nextSite, hd, he, hrb]))
  by_cases hv : v = b32 (P.topkLen (eOf L g))
  · subst v
    have hn : next P L g d e = some (some
        { d with
          site := if P.extraTopkLenBase.isSome then .lenExtra else .pair false true false }) := by
      simp [next, nextSite, hd, he, hrb, ← hinv.len0, ← hinv.len1]
    have ht : At t 2360 (liveFacts P L g d 2360) := by
      refine ⟨htp, ?_, ?_, hat.2.2.2.1, ?_⟩
      · simpa [hd, Site.sub] using hat.2.1
      · simpa [accOf, hd] using hat.2.2.1
      · have hp : d.site.pendingRegs = [] := rfl
        have h := hat.2.2.2.2
        rw [facts_eq_liveFacts hp, liveFacts, hpc] at h
        exact h
    have hu' : u = { setReg t 2968 (b32 (P.topkLen (eOf L g))) with
        pc := t.pc + 1, sub := 0, acc := [] } :=
      hu.trans (afterLoad_ok (d := 2968) ht.2.1 ht.2.2.1 hrb)
    have hvalue : valueOf P L g d 2968 = b32 (P.topkLen (eOf L g)) := by
      change b32 d.len0 = _
      rw [hinv.len0]
    have hau : At u 2361 (liveFacts P L g d 2361) :=
      at_afterLoad_table ht hu' hvalue (fun _ _ _ => rfl) preLive_2361_sub
    exact lenOrig_after_branch hpre hbatch hlt hinv hd hn hau
  · exact .inl (.inl (by simp [next, nextSite, hd, he, hrb, hv]))

/-- The index role's main-cache length site. -/
theorem stepAt_lenOrig {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (hlt : LaunchTest P L g) (d : D) (hd : d.site = .lenOrig) :
    (code P L g).StepAt d :=
  stepAt_of P L g d (fun _ ht => step_lenOrig hpre hbatch hlt hd (atD_code.mp ht))

/-- The extra length load moves the role to the first main-cache pair, after computing both
padded counts and the pair address. -/
theorem step_lenExtra {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) {d : D}
    (hd : d.site = .lenExtra) {t u : TState} {e : Event} {ins : Instr} (hat : AtD P L g d t)
    (hinv : Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step P L g d u e := by
  have hpc : d.site.pc = 2365 := by rw [hd]; rfl
  have htp : t.pc = 2365 := hat.1.trans hpc
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2365)
  rw [← htp] at hf
  obtain ⟨loc, bs, he, hu⟩ := fires_nc_load (a := ncLenExtra) rfl rfl rfl rfl rfl rfl
    (by rw [htp]; exact asms_ncLoads_2365) hf
  rw [htp] at he
  rcases hrb : rebuild 3 bs with f | v
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb]))
  by_cases hv : v = b32 (P.extraTopkLen (eOf L g))
  · subst v
    let d' := { d with site := Site.pair false true false }
    have hnext : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, he, hrb, d', hinv.len1]
    have ht : At t 2365 (factsFrom (preLive 2365) (valueOf P L g d)) := by
      refine ⟨htp, ?_, ?_, hat.2.2.2.1, ?_⟩
      · simpa [hd, Site.sub] using hat.2.1
      · simpa [accOf, hd] using hat.2.2.1
      · have hp : d.site.pendingRegs = [] := rfl
        have h := hat.2.2.2.2
        rw [facts_eq_liveFacts hp, liveFacts, hpc] at h
        exact h
    have hu' : u = { setReg t 2969 (b32 (P.extraTopkLen (eOf L g))) with
        pc := t.pc + 1, sub := 0, acc := [] } :=
      hu.trans (afterLoad_ok (d := 2969) ht.2.1 ht.2.2.1 hrb)
    have heq : ∀ r ∈ preLive 2366, r ≠ 2969 → valueOf P L g d' r = valueOf P L g d r := by
      have hl : preLive 2366 = [460, 466, 490, 491, 492, 493, 494, 495, 496, 497, 498,
          499, 500, 501, 502, 2968, 2969, 3011, 3012] := by decide +kernel
      intro r hr hne
      rw [hl] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hne
    have hvalue : valueOf P L g d' 2969 = b32 (P.extraTopkLen (eOf L g)) := by
      change b32 d.len1 = _
      rw [hinv.len1]
    have hau : At u 2366 (liveFacts P L g d' 2366) :=
      at_afterLoad_table ht hu' hvalue heq preLive_2366_sub
    have hlen0 : d'.len0 ≤ P.topk := by
      change d.len0 ≤ P.topk
      rw [hinv.len0]
      exact topkLen_le hpre hbatch
    have hlen1 : d'.len1 ≤ P.extra_topk := by
      change d.len1 ≤ P.extra_topk
      rw [hinv.len1]
      exact extraLen_le hpre hbatch
    have hpad : origPadded d'.len0 + ceilToMultiple d'.len1 topkBlock < 2 ^ 31 := by
      change origPadded d.len0 + ceilToMultiple d.len1 topkBlock < 2 ^ 31
      rw [hinv.len0, hinv.len1]
      exact hpre.paddedRange _ hbatch
    obtain ⟨t', hr, ht'⟩ := pairTail hpre (d := d') rfl hlen0 hlen1 hpad hau
    have hat' : (code P L g).AtD d' t' := atD_code.mpr
      (atD_of_liveFacts (d := d') (pc := 2403) rfl rfl rfl ht')
    refine Or.inl (Or.inr ⟨d', t', hnext, hr, hat', ?_⟩)
    exact length_continue_inv hinv (.inr hd) (.inr rfl)
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hv]))

/-- The role's step at the extra-cache length load. -/
theorem stepAt_lenExtra {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (d : D) (hd : d.site = .lenExtra) :
    (code P L g).StepAt d :=
  stepAt_of P L g d (fun _ => step_lenExtra hpre hbatch hd)

/-- The state after the first element of an initial or prefetched index pair. -/
def afterPairLow (P : Params) (L : Launch) (g : Nat) (d : D) (extra first : Bool) : D :=
  { d with
    site := .pair extra first true
    i0 := if first then slotIdx P L g d.block (laneOf L g) 0 else d.i0
    n0 := if first then d.n0 else slotIdx P L g (d.block + 1) (laneOf L g) 0 }

private theorem facts_afterPairLow {g : Nat} {d : D} {extra first : Bool}
    (hd : d.site = .pair extra first false) :
    facts P L g (afterPairLow P L g d extra first) = facts P L g d := by
  have hp : (afterPairLow P L g d extra first).site.pc = d.site.pc := by
    rw [hd]
    cases extra <;> cases first <;> rfl
  rw [facts_eq_liveFacts (d := afterPairLow P L g d extra first) rfl,
    facts_eq_liveFacts (d := d) rfl, liveFacts, liveFacts, hp]
  let preserved := [456, 466, 490, 491, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505,
    506, 509, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2977, 2978, 2979, 2980, 2981,
    2982, 3011, 3013, 3014, 3033, 3041, 3043, 4029]
  have hcoverage : (preLive d.site.pc).all preserved.contains = true := by
    rw [hd]
    cases extra <;> cases first <;> decide +kernel
  apply List.map_congr_left
  intro r hr
  have hm := List.all_eq_true.mp hcoverage r hr
  simp only [List.contains_iff_mem, preserved, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (cases extra <;> cases first <;>
      idx_simp [afterPairLow, hd, Site.hasPair, countReg, len1Reg, Bool.false_eq_true,
        ↓reduceIte])

private theorem inv_afterPairLow {g : Nat} {d : D} {extra first : Bool}
    (hd : d.site = .pair extra first false) (h : Inv P L g d) :
    Inv P L g (afterPairLow P L g d extra first) := by
  have hne : d.site ≠ .barrier := by simp [hd]
  refine ⟨h.phase, h.par, fun _ => h.phase_block hne, fun _ => h.par_block hne,
    ?_, h.len0, h.len1, h.block, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases extra <;> cases first <;> simp_all [afterPairLow, h.firstBlock]
  · simpa [afterPairLow, hd, Site.extra] using h.tagMain
  · simpa [afterPairLow, hd, Site.extra] using h.tagExtra
  · cases first <;> simp_all [afterPairLow, Site.hasPair, h.slot0]
  · cases first
    · simpa [afterPairLow, Site.hasPair, hd] using h.slot1
    · simp [afterPairLow, Site.hasPair]
  · simp [afterPairLow, Site.inBody]
  · simp [afterPairLow, Site.inBody]
  · simp [afterPairLow]
  · cases extra <;> cases first <;> first
    | simp [pairInvariant, afterPairLow]; done
    | simpa [pairInvariant, afterPairLow, hd] using h.pairLoad

/-- The address and two destination registers of each pair load. -/
abbrev pairOperands : Bool → Bool → Nat × Nat × Nat
  | false, true => (3033, 2974, 2973)
  | false, false => (4029, 2976, 2975)
  | true, true => (3041, 2982, 2981)
  | true, false => (3043, 2984, 2983)

private theorem pair_opcode (extra first hi : Bool) :
    kernel.code[(Site.pair extra first hi).pc]? = some
      ⟨none, .mem (ncPair (pairOperands extra first).1
        (pairOperands extra first).2.1 (pairOperands extra first).2.2)⟩ := by
  cases extra <;> cases first
  · exact Flow.code_2429
  · exact Flow.code_2403
  · exact Flow.code_2517
  · exact Flow.code_2501

private theorem pair_nc_enabled (extra first hi : Bool) :
    asms.any (·.ncLoads (Site.pair extra first hi).pc) = true := by
  cases extra <;> cases first
  · exact asms_ncLoads_2429
  · exact asms_ncLoads_2403
  · exact asms_ncLoads_2517
  · exact asms_ncLoads_2501

/-- The first element of each vector load stays at the same instruction and saves the value
in the machine's accumulator. -/
theorem stepAt_pairLow {g : Nat} (d : D) {extra first : Bool}
    (hd : d.site = .pair extra first false) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hinv hc hf
  have hcode := pair_opcode extra first false
  rw [← hd] at hcode
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hAt : AtD P L g d t := atD_code.mp hat
  have hnc : asms.any (·.ncLoads t.pc) = true := by
    rw [hAt.1, hd]
    exact pair_nc_enabled extra first false
  rw [← hAt.1] at hf
  obtain ⟨loc, bs, he, hu⟩ := fires_nc_load (a := ncPair (pairOperands extra first).1
    (pairOperands extra first).2.1 (pairOperands extra first).2.2)
    rfl rfl rfl rfl rfl rfl hnc hf
  rcases hrb : rebuild 3 bs with f | v
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb]))
  by_cases hv : v = b32 (ipat (slotIdx P L g
      (if first then d.block else d.block + 1) (laneOf L g) 0))
  · subst v
    let d' := afterPairLow P L g d extra first
    have hn : next P L g d e = some (some d') := by
      change next P L g d e = _
      simp [next, nextSite, hd, he, hrb, d', afterPairLow]
    have hs : t.sub = 0 := by simpa [hd, Site.sub] using hAt.2.1
    have ha : t.acc = [] := by simpa [hd, accOf] using hAt.2.2.1
    have hu' := hu.trans (afterLoad_first (d0 := (pairOperands extra first).2.1)
      (d1 := (pairOperands extra first).2.2) hs ha hrb)
    have hGood : (code P L g).AtD d' u := by
      apply atD_code.mpr
      rw [hu']
      refine ⟨?_, ?_, ?_, hAt.2.2.2.1, ?_⟩
      · cases extra <;> cases first <;> simpa [d', afterPairLow, hd, Site.pc] using hAt.1
      · simp [d', afterPairLow, Site.sub]
      · cases first <;> simp [d', afterPairLow, accOf]
      · change Holds t.regs (facts P L g (afterPairLow P L g d extra first))
        rw [facts_afterPairLow hd]
        exact hAt.2.2.2.2
    exact Or.inl (Or.inr ⟨d', u, hn, .refl, hGood, inv_afterPairLow hd hinv⟩)
  · exact Or.inl (Or.inl (by simp [next, nextSite, hd, he, hrb, hv]))

/-! ## Completing a pair load -/

/-- The successor records the high index of the current or prefetched block. -/
def afterPairHigh (P : Params) (L : Launch) (g : Nat) (d : D) (extra first : Bool) : D :=
  if first then
    { d with site := afterPairFirst d extra, i1 := slotIdx P L g d.block (laneOf L g) 1 }
  else
    { d with site := .waitFree extra, n1 := slotIdx P L g (d.block + 1) (laneOf L g) 1 }

/-- The cache's last block and the row's last block are the two prefetch limits. -/
abbrev pairLimit (d : D) (extra : Bool) : Nat :=
  if extra then totalBlocks d.len0 d.len1 else numOrigBlocks d.len0

private theorem afterPairFirst_eq (d : D) (extra : Bool)
    (hb : d.block = if extra then numOrigBlocks d.len0 else 0) :
    afterPairFirst d extra = if d.block + 1 < pairLimit d extra
      then .pair extra false false else .waitFree extra := by
  cases extra
  · have h0 : d.block = 0 := hb
    simp [afterPairFirst, pairLimit, h0]
  · have h0 : d.block = numOrigBlocks d.len0 := hb
    simp [afterPairFirst, pairLimit, h0]

private theorem inv_afterPairHigh {g : Nat} {d : D} {extra first : Bool}
    (hd : d.site = .pair extra first true) (h : Inv P L g d) :
    Inv P L g (afterPairHigh P L g d extra first) := by
  have hne : d.site ≠ .barrier := by simp [hd]
  have htag : d.site.extra = some extra := by rw [hd]; rfl
  cases first
  · have hp : d.block + 1 < pairLimit d extra ∧
        d.n0 = slotIdx P L g (d.block + 1) (laneOf L g) 0 := by
      simpa only [pairInvariant, hd, Bool.false_eq_true, ↓reduceIte] using h.pairLoad
    simp only [afterPairHigh, Bool.false_eq_true, ↓reduceIte]
    have hpair : d.site.hasPair = true := by rw [hd]; rfl
    refine ⟨h.phase, h.par, fun _ => h.phase_block hne, fun _ => h.par_block hne,
      ?_, h.len0, h.len1, h.block, ?_, ?_, fun _ => h.slot0 hpair, fun _ => h.slot1 hpair,
      fun _ _ => hp.2, fun _ _ => rfl, ?_, trivial⟩
    · simp
    · exact fun ht => h.tagMain (htag.trans ht)
    · exact fun ht => h.tagExtra (htag.trans ht)
    · simp
  · have hi : d.i0 = slotIdx P L g d.block (laneOf L g) 0 := by
      cases extra
      · simpa [pairInvariant, hd] using h.pairLoad
      · have hp : d.block = numOrigBlocks d.len0 ∧
            d.i0 = slotIdx P L g d.block (laneOf L g) 0 := by
          simpa [pairInvariant, hd] using h.pairLoad
        exact hp.2
    have hb : d.block = if extra then numOrigBlocks d.len0 else 0 := by
      cases extra
      · exact h.firstBlock (.inr hd)
      · have hp : d.block = numOrigBlocks d.len0 ∧
            d.i0 = slotIdx P L g d.block (laneOf L g) 0 := by
          simpa [pairInvariant, hd] using h.pairLoad
        exact hp.1
    simp only [afterPairHigh, ↓reduceIte, afterPairFirst_eq d extra hb]
    by_cases hp : d.block + 1 < pairLimit d extra
    · rw [ite_eq_left hp]
      refine ⟨h.phase, h.par, fun _ => h.phase_block hne, fun _ => h.par_block hne,
        ?_, h.len0, h.len1, h.block, ?_, ?_, fun _ => hi, fun _ => rfl,
        ?_, ?_, ?_, ?_⟩
      · simp
      · exact fun ht => h.tagMain (htag.trans ht)
      · exact fun ht => h.tagExtra (htag.trans ht)
      · simp [Site.inBody]
      · simp [Site.inBody]
      · simp
      · exact ⟨hp, trivial⟩
    · rw [ite_eq_right hp]
      refine ⟨h.phase, h.par, fun _ => h.phase_block hne, fun _ => h.par_block hne,
        ?_, h.len0, h.len1, h.block, ?_, ?_, fun _ => hi, fun _ => rfl,
        ?_, ?_, ?_, trivial⟩
      · simp
      · exact fun ht => h.tagMain (htag.trans ht)
      · exact fun ht => h.tagExtra (htag.trans ht)
      · intro _ hlt
        exfalso
        apply hp
        cases extra <;> exact hlt
      · intro _ hlt
        exfalso
        apply hp
        cases extra <;> exact hlt
      · simp

/-- Both words are committed to the destination registers at the second sub-step. -/
abbrev loadedPairFacts (P : Params) (L : Launch) (g : Nat) (d : D) (extra first : Bool) :
    List (Nat × Value) :=
  ((pairOperands extra first).2.1, b32 (ipat (if first then d.i0 else d.n0))) ::
  ((pairOperands extra first).2.2, b32 (ipat (slotIdx P L g
    (if first then d.block else d.block + 1) (laneOf L g) 1))) :: facts P L g d

private theorem at_pair_write {g : Nat} {d : D} {extra first : Bool} {t u : TState}
    (h : AtD P L g d t) (hd : d.site = .pair extra first true)
    (hu : u = { setReg (setReg t (pairOperands extra first).2.1
        (b32 (ipat (if first then d.i0 else d.n0)))) (pairOperands extra first).2.2
        (b32 (ipat (slotIdx P L g (if first then d.block else d.block + 1) (laneOf L g) 1))) with
        pc := t.pc + 1, sub := 0, acc := [] }) :
    At u (d.site.pc + 1) (loadedPairFacts P L g d extra first) := by
  have hlo : ∀ p ∈ facts P L g d, p.1 ≠ (pairOperands extra first).2.1 := by
    rw [facts_eq_liveFacts rfl, liveFacts, hd]
    apply not_mem_factsFrom
    cases extra <;> cases first <;> decide +kernel
  have hhi : ∀ p ∈ facts P L g d, p.1 ≠ (pairOperands extra first).2.2 := by
    rw [facts_eq_liveFacts rfl, liveFacts, hd]
    apply not_mem_factsFrom
    cases extra <;> cases first <;> decide +kernel
  have hne : (pairOperands extra first).2.1 ≠ (pairOperands extra first).2.2 := by
    cases extra <;> cases first <;> decide
  rw [hu]
  refine ⟨by rw [h.1], rfl, rfl, h.2.2.2.1, ?_, ?_, ?_⟩
  · simp [setReg, Function.update_of_ne hne]
  · simp [setReg]
  · exact holds_update (holds_update h.2.2.2.2 hlo) hhi

/-- The high load either yields the expected pair with both registers set or leaves the
role's traced path. -/
theorem pairHigh_loaded {g : Nat} {d : D} {extra first : Bool} {t u : TState} {e : Event}
    {ins : Instr} (hd : d.site = .pair extra first true) (hat : AtD P L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    next P L g d e = some none ∨
      (next P L g d e = some (some (afterPairHigh P L g d extra first)) ∧
        At u (d.site.pc + 1) (loadedPairFacts P L g d extra first)) := by
  have hop := pair_opcode extra first true
  rw [← hd] at hop
  obtain rfl := Option.some.inj (hc.symm.trans hop)
  have hnc : asms.any (·.ncLoads t.pc) = true := by
    rw [hat.1, hd]
    exact pair_nc_enabled extra first true
  rw [← hat.1] at hf
  obtain ⟨loc, bs, he, hu⟩ := fires_nc_load (a := ncPair (pairOperands extra first).1
    (pairOperands extra first).2.1 (pairOperands extra first).2.2)
    rfl rfl rfl rfl rfl rfl hnc hf
  rcases hr : rebuild 3 bs with f | v
  · exact .inl (by simp [next, nextSite, hd, he, hr])
  by_cases hv : v = b32 (ipat (slotIdx P L g
      (if first then d.block else d.block + 1) (laneOf L g) 1))
  · subst v
    have hs : t.sub = 1 := by simpa [hd, Site.sub] using hat.2.1
    have ha : t.acc = [b32 (ipat (if first then d.i0 else d.n0))] := by
      cases first <;> simpa [hd, accOf] using hat.2.2.1
    have hnext : next P L g d e = some (some (afterPairHigh P L g d extra first)) := by
      simp [next, nextSite, hd, he, hr, afterPairHigh]
    have hload := afterLoad_second (d0 := (pairOperands extra first).2.1)
      (d1 := (pairOperands extra first).2.2) hs ha hr
    rw [ha] at hload
    exact .inr ⟨hnext, at_pair_write hat hd (hu.trans hload)⟩
  · exact .inl (by simp [next, nextSite, hd, he, hr, hv])
end

/-! ## Preparing the free-slot wait -/

private theorem intDiv_unsigned32 {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hpos : 0 < b) :
    intDiv .u 32 (truncBits 32 (BitVec.ofNat 64 a)) (truncBits 32 (BitVec.ofNat 64 b)) =
      .ok ((a / b : Nat) : Int) := by
  have ha' : a < 2 ^ 64 := by omega
  have hb' : b < 2 ^ 64 := by omega
  rw [truncBits_ofNat ha (by decide), truncBits_ofNat hb (by decide)]
  unfold intDiv
  simp only [intOf, reduceCtorEq, ↓reduceIte, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  simp [hpos.ne', not_lt_of_ge (Int.natCast_nonneg a), not_lt_of_ge (Int.natCast_nonneg b),
    Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg a)]
  rfl

private theorem uint32_bits {n : Nat} (hn : n < 2 ^ 32) :
    intBits 32 (n : Int) = BitVec.ofNat 64 n := by
  have h64 : n < 2 ^ 64 := by omega
  unfold intBits
  rw [show BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n by
    apply BitVec.eq_of_toNat_eq
    simp]
  exact truncBits_ofNat hn (by decide)

private theorem run_div_u32 {L : Launch} {g pc dst a b x y : Nat}
    {t : TState} {F : List (Nat × Value)}
    (hc : kernel.code[pc]? = some
      ⟨none, .int ⟨.div, .int .u 32, false, [some dst], [.reg a, .reg b]⟩⟩)
    (h : At t pc F) (ha : (a, b32 x) ∈ F) (hb : (b, b32 y) ∈ F)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hypos : 0 < y)
    (hnew : ∀ p ∈ F, p.1 ≠ dst)
    (hadd : pc ∉ paramAdds) (hprefetch : pc ∉ prefetchTensorMapSites)
    (hshared : pc ∉ Assumptions.sharedBitsSites) (hpeer : 474 ≤ pc)
    (hfree : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) ((dst, b32 (x / y)) :: F) := by
  have ha' := readBits_b32 (L := L) (g := g) (holds_mem h.2.2.2.2 ha) hx
  have hb' := readBits_b32 (L := L) (g := g) (holds_mem h.2.2.2.2 hb) hy
  have he := intDiv_unsigned32 hx hy hypos
  rw [truncBits_ofNat hx (by decide), truncBits_ofNat hy (by decide)] at he
  let op := (Op.int ⟨.div, .int .u 32, false, [some dst], [.reg a, .reg b]⟩)
  have hn : ∀ a' ∈ asms, a'.localRule L g t op = none :=
    Thread.asms_localRule_int (t := t)
      (by rw [h.1]; exact hadd) (by rw [h.1]; exact hprefetch) (by rw [h.1]; exact hshared)
      (Assumptions.peerPackRule_of_none (Assumptions.peerPack_none_of_outside
        (Or.inr (by rw [h.1]; exact hpeer))))
  have hquot := lt_of_le_of_lt (Nat.div_le_self x y) hx
  let t' := PTX.next (setReg t dst (b32 (x / y)))
  have hex : execLocalA asms L g t op = .ok t' := by
    rw [Assumption.SegFreePc.exec hfree h.1, execLocalRule_of_none hn]
    dsimp only [op]
    rw [execLocal_int (by rfl)]
    simp [execInt, intResult, DType.intLanes?, DType.width, ha', hb', he, t', b32,
      bind, Except.bind, pure, Except.pure]
    rw [← Int.natCast_ediv, uint32_bits hquot]
  exact ⟨t', run_local hc rfl h hex, At.set h hnew⟩

private theorem ipat_bound (i : Int) : ipat i < 2 ^ 32 := by
  unfold ipat i32Bits
  have hpos : (0 : Int) < 2 ^ 32 := by decide
  have h := Int.emod_lt_of_pos i hpos
  omega

private theorem index_remainder {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    Value.bits 32
      (truncBits 32
        (truncBits 32 (BitVec.ofNat 64 a) -
         truncBits 32 (truncBits 32
           (truncBits 32 (BitVec.ofNat 64 (a / b)) * truncBits 32 (BitVec.ofNat 64 b))))) =
      b32 (a % b) := by
  have h := Nat.div_add_mod a b
  have hdiv : a / b < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) ha
  have hprod : a / b * b ≤ a := by rw [Nat.mul_comm]; omega
  have ht : a / b * b + a % b = a := by rw [Nat.mul_comm]; exact h
  have hprod32 : a / b * b < 2 ^ 32 := lt_of_le_of_lt hprod ha
  rw [truncBits_ofNat ha (by decide), truncBits_ofNat hdiv (by decide),
    truncBits_ofNat hb (by decide), nf_mul,
    truncBits_ofNat hprod32 (by decide), truncBits_ofNat hprod32 (by decide)]
  norm_bits

private theorem live_mem {P : Params} {L : Launch} {g pc r : Nat} {d : D} {v : Value}
    (hr : r ∈ preLive pc) (hv : valueOf P L g d r = v) :
    (r, v) ∈ liveFacts P L g d pc := by
  rw [← hv]
  exact mem_factsFrom hr

private theorem main_page_bounds {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    (hpre : Pre P L mem0) (_hbatch : eOf L g < P.b) (_hi : Inv P L g d)
    (_hd : d.site = .waitFree false) : 0 < P.page ∧ P.page < 2 ^ 32 := by
  have hf := hpre.pageFits
  have hs := hpre.blockStrideRange
  exact ⟨hpre.pagePos, by omega⟩

private theorem extra_page_bounds {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hi : Inv P L g d)
    (hd : d.site = .waitFree true) : 0 < P.extraPage ∧ P.extraPage < 2 ^ 32 := by
  have htag := hi.tagExtra (by rw [hd]; rfl)
  have hpos : 0 < d.len1 := by
    by_contra hzero
    have hlen : d.len1 = 0 := by omega
    have hblk := hi.block
    rw [hlen] at hblk
    change d.block < numOrigBlocks d.len0 at hblk
    omega
  have hbudget : 0 < P.extra_topk := by
    have hb := extraLen_le hpre hbatch
    rw [hi.len1] at hpos
    omega
  obtain ⟨hp, _, _, hf⟩ := hpre.extraPos hbudget
  have hs := hpre.extraBlockStrideRange
  exact ⟨hp, by omega⟩

private theorem flip_wait_parity (p : Nat) (hp : p < 2) :
    Value.bits 32
      (truncBits 32 (truncBits 32 (truncBits 16
        (truncBits 16 (BitVec.ofNat 64 p) ^^^ truncBits 16 (BitVec.ofInt 64 1)))) &&&
        truncBits 32 (BitVec.ofInt 64 255)) = b32 (1 - p) := by
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> decide

private theorem add_negative_word {a n : Nat} (ha : a < 2 ^ 32) (hn : n ≤ a) :
    Value.bits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) +
        truncBits 32 (BitVec.ofInt 64 (-(n : Int))))) = b32 (a - n) := by
  rw [truncBits_ofNat ha (by decide)]
  nf_simp
  omega

/-- The body computes both page quotients and remainders before polling the free barrier. -/
macro "prove_wait_operands " name:ident "," extra:term "," start:num "," pc1:num ","
    pc2:num "," parity:num "," poll:num "," page:ident "," off:num "," param:ident ","
    bounds:term "," x:num "," y:num "," pageReg:num "," code1:term "," code2:term : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState}
      (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hd : d.site = Site.waitFree $extra)
      (hi : Inv P L g d) (hat : At t $start (liveFacts P L g d $start)) :
      ∃ t', run kernel asms L g ($poll - $start) t = some t' ∧
        At t' $poll (liveFacts P L g d $poll) := by
    obtain ⟨hpos, hp⟩ := $bounds hpre hbatch hi hd
    have hw : Thread.paramWord L $off 4 = P.$page :=
      (Thread.paramWord_four (fun k hk => hpre.$param k hk)).trans (Nat.mod_eq_of_lt hp)
    have hx := ipat_bound d.i0
    have hy := ipat_bound d.i1
    have hpar := hi.par
    have hphase := hi.phase
    have hb := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have hPad := hpre.paddedRange _ hbatch
    rw [← hi.len0, ← hi.len1] at hPad
    have htotal : totalBlocks d.len0 d.len1 * 64 ≤
        origPadded d.len0 + ceilToMultiple d.len1 topkBlock := by
      rw [← totalBlocks_eq_counts]
      exact Nat.div_mul_le_self _ _
    have hblock := hi.block
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    have hWord : 64 + 2 * laneOf L g + 64 * (d.block - numOrigBlocks d.len0) < 2 ^ 32 := by
      omega
    have hnegative := add_negative_word (n := 64) hWord (by omega)
    rw [show (64 + 2 * laneOf L g + 64 * (d.block - numOrigBlocks d.len0)) - 64 =
      2 * laneOf L g + 64 * (d.block - numOrigBlocks d.len0) by omega] at hnegative
    obtain ⟨t1, r1, h1⟩ : ∃ t1, run kernel asms L g 2 t = some t1 ∧
        At t1 $pc1 (liveFacts P L g d $pc1) := by
      seg_fp hat using
        all_goals (try idx_values)
        all_goals first
          | (show Value.pred _ = _
             nf_simp [PTX.compare, Value.pred.injEq]
             rw [show (tidOf L g % 4 != 0) = decide (tidOf L g % 4 ≠ 0) from rfl,
               decide_eq_decide]
             omega)
          | norm_bits
          | exact hnegative
    have hi0 : ($x, b32 (ipat d.i0)) ∈ liveFacts P L g d $pc1 :=
      live_mem (by decide +kernel) (by idx_simp [hd, Site.hasPair, ite_true])
    have hp0 : ($pageReg, b32 P.$page) ∈ liveFacts P L g d $pc1 :=
      live_mem (by decide +kernel) (by idx_simp [hw])
    obtain ⟨t2, r2, h2⟩ := run_div_u32 (L := L) (g := g) $code1 h1 hi0 hp0 hx hp hpos
      (not_mem_factsFrom (by decide +kernel)) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨t3, r3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 $pc2 (liveFacts P L g d $pc2) := by
      seg_fp h2 using
        all_goals idx_simp [hd, Site.hasPair, hw]
        all_goals exact index_remainder hx hp
    have hi1 : ($y, b32 (ipat d.i1)) ∈ liveFacts P L g d $pc2 :=
      live_mem (by decide +kernel) (by idx_simp [hd, Site.hasPair, ite_true])
    have hp1 : ($pageReg, b32 P.$page) ∈ liveFacts P L g d $pc2 :=
      live_mem (by decide +kernel) (by idx_simp [hw])
    obtain ⟨t4, r4, h4⟩ := run_div_u32 (L := L) (g := g) $code2 h3 hi1 hp1 hy hp hpos
      (not_mem_factsFrom (by decide +kernel)) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨t5, r5, h5⟩ : ∃ t5, run kernel asms L g 2 t4 = some t5 ∧
        At t5 $parity (liveFacts P L g d $parity) := by
      seg_fp h4 using
        all_goals idx_simp [hd, Site.hasPair, hw]
        all_goals exact index_remainder hy hp
    obtain ⟨t6, r6, h6⟩ : ∃ t6, run kernel asms L g 8 t5 = some t6 ∧
        At t6 $poll (liveFacts P L g d $poll) := by
      seg_fp h5 using
        all_goals (try idx_values)
        all_goals first
          | norm_bits [sb, freeOff]
          | exact flip_wait_parity d.par hpar
    exact ⟨t6, run_comp (run_comp (run_comp r1 r2) (run_comp r3 r4)) (run_comp r5 r6), h6⟩)

prove_wait_operands prepare_wait_main, false, 2430, 2432, 2435, 2438, 2446, page, 36,
  paramPage, main_page_bounds, 2974, 2973, 497,
  Flow.code_2432, Flow.code_2435

prove_wait_operands prepare_wait_extra, true, 2518, 2520, 2523, 2526, 2534, extraPage, 116,
  paramExtraPage, extra_page_bounds, 2982, 2981, 502,
  Flow.code_2520, Flow.code_2523

private theorem after_pair_table {t : TState} {pc low high : Nat} {v0 v1 : Value}
    {F : List (Nat × Value)} {val : Nat → Value}
    (h : At t pc ((low, v0) :: (high, v1) :: F))
    (h0 : val low = v0) (h1 : val high = v1)
    (hframe : ∀ r ∈ preLive pc, r ≠ low → r ≠ high → (r, val r) ∈ F) :
    At t pc (factsFrom (preLive pc) val) := by
  apply h.mono
  apply holds_of_pointwise
  intro r hr
  apply holds_mem h.2.2.2.2
  by_cases hlo : r = low
  · subst r
    rw [h0]
    exact List.mem_cons_self
  by_cases hhi : r = high
  · subst r
    rw [h1]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hframe r hr hlo hhi))

private theorem prefetch_raw_main {P : Params} {L : Launch} {g : Nat} {d : D} {u : TState}
    (hd : d.site = .pair false false true) (hi : Inv P L g d)
    (hu : At u (d.site.pc + 1) (loadedPairFacts P L g d false false)) :
    At u 2430 (liveFacts P L g (afterPairHigh P L g d false false) 2430) := by
  have hnext : d.block + 1 < numOrigBlocks d.len0 := by
    have hpair := hi.pairLoad
    simp only [pairInvariant, hd, Bool.false_eq_true, ↓reduceIte] at hpair
    exact hpair.1
  rw [hd] at hu
  apply after_pair_table hu
  · idx_simp [afterPairHigh, hnext, Bool.false_eq_true, ↓reduceIte]
  · idx_simp [afterPairHigh, hnext, Bool.false_eq_true, ↓reduceIte]
  · intro r hr hlo hhi
    change r ∈ preLive 2430 at hr
    rw [show preLive 2430 = [456, 491, 496, 497, 498, 500, 501, 502, 503, 504, 505, 506, 2968, 2969,
      2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2980, 3014, 4029]
      from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hlo
      | exact absurd rfl hhi
      | (rw [facts_eq_liveFacts rfl, hd]
         apply live_mem (by decide +kernel)
         idx_simp [hd, afterPairHigh, Bool.false_eq_true, ↓reduceIte, len1Reg,
           countReg, Site.hasPair, ite_true])

private theorem prefetch_raw_extra {P : Params} {L : Launch} {g : Nat} {d : D} {u : TState}
    (hd : d.site = .pair true false true) (hi : Inv P L g d)
    (hu : At u (d.site.pc + 1) (loadedPairFacts P L g d true false)) :
    At u 2518 (liveFacts P L g (afterPairHigh P L g d true false) 2518) := by
  have hnext : d.block + 1 < totalBlocks d.len0 d.len1 := by
    have hpair := hi.pairLoad
    simp only [pairInvariant, hd, Bool.false_eq_true, ↓reduceIte] at hpair
    exact hpair.1
  rw [hd] at hu
  apply after_pair_table hu
  · idx_simp [afterPairHigh, hnext, Bool.false_eq_true, ↓reduceIte]
  · idx_simp [afterPairHigh, hnext, Bool.false_eq_true, ↓reduceIte]
  · intro r hr hlo hhi
    change r ∈ preLive 2518 at hr
    rw [show preLive 2518 = [456, 498, 500, 501, 502, 503, 505, 509, 2969, 2977, 2978, 2979,
      2980, 2981, 2982, 2983, 2984, 3014] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hlo
      | exact absurd rfl hhi
      | (rw [facts_eq_liveFacts rfl, hd]
         apply live_mem (by decide +kernel)
         idx_simp [hd, afterPairHigh, Bool.false_eq_true, ↓reduceIte, len1Reg,
           countReg, Site.hasPair, ite_true])

/-- Completing a look-ahead load computes the two page offsets and reaches the free barrier. -/
theorem stepAt_prefetchedPairHigh {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (d : D) {extra : Bool}
    (hd : d.site = .pair extra false true) : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  rcases pairHigh_loaded hd (atD_code.mp hat) hc hf with hn | ⟨hn, hload⟩
  · exact .inl (.inl hn)
  have hi' := inv_afterPairHigh hd hi
  cases extra
  · let d' := afterPairHigh P L g d false false
    have hhead := prefetch_raw_main hd hi hload
    obtain ⟨t', hr, hf⟩ := prepare_wait_main hpre hbatch rfl hi' hhead
    have ha := atD_of_liveFacts (d := d') (pc := 2446) rfl rfl rfl hf
    exact .inl (.inr ⟨d', t', hn, run_rtg hr, atD_code.mpr ha, hi'⟩)
  · let d' := afterPairHigh P L g d true false
    have hhead := prefetch_raw_extra hd hi hload
    obtain ⟨t', hr, hf⟩ := prepare_wait_extra hpre hbatch rfl hi' hhead
    have ha := atD_of_liveFacts (d := d') (pc := 2534) rfl rfl rfl hf
    exact .inl (.inr ⟨d', t', hn, run_rtg hr, atD_code.mpr ha, hi'⟩)

/-! ## Preparing the first block of a cache -/

private theorem magic_528 (n : Nat) (h : n < 2 ^ 31) (hm : n % 528 = 0) :
    n * 1041204193 / 4294967296 / 128 = n / 528 := by
  have hdiv : 528 * (n / 528) = n := by
    have hd := Nat.div_add_mod n 528
    omega
  rw [Nat.div_div_eq_div_mul]
  change n * 1041204193 / 549755813888 = n / 528
  apply Nat.div_eq_of_lt_le <;> omega

/-- Positive signed stride words use the upper half of the constant product. -/
private theorem mulhi_stride_value {n : Nat} (hn : n < 2 ^ 31) :
    Value.bits 32
      (truncBits 32 (BitVec.ofInt 64
        ((toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) *
          toSigned 32 (truncBits 32 (BitVec.ofInt 64 1041204193))) / 2 ^ 32))) =
      b32 (n * 1041204193 / 4294967296) := by
  have hn32 : n < 2 ^ 32 := by omega
  have hmod : n % 2 ^ 32 = n := Nat.mod_eq_of_lt hn32
  have hs : toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
    have hlt : n % 2 ^ 32 < 2 ^ 31 := by rwa [hmod]
    rw [toSigned_b32 hlt, hmod]
  have hm : toSigned 32 (truncBits 32 (BitVec.ofInt 64 1041204193)) = 1041204193 := by
    decide
  rw [truncBits_ofNat hn32 (by decide), hs, hm]
  have hnat : (n : Int) * 1041204193 / 2 ^ 32 =
      ((n * 1041204193 / 4294967296 : Nat) : Int) := by
    rw [Int.natCast_ediv, Nat.cast_mul]
    norm_num
  rw [hnat]
  exact congrArg (Value.bits 32) (uint32_bits (by omega))

/-- Evaluate the two shifts and carry-dependent correction for a nonnegative stride. -/
private theorem stride_shift_value {n : Nat} (hn : n < 2 ^ 31) :
    (toSigned 32 (BitVec.ofNat 64 n) / 2 ^ min 7 32 % 18446744073709551616).toNat %
      4294967296 = n / 128 := by
  exact shr_s_val (s := 7) hn (by decide)

/-- The two signed-stride sequences both divide an integral number of 528-byte rows. -/
macro "prove_stride_count " name:ident "," first:num "," second:num "," add:num "," stop:num ","
    high:num "," sign:num "," quot:num "," word:ident "," nOff:num "," nParam:ident ","
    range:ident : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hmod : P.$word % 528 = 0)
      (h : At t $first (liveFacts P L g d $first)) :
      ∃ t', run kernel asms L g 4 t = some t' ∧ At t' $stop (liveFacts P L g d $stop) := by
    have hn : P.$word < 2 ^ 31 := hpre.$range
    have hn32 : P.$word < 2 ^ 32 := by omega
    have hw : Thread.paramWord L $nOff 4 = P.$word :=
      (Thread.paramWord_four (fun k hk => hpre.$nParam k hk)).trans (Nat.mod_eq_of_lt hn32)
    have hhi : P.$word * 1041204193 / 4294967296 < 2 ^ 31 := by omega
    have hquot := magic_528 P.$word hn hmod
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
        At t1 $second (($high, b32 (P.$word * 1041204193 / 4294967296)) ::
          liveFacts P L g d $first) := by
      seg_fp h using
        all_goals idx_simp [hw]
        all_goals exact mulhi_stride_value hn
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 t1 = some t2 ∧
        At t2 $add (($sign, b32 0) ::
          ($quot, b32 (P.$word * 1041204193 / 4294967296 / 128)) ::
          liveFacts P L g d $first) := by
      have hhi32 : P.$word * 1041204193 / 4294967296 < 4294967296 := by omega
      have hhi31 : P.$word * 1041204193 / 4294967296 < 2147483648 := hhi
      have hm := Nat.mod_eq_of_lt hhi32
      have hz := Nat.div_eq_of_lt hhi31
      have hs := stride_shift_value hhi
      have hm64 := Nat.mod_eq_of_lt (show
        P.$word * 1041204193 / 4294967296 < 18446744073709551616 by omega)
      seg_fp h1 using (all_goals nf_simp [hm, hm64, hz, hs])
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 $stop (liveFacts P L g d $stop) := by
      have ha : P.$word / 528 < 4294967296 := by
        have := Nat.div_le_self P.$word 528
        omega
      have ha64 : P.$word / 528 < 18446744073709551616 := by omega
      seg_fp h2 using
        all_goals idx_simp [bytesPerToken]
        all_goals
          rw [hquot]
          nf_simp [Nat.add_zero, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha64]
    exact ⟨t3, run_comp (run_comp hr1 hr2) hr3, h3⟩)

prove_stride_count prepare_stride_main, 2410, 2411, 2413, 2414, 582, 583, 584, blockStride, 164,
  paramStrideKvBlock, blockStrideRange

prove_stride_count prepare_stride_extra, 2504, 2505, 2507, 2508, 620, 621, 622, extraBlockStride,
  200, paramStrideExtraKvBlock, extraBlockStrideRange

/-- At the head of the first iteration the fallback prefetch words are copies of the
current pair, until a look-ahead load replaces them. -/
private def firstPairWords (P : Params) (L : Launch) (g : Nat) (d : D) (extra : Bool) : D :=
  let hi := slotIdx P L g d.block (laneOf L g) 1
  { d with site := .waitFree extra, i1 := hi, n0 := d.i0, n1 := hi }

section
variable {P : Params} {L : Launch}

private theorem first_main_raw {g : Nat} {d : D} {u : TState} (hd : d.site = .pair false true true)
    (hu : At u (d.site.pc + 1) (loadedPairFacts P L g d false true)) :
    At u 2404 (liveFacts P L g (firstPairWords P L g d false) 2404) := by
  rw [hd] at hu
  apply after_pair_table hu
  · idx_simp [firstPairWords, Site.hasPair, ite_true, ↓reduceIte]
  · idx_simp [firstPairWords, Site.hasPair, ite_true, ↓reduceIte]
  · intro r hr hlo hhi
    change r ∈ preLive 2404 at hr
    rw [show preLive 2404 = [466, 490, 491, 496, 497, 498, 499, 500, 501, 502, 503, 504,
        2968, 2969, 2973, 2974, 2980, 3011, 3013, 3014] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hlo
      | exact absurd rfl hhi
      | (rw [facts_eq_liveFacts rfl, hd]
         apply live_mem (by decide +kernel)
         idx_simp [hd, firstPairWords, len1Reg, countReg, Site.hasPair, ite_true, ↓reduceIte])

private theorem total_count_lt {mem0 : Mem0} {g : Nat} {d : D} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (hi : Inv P L g d) :
    totalBlocks d.len0 d.len1 < 2 ^ 31 := by
  have hp := hpre.paddedRange _ hbatch
  rw [← hi.len0, ← hi.len1] at hp
  rw [← totalBlocks_eq_counts]
  omega

private theorem main_first_head {mem0 : Mem0} {g : Nat} {d : D} {t : TState} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (hd : d.site = .pair false true true) (hi : Inv P L g d)
    (h : At t 2404 (liveFacts P L g (firstPairWords P L g d false) 2404)) :
    ∃ t', run kernel asms L g 23 t = some t' ∧
      At t' 2427 (liveFacts P L g (firstPairWords P L g d false) 2427) := by
  have hb : d.block = 0 := hi.firstBlock (.inr hd)
  have hne : d.site ≠ .barrier := by simp [hd]
  have hph : d.phase = 0 := by rw [hi.phase_block hne, hb]
  have hpar : d.par = 0 := by rw [hi.par_block hne, hb]
  have hcount := lt_of_le_of_lt (numOrigBlocks_le_totalBlocks d.len0 d.len1)
    (total_count_lt hpre hbatch hi)
  have hcountPos := numOrigBlocks_pos d.len0
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hbase := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 5 t = some t1 ∧
      At t1 2409 ((18, .pred false) :: liveFacts P L g (firstPairWords P L g d false) 2409) := by
    seg_fp h using
      all_goals (try idx_values)
      all_goals first
        | norm_signed [firstPairWords]
        | norm_bits [firstPairWords, sb, hph, hpar]
  obtain ⟨t2, hr2, ht2⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2409 h1
    (by simp) (by decide) (by decide)
  have h2 : At t2 2410 (liveFacts P L g (firstPairWords P L g d false) 2410) :=
    at_of_cons ht2 (by lit_mem)
  obtain ⟨t3, hr3, h3⟩ := prepare_stride_main hpre hpre.blockStrideMod h2
  obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 6 t3 = some t4 ∧
      At t4 2420 (liveFacts P L g (firstPairWords P L g d false) 2420) := by
    seg_fp h3 using (all_goals idx_bits [firstPairWords, hb, sb])
  obtain ⟨t5, hr5, h5⟩ : ∃ t5, run kernel asms L g 7 t4 = some t5 ∧
      At t5 2427 (liveFacts P L g (firstPairWords P L g d false) 2427) := by
    seg_fp h4 using
      all_goals (try idx_values)
      all_goals norm_bits [firstPairWords, hb, hph, hpar, ite_self, Site.hasPair, ite_true]
  exact ⟨t5, run_comp (run_comp (run_comp hr1 hr2) hr3) (run_comp hr4 hr5), h5⟩

/-- Change the table after a local branch while preserving its instruction boundary. -/
private theorem first_branch_frame {g pc src : Nat} {d d' : D} {t : TState} {p : Nat} {b : Bool}
    (h : At t pc ((p, .pred b) :: liveFacts P L g d src)) (hs : ∀ r ∈ preLive pc, r ∈ preLive src)
    (hv : ∀ r ∈ preLive pc, valueOf P L g d r = valueOf P L g d' r) :
    At t pc (liveFacts P L g d' pc) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  apply holds_of_pointwise
  intro r hr
  rw [← hv r hr]
  exact holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (mem_factsFrom (hs r hr)))

private theorem main_first_branch {mem0 : Mem0} {g : Nat} {d : D} {t : TState} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (hd : d.site = .pair false true true) (hi : Inv P L g d)
    (h : At t 2427 (liveFacts P L g (firstPairWords P L g d false) 2427)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      AtD P L g (afterPairHigh P L g d false true) t' := by
  let d' := afterPairHigh P L g d false true
  have hb := hi.firstBlock (.inr hd)
  have hs := afterPairFirst_eq d false hb
  have hcount := lt_of_le_of_lt (numOrigBlocks_le_totalBlocks d.len0 d.len1)
    (total_count_lt hpre hbatch hi)
  have hn : d.block + 1 < 2 ^ 31 := by simp [hb]
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
      At t1 2428 ((19, .pred (decide (numOrigBlocks d.len0 ≤ d.block + 1))) ::
        liveFacts P L g (firstPairWords P L g d false) 2428) := by
    seg_fp h using
      all_goals idx_values
      all_goals norm_signed [firstPairWords]
  by_cases hnext : d.block + 1 < numOrigBlocks d.len0
  · have hsite : d'.site = .pair false false false := by
      simpa [d', afterPairHigh, pairLimit, hnext] using hs
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2428 h1
      (by simp [Nat.not_le.mpr hnext]) (by decide) (by decide)
    have ht : At t2 2429 (liveFacts P L g d' 2429) := by
      apply first_branch_frame h2 (by lit_mem)
      intro r hr
      change r ∈ preLive 2429 at hr
      rw [show preLive 2429 = [456, 491, 496, 497, 498, 500, 501, 502, 503, 504, 505, 506,
        2968, 2969, 2970, 2971, 2972, 2973, 2974, 2977, 2980, 3014, 4029]
        from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        idx_simp [firstPairWords, hsite, d', afterPairHigh, hs, pairLimit, hnext, Site.hasPair,
          countReg, len1Reg, Bool.false_eq_true, ite_true, ↓reduceIte]
    exact ⟨t2, run_rtg (run_comp hr1 hr2),
      atD_of_liveFacts (d := d') (by rw [hsite]; rfl) (by rw [hsite]; rfl)
        (by rw [accOf, hsite]) ht⟩
  · have hsite : d'.site = .waitFree false := by
      simpa [d', afterPairHigh, pairLimit, hnext] using hs
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2428 h1
      (by simp [Nat.le_of_not_lt hnext]) (by decide) (by decide)
    have ht : At t2 2430 (liveFacts P L g d' 2430) := by
      apply first_branch_frame h2 (by lit_mem)
      intro r hr
      change r ∈ preLive 2430 at hr
      rw [show preLive 2430 = [456, 491, 496, 497, 498, 500, 501, 502, 503, 504, 505, 506,
        2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2977, 2980, 3014, 4029]
        from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        idx_simp [firstPairWords, hsite, d', afterPairHigh, hs, pairLimit, hnext, Site.hasPair,
          countReg, len1Reg, Bool.false_eq_true, ite_true, ↓reduceIte]
    obtain ⟨t3, hr3, h3⟩ := prepare_wait_main hpre hbatch hsite (inv_afterPairHigh hd hi) ht
    exact ⟨t3, (run_rtg (run_comp hr1 hr2)).trans (run_rtg hr3),
      atD_of_liveFacts (d := d') (by rw [hsite]; rfl) (by rw [hsite]; rfl)
        (by rw [accOf, hsite]) h3⟩

/-- Complete the main cache's initial pair load and choose the first look-ahead path. -/
theorem stepAt_mainFirstPairHigh {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (d : D) (hd : d.site = .pair false true true)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  rcases pairHigh_loaded hd (atD_code.mp hat) hc hf with hn | ⟨hn, hload⟩
  · exact .inl (.inl hn)
  obtain ⟨t1, hr1, h1⟩ := main_first_head hpre hbatch hd hi (first_main_raw hd hload)
  obtain ⟨t2, hr2, h2⟩ := main_first_branch hpre hbatch hd hi h1
  exact .inl (.inr ⟨afterPairHigh P L g d false true, t2, hn,
    (run_rtg hr1).trans hr2, atD_code.mpr h2, inv_afterPairHigh hd hi⟩)

/-- Before the first extra-cache look-ahead increment, the counter is the current block. -/
private def extraFirstWords (P : Params) (L : Launch) (g : Nat) (d : D) : D :=
  { firstPairWords P L g d true with site := .waitFree false }

private theorem first_extra_raw {g : Nat} {d : D} {u : TState} (hd : d.site = .pair true true true)
    (hu : At u (d.site.pc + 1) (loadedPairFacts P L g d true true)) :
    At u 2502 (liveFacts P L g (extraFirstWords P L g d) 2502) := by
  rw [hd] at hu
  apply after_pair_table hu
  · idx_simp [extraFirstWords, firstPairWords, Site.hasPair, ite_true, ↓reduceIte]
  · idx_simp [extraFirstWords, firstPairWords, Site.hasPair, ite_true, ↓reduceIte]
  · intro r hr hlo hhi
    change r ∈ preLive 2502 at hr
    rw [show preLive 2502 = [456, 491, 496, 498, 500, 501, 502, 503, 505, 2969, 2977, 2980,
      2981, 2982, 3014] from by decide +kernel] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
      first
      | exact absurd rfl hlo
      | exact absurd rfl hhi
      | (rw [facts_eq_liveFacts rfl, hd]
         apply live_mem (by decide +kernel)
         idx_simp [hd, extraFirstWords, firstPairWords, len1Reg, countReg, Site.hasPair,
           ite_true, ↓reduceIte])

private theorem extra_first_head {mem0 : Mem0} {g : Nat} {d : D} {t : TState} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (hd : d.site = .pair true true true) (hi : Inv P L g d)
    (h : At t 2502 (liveFacts P L g (extraFirstWords P L g d) 2502)) :
    ∃ t', run kernel asms L g 11 t = some t' ∧
      At t' 2513 (liveFacts P L g (firstPairWords P L g d true) 2513) := by
  have hb : d.block = numOrigBlocks d.len0 := by
    have hp := hi.pairLoad
    rw [pairInvariant, hd] at hp
    exact hp.1
  have hcount := total_count_lt hpre hbatch hi
  have hblk := hi.block
  have hon : numOrigBlocks d.len0 < totalBlocks d.len0 d.len1 := by omega
  have hnum : numOrigBlocks d.len0 < 2 ^ 31 := by omega
  have hpos : 0 < d.len1 := by
    by_contra hzero
    have hlen : d.len1 = 0 := by omega
    rw [hlen] at hblk
    change d.block < numOrigBlocks d.len0 at hblk
    omega
  have hbudget : 0 < P.extra_topk := by
    have hle := extraLen_le hpre hbatch
    rw [hi.len1] at hpos
    omega
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
      At t1 2503 ((33, .pred false) :: liveFacts P L g (extraFirstWords P L g d) 2503) := by
    seg_fp h using
      all_goals idx_values
      all_goals norm_signed [extraFirstWords, firstPairWords, countReg]
  obtain ⟨t2, hr2, ht2⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2503 h1
    (by simp) (by decide) (by decide)
  have h2 : At t2 2504 (liveFacts P L g (extraFirstWords P L g d) 2504) :=
    at_of_cons ht2 (by lit_mem)
  obtain ⟨t3, hr3, h3⟩ := prepare_stride_extra hpre (hpre.extraPos hbudget).2.2.1 h2
  have hor : (2 * laneOf L g) ||| 64 = 64 + 2 * laneOf L g := by
    exact (Nat.or_two_pow_eq_add_of_lt (n := 6) (by omega)).trans (Nat.add_comm _ _)
  obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 5 t3 = some t4 ∧
      At t4 2513 (liveFacts P L g (firstPairWords P L g d true) 2513) := by
    seg_fp h3 using
      all_goals idx_simp [extraFirstWords, firstPairWords, countReg, Site.hasPair, ite_true]
      all_goals nf_simp [hb, Nat.mod_eq_of_lt (show 2 * laneOf L g < 4294967296 by omega),
        Nat.mod_eq_of_lt (show 2 * laneOf L g < 18446744073709551616 by omega),
        hor, Nat.sub_self, Nat.mul_zero, Nat.add_zero, ite_self]
      all_goals omega
  exact ⟨t4, run_comp (run_comp hr1 hr2) (run_comp hr3 hr4), h4⟩

private theorem extra_first_branch {mem0 : Mem0} {g : Nat} {d : D} {t : TState}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hd : d.site = .pair true true true)
    (hi : Inv P L g d) (h : At t 2513 (liveFacts P L g (firstPairWords P L g d true) 2513)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      AtD P L g (afterPairHigh P L g d true true) t' := by
  let d' := afterPairHigh P L g d true true
  have hb : d.block = numOrigBlocks d.len0 := by
    have hp := hi.pairLoad
    rw [pairInvariant, hd] at hp
    exact hp.1
  have hs := afterPairFirst_eq d true hb
  have hcount := total_count_lt hpre hbatch hi
  have hblk := hi.block
  have hn : d.block + 1 < 2 ^ 31 := by omega
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
      At t1 2514 ((34, .pred (decide (totalBlocks d.len0 d.len1 ≤ d.block + 1))) ::
        liveFacts P L g (firstPairWords P L g d true) 2514) := by
    seg_fp h using
      all_goals idx_values
      all_goals norm_signed [firstPairWords, countReg]
  by_cases hnext : d.block + 1 < totalBlocks d.len0 d.len1
  · have hsite : d'.site = .pair true false false := by
      simpa [d', afterPairHigh, pairLimit, hnext] using hs
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2514 h1
      (by simp [Nat.not_le.mpr hnext]) (by decide) (by decide)
    have ht : At t2 2515 (liveFacts P L g (firstPairWords P L g d true) 2515) :=
      at_of_cons h2 (by lit_mem)
    have hcount1 : d.block + 1 - numOrigBlocks d.len0 = 1 := by omega
    have hcount0 : d.block - numOrigBlocks d.len0 = 0 := by omega
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 2517 (liveFacts P L g (firstPairWords P L g d true) 2517) := by
      seg_fp ht using
        all_goals idx_simp [extraPairAddr, firstPairWords, hcount0, hcount1, Nat.mul_zero,
          Nat.add_zero]
        all_goals norm_bits [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hgood : At t3 2517 (liveFacts P L g d' 2517) := by
      refine ⟨h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, ?_⟩
      apply holds_of_pointwise
      intro r hr
      refine holds_mem h3.2.2.2.2 (live_mem hr ?_)
      change r ∈ preLive 2517 at hr
      rw [show preLive 2517 = [456, 498, 500, 501, 502, 503, 505, 509, 2969, 2977, 2978, 2979,
        2980, 2981, 2982, 3014, 3043] from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        idx_simp [firstPairWords, d', afterPairHigh, hs, pairLimit, hnext, Site.hasPair,
          countReg, len1Reg, ite_true, ↓reduceIte]
    exact ⟨t3, run_rtg (run_comp (run_comp hr1 hr2) hr3),
      atD_of_liveFacts (d := d') (by rw [hsite]; rfl) (by rw [hsite]; rfl)
        (by rw [accOf, hsite]) hgood⟩
  · have hsite : d'.site = .waitFree true := by
      simpa [d', afterPairHigh, pairLimit, hnext] using hs
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2514 h1
      (by simp [Nat.le_of_not_lt hnext]) (by decide) (by decide)
    have ht : At t2 2518 (liveFacts P L g d' 2518) := by
      apply first_branch_frame h2 (by lit_mem)
      intro r hr
      change r ∈ preLive 2518 at hr
      rw [show preLive 2518 = [456, 498, 500, 501, 502, 503, 505, 509, 2969, 2977, 2978, 2979,
        2980, 2981, 2982, 2983, 2984, 3014] from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        idx_simp [firstPairWords, d', afterPairHigh, hs, pairLimit, hnext, Site.hasPair,
          countReg, len1Reg, ite_true, ↓reduceIte]
    obtain ⟨t3, hr3, h3⟩ := prepare_wait_extra hpre hbatch hsite (inv_afterPairHigh hd hi) ht
    exact ⟨t3, (run_rtg (run_comp hr1 hr2)).trans (run_rtg hr3),
      atD_of_liveFacts (d := d') (by rw [hsite]; rfl) (by rw [hsite]; rfl)
        (by rw [accOf, hsite]) h3⟩

/-- Complete the extra cache's initial pair load and choose the first look-ahead path. -/
theorem stepAt_extraFirstPairHigh {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hbatch : eOf L g < P.b) (d : D) (hd : d.site = .pair true true true)
    : (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  rcases pairHigh_loaded hd (atD_code.mp hat) hc hf with hn | ⟨hn, hload⟩
  · exact .inl (.inl hn)
  obtain ⟨t1, hr1, h1⟩ := extra_first_head hpre hbatch hd hi (first_extra_raw hd hload)
  obtain ⟨t2, hr2, h2⟩ := extra_first_branch hpre hbatch hd hi h1
  exact .inl (.inr ⟨afterPairHigh P L g d true true, t2, hn,
    (run_rtg hr1).trans hr2, atD_code.mpr h2, inv_afterPairHigh hd hi⟩)

/-! ## Retrying the free-slot poll -/

/-- A site's free-barrier poll writes the outcome predicate and preserves the operand table. -/
private theorem after_free_wait {g : Nat} {d : D} {t u : TState} {p : Nat} {ok extra : Bool}
    (hd : d.site = .waitFree extra) (hat : AtD P L g d t)
    (hu : u = PTX.next (setReg t p (.pred ok))) (hp : p ∉ preLive d.site.pc) :
    At u (d.site.pc + 1) ((p, .pred ok) :: liveFacts P L g d d.site.pc) := by
  subst u
  have ha : At (setReg t p (.pred ok)) d.site.pc
      ((p, .pred ok) :: liveFacts P L g d d.site.pc) := by
    refine ⟨hat.1, ?_, ?_, hat.2.2.2.1, ?_⟩
    · show t.sub = 0
      rw [hat.2.1, hd]; rfl
    · show t.acc = []
      rw [hat.2.2.1, accOf, hd]
    rw [holds_cons]
    refine ⟨by simp [setReg], ?_⟩
    apply holds_of_pointwise
    intro r hr
    have hn : r ≠ p := fun he => hp (he ▸ hr)
    have hholds := hat.2.2.2.2
    rw [facts_eq_liveFacts (d := d) rfl] at hholds
    have h := holds_mem hholds (mem_factsFrom (val := valueOf P L g d) hr)
    simpa [setReg, Function.update_of_ne hn] using h
  exact At.next ha
end

/-- Invert either cache's free-barrier poll and recover its boundary and concrete outcome. -/
macro "prove_free_poll" name:ident "," extra:term "," poll:num "," pred:num ","
    base:num "," parity:num "," code:term : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t u : TState} {ins : Instr} {e : Event}
      (hpre : Pre P L mem0) (hd : d.site = .waitFree $extra) (hi : Inv P L g d)
      (hat : AtD P L g d t) (hc : kernel.code[d.site.pc]? = some ins)
      (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
      ∃ ok acq sc, e.kind = .wait ⟨.shared, ctaOf L g, L.sharedBase + freeOff d.phase⟩
          ((1 - d.par) % 2) ok acq sc ∧
        At u ($poll + 1) (($pred, .pred ok) :: liveFacts P L g d $poll) := by
    have hpc : d.site.pc = $poll := by rw [hd]; rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $code)
    subst ins
    have ht : At t $poll (liveFacts P L g d $poll) := by
      refine ⟨hat.1.trans hpc, ?_, ?_, hat.2.2.2.1, ?_⟩
      · rw [hat.2.1, hd]; rfl
      · rw [hat.2.2.1, accOf, hd]
      · have hholds := hat.2.2.2.2
        rw [facts_eq_liveFacts (d := d) rfl, hpc] at hholds
        exact hholds
    have hbase : t.regs $base = some (sb L (freeOff d.phase)) := by
      exact holds_mem ht.2.2.2.2 (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $poll)
        (by decide +kernel) (by idx_values))
    have hpar : t.regs $parity = some (b32 (1 - d.par)) := by
      exact holds_mem ht.2.2.2.2 (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $poll)
        (by decide +kernel) (by idx_values))
    have hwindow := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have haddr : L.sharedBase + freeOff d.phase < 2 ^ 32 := by
      have := hi.phase
      unfold freeOff
      omega
    have hb8 : L.sharedBase % 8 = 0 := by
      rw [hpre.sharedBase]
      have h := hpre.sharedAlignment
      omega
    have hf8 : freeOff d.phase % 8 = 0 := by
      unfold freeOff
      omega
    have ha : (L.sharedBase + freeOff d.phase) % 8 = 0 := by omega
    have hm := mbarLoc_b32 (L := L) (g := g) hbase haddr ha
    have hq := readBits_b32 (L := L) (g := g) hpar (by omega)
    obtain ⟨ok, acq, sc, he, hu⟩ := fires_wait_at_succ hm hq hf
    have hp : $pred ∉ preLive d.site.pc := by rw [hpc]; decide +kernel
    have hr := after_free_wait hd hat hu hp
    rw [hpc] at hr
    refine ⟨ok, acq, sc, ?_, hr⟩
    have hpar64 : 1 - d.par < 2 ^ 64 := by omega
    rw [he]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpar64, ctaOf])

prove_free_poll fire_free_main, false, 2446, 4122, 585, 586, Flow.code_2446
prove_free_poll fire_free_extra, true, 2534, 4123, 623, 624, Flow.code_2534

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private theorem retry_free_main {P : Params} {L : Launch} {g : Nat} {d : D} {u : TState}
    (h : At u 2447 ((4122, .pred false) :: liveFacts P L g d 2446)) :
    ∃ t', run kernel asms L g 2 u = some t' ∧ At t' 2446 (liveFacts P L g d 2446) := by
  seg_fp h using rfl

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
private theorem retry_free_extra {P : Params} {L : Launch} {g : Nat} {d : D} {u : TState}
    (h : At u 2535 ((4123, .pred false) :: liveFacts P L g d 2534)) :
    ∃ t', run kernel asms L g 2 u = some t' ∧ At t' 2534 (liveFacts P L g d 2534) := by
  seg_fp h using rfl

/-! ## Combining the four lane masks -/

private theorem sx8_lt (x : Nat) : sx8 x < 2 ^ 32 := by
  unfold sx8
  have h := Nat.mod_lt x (by decide : 0 < 256)
  split <;> omega

private theorem sx8_mod256 (x : Nat) : sx8 x % 256 = x % 256 := by
  unfold sx8
  split <;> omega

private theorem mod256_or (x y : Nat) : (x ||| y) % 256 = x % 256 ||| y % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((x ||| y) % 2 ^ 8).testBit i = ((x % 2 ^ 8) ||| (y % 2 ^ 8)).testBit i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or]
  by_cases hi : i < 8 <;> simp [hi]

private theorem sx8_quadWord (P : Params) (L : Launch) (g b l : Nat) :
    sx8 (quadWord P L g b l) = pairWord P L g b l := by
  unfold pairWord quadWord
  generalize laneWord P L g b (l ^^^ 1) = x
  unfold laneWord
  generalize laneByte P L g b l = y
  let signedByte := fun n : Nat => if n < 128 then n else n + (2 ^ 32 - 256)
  change signedByte ((x ||| y) % 256) = signedByte ((sx8 y ||| x) % 256)
  exact congrArg signedByte (by
    rw [mod256_or, mod256_or, sx8_mod256, Nat.or_comm (x % 256) (y % 256)])

private theorem or_word32 (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    Value.bits 32 (truncBits 32 (BitVec.ofNat 64 x) |||
      truncBits 32 (BitVec.ofNat 64 y)) = b32 (x ||| y) := by
  rw [truncBits_ofNat hx (by decide), truncBits_ofNat hy (by decide)]
  nf_simp [Nat.mod_eq_of_lt (show x < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show y < 18446744073709551616 by omega)]

private theorem sx8_value (x : Nat) :
    (.same : MemExt).extendBits 32
      (cvtIntBits false .s 32 .s 8 (truncBits 8 (BitVec.ofNat 64 x))) = b32 (sx8 x) := by
  nf_simp [MemExt.extendBits, cvtIntBits, intBits, intSat, intOf, toSigned, sx8]
  split_ifs <;> omega

private theorem body_pair {d : D} (h : d.site.inBody = true) : d.site.hasPair = true := by
  cases hs : d.site <;> simp_all [Site.inBody, Site.hasPair]

private theorem body_len1 {P : Params} {d : D} (h : d.site.inBody = true) :
    len1Reg P d = d.len1 := by
  cases hs : d.site <;> simp_all [Site.inBody, len1Reg]

private theorem body_count {d : D} (h : d.site.inBody = true) :
    countReg d = if d.site.extra = some true then d.block + 1 else numOrigBlocks d.len0 := by
  cases hs : d.site <;> simp_all [Site.inBody, countReg, Site.extra]
  case coord e hi => cases e <;> rfl
  all_goals rename_i e; cases e <;> rfl

private theorem body_table {P : Params} {L : Launch} {g : Nat} {d : D} {s : Site}
    (h : d.site.inBody = true) (hs : s.inBody = true) (he : s.extra = d.site.extra) :
    table P L g d = table P L g { d with site := s } := by
  let d' := { d with site := s }
  have hs' : d'.site.inBody = true := hs
  have hc : countReg d = countReg d' := by
    rw [body_count h, body_count hs']
    change (if d.site.extra = some true then d.block + 1 else numOrigBlocks d.len0) =
      (if s.extra = some true then d.block + 1 else numOrigBlocks d.len0)
    rw [he]
  change table P L g d = table P L g d'
  unfold table
  rw [body_pair h, body_pair hs', body_len1 h, body_len1 hs', hc]

private theorem body_live {P : Params} {L : Launch} {g pc : Nat} {d : D} {s : Site}
    (h : d.site.inBody = true) (hs : s.inBody = true) (he : s.extra = d.site.extra) :
    liveFacts P L g d pc = liveFacts P L g { d with site := s } pc := by
  unfold liveFacts valueOf
  rw [body_table h hs he]

/-- The first shuffle receives its neighbor's mask, then ORs and sign-extends the byte. -/
macro "prove_shuffle_pair" name:ident "," extra:term "," pc:num "," after:num ","
    cast:num "," stop:num "," dst:num "," pred:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
      {d : D} {t : TState} (_hpre : Pre P L mem0) (_hi : Inv P L g d)
      (hd : d.site = .quad1 $extra)
      (h : At t $after (($pred, .pred true) ::
        ($dst, b32 (laneWord P L g d.block (laneOf L g ^^^ 1))) :: liveFacts P L g d $pc)) :
      ∃ t', run kernel asms L g 2 t = some t' ∧
        At t' $stop (liveFacts P L g { d with site := .quad2 $extra } $stop) := by
    have hb : d.site.inBody = true := by rw [hd]; rfl
    have hx := sx8_lt (laneByte P L g d.block (laneOf L g ^^^ 1))
    have hy : laneByte P L g d.block (laneOf L g) < 2 ^ 32 := by
      have := laneByte_lt P L g d.block (laneOf L g)
      omega
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
        At t1 $cast (liveFacts P L g d $cast) := by
      seg_fp h using
        all_goals idx_simp [hd, Site.hasPair, countReg, len1Reg, ite_true]
        all_goals exact or_word32 _ _ hx hy
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
        At t2 $stop (liveFacts P L g d $stop) := by
      seg_fp h1 using
        all_goals idx_values
        all_goals rw [sx8_value, sx8_quadWord]
    rw [body_live (pc := $stop) hb (s := .quad2 $extra) rfl (by rw [hd]; rfl)] at h2
    exact ⟨t2, run_comp hr1 hr2, h2⟩)

prove_shuffle_pair after_quad1_main, false, 2464, 2465, 2466, 2467, 607, 27
prove_shuffle_pair after_quad1_extra, true, 2553, 2554, 2555, 2556, 646, 42

private theorem quadWord_lt (P : Params) (L : Launch) (g b l : Nat) :
    quadWord P L g b l < 2 ^ 32 := by
  unfold quadWord laneWord
  exact Nat.or_lt_two_pow (sx8_lt _) (by have := laneByte_lt P L g b l; omega)

/-- The second shuffle finishes the OR, and the loop computes the two-word store address. -/
macro "prove_shuffle_quad" name:ident "," extra:term "," pc:num "," after:num ","
    address:num "," stop:num "," dst:num "," pred:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hi : Inv P L g d)
      (hd : d.site = .quad2 $extra)
      (h : At t $after (($pred, .pred true) ::
        ($dst, b32 (pairWord P L g d.block (laneOf L g ^^^ 2))) :: liveFacts P L g d $pc)) :
      ∃ t', run kernel asms L g 3 t = some t' ∧
        At t' $stop (liveFacts P L g { d with site := .coord $extra false } $stop) := by
    have hb : d.site.inBody = true := by rw [hd]; rfl
    have hx := quadWord_lt P L g d.block (laneOf L g)
    have hy : pairWord P L g d.block (laneOf L g ^^^ 2) < 2 ^ 32 := sx8_lt _
    have hbase := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have hphase := hi.phase
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
        At t1 $address (liveFacts P L g d $address) := by
      seg_fp h using
        all_goals idx_simp [hd, Site.hasPair, countReg, len1Reg, ite_true]
        all_goals exact or_word32 _ _ hx hy
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 2 t1 = some t2 ∧
        At t2 $stop (liveFacts P L g d $stop) := by
      seg_fp h1 using
        all_goals idx_values
        all_goals norm_bits [sb]
    rw [body_live (pc := $stop) hb (s := .coord $extra false) rfl (by rw [hd]; rfl)] at h2
    exact ⟨t2, run_comp hr1 hr2, h2⟩)

prove_shuffle_quad after_quad2_main, false, 2467, 2468, 2469, 2471, 610, 28
prove_shuffle_quad after_quad2_extra, true, 2556, 2557, 2558, 2560, 649, 43

private theorem inv_body_move {P : Params} {L : Launch} {g : Nat} {d : D} {s : Site}
    (h : Inv P L g d) (hfrom : d.site.inBody = true) (hto : s.inBody = true)
    (hextra : s.extra = d.site.extra) : Inv P L g { d with site := s } := by
  have hn : d.site ≠ .barrier := by intro hbar; simp [hbar, Site.inBody] at hfrom
  have hp := body_pair hfrom
  refine ⟨h.phase, h.par, fun _ => h.phase_block hn, fun _ => h.par_block hn, ?_,
    h.len0, h.len1, h.block, ?_, ?_, fun _ => h.slot0 hp, fun _ => h.slot1 hp, ?_, ?_, ?_, ?_⟩
  · rcases s <;> simp_all [Site.inBody]
  · intro hs
    exact h.tagMain (hextra.symm.trans hs)
  · intro hs
    exact h.tagExtra (hextra.symm.trans hs)
  · intro _ hs
    apply h.pref0 hfrom
    rwa [← hextra]
  · intro _ hs
    apply h.pref1 hfrom
    rwa [← hextra]
  · rcases s <;> simp_all [Site.inBody]
  · rcases s <;> simp_all [Site.inBody, pairInvariant]

private theorem at_body_event {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (h : AtD P L g d t) (hs : d.site.sub = 0) (ha : accOf d = []) :
    At t d.site.pc (liveFacts P L g d d.site.pc) := by
  refine ⟨h.1, h.2.1.trans hs, h.2.2.1.trans ha, h.2.2.2.1, ?_⟩
  rw [← facts_eq_liveFacts rfl]
  exact h.2.2.2.2

private theorem reg_not_in_facts {r : Nat} {live : List Nat} {val : Nat → Value}
    (h : r ∉ live) : ∀ p ∈ factsFrom live val, p.1 ≠ r := by
  intro p hp hn
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h (hn ▸ hq)

private theorem at_shfl_result {t : TState} {pc dst pred : Nat} {F : List (Nat × Value)}
    {v : Value} (h : At t pc F)
    (hd : ∀ p ∈ F, p.1 ≠ dst) (hp : ∀ p ∈ F, p.1 ≠ pred) (hne : dst ≠ pred) :
    At (PTX.next (setReg (setReg t dst v) pred (.pred true))) (pc + 1)
      ((pred, .pred true) :: (dst, v) :: F) := by
  refine ⟨h.1 ▸ rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_⟩
  · simp [PTX.next, setReg]
  · simp [PTX.next, setReg, Function.update_of_ne hne]
  · exact holds_update (holds_update h.2.2.2.2 hd) hp

/-- Check one reduction stage followed by the concrete integer instructions that use it. -/
macro "prove_index_shuffle " name:ident "," old:term "," new:term "," pc:num "," after:num ","
    stop:num "," dst:num "," pred:num "," laneXor:num "," word:ident ","
    opcode:term "," tail:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
      (hpre : Pre P L mem0) (d : D) (hd : d.site = $old) :
      (code P L g).StepAt d := by
    apply stepAt_of
    intro t e u ins hat hi hc hf
    have hs : d.site.pc = $pc := by rw [hd]; rfl
    rw [hs] at hc hf
    have hop := Option.some.inj (hc.symm.trans $opcode)
    subst ins
    obtain ⟨va, vb, vc, recv, ok, he, hu⟩ := fires_shfl (p := some $pred) hf
    by_cases hw : ok = true ∧ recv = b32 ($word P L g d.block (laneOf L g ^^^ $laneXor))
    · obtain ⟨hok, hrecv⟩ := hw
      subst ok recv
      let d' := { d with site := $new }
      have hn : next P L g d e = some (some d') := by
        simp [next, nextSite, hd, he, d']
      have ht := at_body_event (atD_code.mp hat) (by rw [hd]; rfl) (by simp [accOf, hd])
      rw [hs] at ht
      have hu' : At u $after (($pred, .pred true) ::
          ($dst, b32 ($word P L g d.block (laneOf L g ^^^ $laneXor))) ::
          liveFacts P L g d $pc) := by
        rw [hu]
        exact at_shfl_result ht (reg_not_in_facts (by decide +kernel))
          (reg_not_in_facts (by decide +kernel)) (by decide)
      obtain ⟨t', hr, ht'⟩ := $tail hpre hi hd hu'
      have hAt := atD_of_liveFacts (d := d') (pc := $stop) rfl rfl rfl ht'
      have hi' : Inv P L g d' :=
        inv_body_move (s := $new) hi (by rw [hd]; rfl) rfl (by rw [hd]; rfl)
      exact .inl (.inr ⟨d', t', hn, run_rtg hr, atD_code.mpr hAt, hi'⟩)
    · exact .inl (.inl (by simp [next, nextSite, hd, he, hw])))

prove_index_shuffle stepAt_quad1Main, (.quad1 false), (.quad2 false), 2464, 2465, 2467,
  607, 27, 1, laneWord, Flow.code_2464, after_quad1_main

prove_index_shuffle stepAt_quad1Extra, (.quad1 true), (.quad2 true), 2553, 2554, 2556,
  646, 42, 1, laneWord, Flow.code_2553, after_quad1_extra

prove_index_shuffle stepAt_quad2Main, (.quad2 false), (.coord false false), 2467, 2468, 2471,
  610, 28, 2, pairWord, Flow.code_2467, after_quad2_main

prove_index_shuffle stepAt_quad2Extra, (.quad2 true), (.coord true false), 2556, 2557, 2560,
  649, 43, 2, pairWord, Flow.code_2556, after_quad2_extra
/-! ## Computing the two coordinates -/

/-- When the length check succeeds, the sentinel comparison is faithful to the signed index. -/
private theorem slot_present_bits {P : Params} {L : Launch} {mem0 : Mem0} {g b lane i : Nat}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hr : slotPos (P.topkLen (eOf L g)) b lane i <
      slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) b) :
    ipat (slotIdx P L g b lane i) ≠ 4294967295 ↔ slotIdx P L g b lane i ≠ -1 := by
  let pos := slotPos (P.topkLen (eOf L g)) b lane i
  by_cases hn : slotIdx P L g b lane i = -1
  · simp [hn, ipat, i32Bits]
  have hword : 0 ≤ slotIdx P L g b lane i ∧ (slotIdx P L g b lane i).toNat < 2147483648 := by
    cases hx : isExtraBlock b (P.topkLen (eOf L g))
    · have he : slotIdx P L g b lane i = P.idx (eOf L g) (qOf L g) pos := by
        simp [slotIdx, slotIndex, hx, pos]
      have hlen : pos < P.topkLen (eOf L g) := by simpa [slotLen, hx, pos] using hr
      obtain ⟨h0, h1⟩ := hpre.idxRange _ hbatch _ hq pos ⟨hlen, he ▸ hn⟩
      have hp : P.page ≤ P.blockStride / 528 := by have := hpre.pageFits; omega
      have hprod := Nat.mul_le_mul_left P.numBlocks hp
      have ht := hpre.rowsRange
      rw [he]
      exact ⟨h0, by omega⟩
    · have he : slotIdx P L g b lane i = P.extraIdx (eOf L g) (qOf L g) pos := by
        simp [slotIdx, slotIndex, hx, pos]
      have hlen : pos < P.extraTopkLen (eOf L g) := by simpa [slotLen, hx, pos] using hr
      obtain ⟨h0, h1⟩ := hpre.extraIdxRange _ hbatch _ hq pos ⟨hlen, he ▸ hn⟩
      have hbudget : 0 < P.extra_topk := by
        have he := extraLen_le hpre hbatch
        omega
      have hp : P.extraPage ≤ P.extraBlockStride / 528 := by
        have hf := (hpre.extraPos hbudget).2.2.2
        omega
      have hprod := Nat.mul_le_mul_left P.extraNumBlocks hp
      have ht := hpre.extraRowsRange
      rw [he]
      exact ⟨h0, by omega⟩
  rw [ipat_eq_toNat hword.1 (by have := hword.2; omega)]
  exact iff_of_true (by have := hword.2; omega) hn

private theorem validBit_ptx {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {extra : Bool} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hi : Inv P L g d) (htag : isExtraBlock d.block (P.topkLen (eOf L g)) = extra) (i : Nat) :
    (decide (ipat (slotIdx P L g d.block (laneOf L g) i) ≠ 4294967295) &&
      decide ((if extra then d.block - numOrigBlocks d.len0 else d.block) * 64
          + 2 * laneOf L g + i < (if extra then d.len1 else d.len0))) =
      validBit P L g d.block (laneOf L g) i := by
  rw [hi.len0, hi.len1]
  have hpos : slotPos (P.topkLen (eOf L g)) d.block (laneOf L g) i =
      (if extra then d.block - numOrigBlocks (P.topkLen (eOf L g)) else d.block) * 64
        + 2 * laneOf L g + i := by
    cases extra <;> simp [slotPos, htag, topkBlock, Nat.mul_comm, Nat.add_comm]
  have hlen : slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) d.block =
      (if extra then P.extraTopkLen (eOf L g) else P.topkLen (eOf L g)) := by
    simp [slotLen, htag]
  rw [← hpos, ← hlen]
  unfold validBit kvSlotValid
  by_cases hr : slotPos (P.topkLen (eOf L g)) d.block (laneOf L g) i <
      slotLen (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)) d.block
  · have he := slot_present_bits hpre hbatch hq hr
    simp only [hr, decide_true, Bool.and_true]
    by_cases hs : slotIdx P L g d.block (laneOf L g) i = -1
    · simp [hs, ipat, i32Bits]
    · simp [hs, he.mpr hs]
  · simp [hr]

private theorem row_of_in_range {idx page stride count : Nat} (hp : 0 < page)
    (hfit : page ≤ stride / bytesPerToken) (hi : idx < count * page) :
    idx / page * (stride / bytesPerToken) + idx % page < count * (stride / bytesPerToken) := by
  have hblock := (Nat.div_lt_iff_lt_mul hp).2 hi
  have hrow := Nat.mod_lt idx hp
  have hstep := Nat.mul_le_mul_right (stride / bytesPerToken) (show idx / page + 1 ≤ count by omega)
  rw [Nat.add_mul, Nat.one_mul] at hstep
  omega

private theorem valid_row_bound {P : Params} {L : Launch} {mem0 : Mem0} {g b lane i : Nat}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hblk : b < totalBlocks (P.topkLen (eOf L g)) (P.extraTopkLen (eOf L g)))
    (hv : validBit P L g b lane i = true) : rowBits P L g b lane i < 2 ^ 32 := by
  rw [rowBits_eq_rowOf hpre hbatch hq hblk hv]
  have hpos := slotPos_lt_slotLen_of_kvSlotValid hv
  have hne := (kvSlotValid_eq_true_iff.mp hv).1
  let j := slotPos (P.topkLen (eOf L g)) b lane i
  cases he : isExtraBlock b (P.topkLen (eOf L g))
  · have hidx : slotIdx P L g b lane i = P.idx (eOf L g) (qOf L g) j := by
      simp [slotIdx, slotIndex, he, j]
    have hlen : j < P.topkLen (eOf L g) := by simpa [slotLen, he, j] using hpos
    obtain ⟨_, hidxRange⟩ := hpre.idxRange _ hbatch _ hq j ⟨hlen, hidx ▸ hne⟩
    have hpage : P.page ≤ P.blockStride / bytesPerToken := by
      have := hpre.pageFits
      change P.page ≤ P.blockStride / 528
      omega
    have hr := row_of_in_range hpre.pagePos hpage hidxRange
    simp only [slotStride, slotBlockStride, slotPg, slotPage, he, Bool.false_eq_true, ↓reduceIte,
      hidx, rowOf, blockOf, inBlock]
    have ht := hpre.rowsRange
    change P.numBlocks * (P.blockStride / bytesPerToken) < 2 ^ 31 at ht
    exact lt_trans hr (by omega)
  · have hidx : slotIdx P L g b lane i = P.extraIdx (eOf L g) (qOf L g) j := by
      simp [slotIdx, slotIndex, he, j]
    have hlen : j < P.extraTopkLen (eOf L g) := by simpa [slotLen, he, j] using hpos
    obtain ⟨_, hidxRange⟩ := hpre.extraIdxRange _ hbatch _ hq j ⟨hlen, hidx ▸ hne⟩
    have hbudget : 0 < P.extra_topk := by
      have h := extraLen_le hpre hbatch
      omega
    obtain ⟨hp, _, _, hf⟩ := hpre.extraPos hbudget
    have hpage : P.extraPage ≤ P.extraBlockStride / bytesPerToken := by
      change P.extraPage ≤ P.extraBlockStride / 528
      omega
    have hr := row_of_in_range hp hpage hidxRange
    simp only [slotStride, slotBlockStride, slotPg, slotPage, he, ↓reduceIte, hidx,
      rowOf, blockOf, inBlock]
    have ht := hpre.extraRowsRange
    change P.extraNumBlocks * (P.extraBlockStride / bytesPerToken) < 2 ^ 31 at ht
    exact lt_trans hr (by omega)

private theorem compare_ne_marker {n : Nat} (hn : n < 2 ^ 32) :
    PTX.compare .ne .b 32 (BitVec.ofNat 64 n) (BitVec.ofNat 64 4294967295) =
      decide (n ≠ 4294967295) := by
  have h64 : n < 18446744073709551616 := by omega
  simp [PTX.compare, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
  omega

private theorem pos_word_bound {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hi : Inv P L g d)
    {b' : Nat} (hb : b' ≤ d.block) :
    2 * laneOf L g + 64 * b' + 1 < 2147483648 := by
  have hp := hpre.paddedRange _ hbatch
  rw [← hi.len0, ← hi.len1] at hp
  have ht := Nat.div_mul_le_self
    (origPadded d.len0 + ceilToMultiple d.len1 topkBlock) 64
  change totalBlocks d.len0 d.len1 * 64 ≤ _ at ht
  have hblk := hi.block
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  omega

private theorem valid_compare_low {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {extra : Bool} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hi : Inv P L g d) (htag : isExtraBlock d.block (P.topkLen (eOf L g)) = extra)
    (i : Nat) {x : Int}
    (hx : x = slotIdx P L g d.block (laneOf L g) i)
    (ha : 2 * laneOf L g + 64 * (if extra then d.block - numOrigBlocks d.len0 else d.block)
      + i < 2 ^ 31) :
    (PTX.compare .ne .b 32
       (truncBits 32 (BitVec.ofNat 64 (ipat x))) (truncBits 32 (BitVec.ofInt 64 (-1))) &&
     PTX.compare .lt .s 32
       (truncBits 32 (BitVec.ofNat 64 (2 * laneOf L g +
         64 * (if extra then d.block - numOrigBlocks d.len0 else d.block) + i)))
       (truncBits 32 (BitVec.ofNat 64 (if extra then d.len1 else d.len0)))) =
      validBit P L g d.block (laneOf L g) i := by
  let n := 2 * laneOf L g + 64 * (if extra then d.block - numOrigBlocks d.len0 else d.block) + i
  let k := if extra then d.len1 else d.len0
  have h1 := topkLen_le hpre hbatch
  have h2 := extraLen_le hpre hbatch
  rw [← hi.len0] at h1
  rw [← hi.len1] at h2
  have hk : k < 2 ^ 31 := by
    have := hpre.topkAdd63Lt
    have := hpre.extraTopkAdd63Lt
    cases extra <;> dsimp [k] <;> omega
  rw [truncBits_ofNat (ipat_bound x) (by decide),
    truncBits_ofNat (show n < 2 ^ 32 by omega) (by decide),
    truncBits_ofNat (show k < 2 ^ 32 by omega) (by decide)]
  rw [show truncBits 32 (BitVec.ofInt 64 (-1)) = BitVec.ofNat 64 4294967295 by decide,
    compare_ne_marker (ipat_bound _), compare_lt_b32 (by omega) (by omega) ha hk, hx]
  have hv := validBit_ptx hpre hbatch hq hi htag i
  simpa [Nat.add_comm (2 * laneOf L g), Nat.mul_comm 64] using congrArg Value.pred hv

/-- Compute the first coordinate and mask bit after a successful poll. -/
macro "prove_low_coord" name:ident "," extra:term "," start:num "," stop:num ","
    page:ident "," st:ident "," strideRange:ident "," test:num "," pred:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
      (hq : qOf L g < P.s_q) (hi : Inv P L g d) (hd : d.site = .waitFree $extra)
      (htag : isExtraBlock d.block (P.topkLen (eOf L g)) = $extra)
      (h : At t $start (liveFacts P L g d $start)) :
      ∃ t', run kernel asms L g 6 t = some t' ∧ At t' $stop (liveFacts P L g d $stop) := by
    have hpair : d.site.hasPair = true := by rw [hd]; rfl
    have hslot := hi.slot0 hpair
    have hp := pos_word_bound hpre hbatch hi (b' := if $extra then
      d.block - numOrigBlocks d.len0 else d.block) (by simp)
    have hv := valid_compare_low hpre hbatch hq hi htag 0 hslot (by omega)
    have hrow : rowBits P L g d.block (laneOf L g) 0 =
        ipat d.i0 / P.$page * (P.$st / bytesPerToken) + ipat d.i0 % P.$page := by
      simp [rowBits, slotPg, slotPage, slotStride, slotBlockStride, htag, ← hslot]
    have hdiv : ipat d.i0 / P.$page < 4294967296 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (ipat_bound d.i0)
    have hmod : ipat d.i0 % P.$page < 4294967296 :=
      lt_of_le_of_lt (Nat.mod_le _ _) (ipat_bound d.i0)
    have hst : P.$st / bytesPerToken < 4294967296 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by have := hpre.$strideRange; omega)
    have hblk := hi.block
    rw [hi.len0, hi.len1] at hblk
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 3 t = some t1 ∧
        At t1 $test (($pred, .pred (validBit P L g d.block (laneOf L g) 0)) ::
          liveFacts P L g d $test) := by
      seg_fp h using
        all_goals idx_simp [hd, Site.hasPair, len1Reg, ite_true]
        all_goals
          simpa only [Nat.add_zero, Bool.false_eq_true, ↓reduceIte] using congrArg Value.pred hv
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 t1 = some t2 ∧
        At t2 $stop (liveFacts P L g d $stop) := by
      cases hab : validBit P L g d.block (laneOf L g) 0
      · rw [hab] at h1
        seg_fp h1 using
          all_goals idx_values
          all_goals idx_bits [coordValue, hab, Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hmod,
            Nat.mod_eq_of_lt hst]
      · rw [hab] at h1
        have hword := valid_row_bound hpre hbatch hq hblk hab
        rw [hrow] at hword
        change _ < 4294967296 at hword
        have hword64 : ipat d.i0 / P.$page * (P.$st / bytesPerToken) +
            ipat d.i0 % P.$page < 18446744073709551616 := by omega
        seg_fp h1 using
          all_goals idx_values
          all_goals idx_bits [coordValue, hrow, hab, Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hmod,
            Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hword, Nat.mod_eq_of_lt hword64]
    exact ⟨t2, run_comp hr1 hr2, h2⟩)

prove_low_coord low_coord_main, false, 2449, 2455, page, blockStride, blockStrideRange, 2452, 23
prove_low_coord low_coord_extra, true, 2537, 2543, extraPage, extraBlockStride,
  extraBlockStrideRange, 2540, 38

/-- The two cache loops use the same lane mask after setting the two position bits. -/
private theorem laneByte_of_masks (P : Params) (L : Launch) (g b : Nat) :
    ((if validBit P L g b (laneOf L g) 1 then 2 else 0) |||
      (if validBit P L g b (laneOf L g) 0 then 1 else 0)) *
       2 ^ (2 * (tidOf L g % 4)) = laneByte P L g b (laneOf L g) := by
  have hmod : laneOf L g % 4 = tidOf L g % 4 := Nat.mod_mod_of_dvd _ (by decide)
  unfold laneByte laneMask
  rw [hmod]
  cases validBit P L g b (laneOf L g) 0 <;> cases validBit P L g b (laneOf L g) 1 <;> rfl

private theorem extra_second_pos {lane block : Nat}
    (hn : 2 * lane + 64 * block + 1 < 2147483648) :
    truncBits 32 (truncBits 32 (BitVec.ofNat 64
        (64 + 2 * lane + 64 * block)) +
      truncBits 32 (BitVec.ofInt 64 (-63))) =
      truncBits 32 (BitVec.ofNat 64
        (2 * lane + 64 * block + 1)) := by
  have hx := add_negative_word
    (a := 64 + 2 * lane + 64 * block) (n := 63)
    (by omega) (by omega)
  have he : 64 + 2 * lane + 64 * block - 63 =
      2 * lane + 64 * block + 1 := by omega
  rw [he] at hx
  have hn32 : 2 * lane + 64 * block + 1 < 2 ^ 32 := by
    omega
  rw [truncBits_ofNat hn32 (by decide)]
  exact (Value.bits.inj hx).2

private theorem main_second_pos {lane block : Nat}
    (_h : 2 * lane + 64 * block + 1 < 2147483648) :
    2 * lane + 1 + 64 * block = 2 * lane + 64 * block + 1 := by omega

/-- Evaluate the selected second coordinate, then form and sign-extend the lane mask. -/
macro "prove_high_coord" name:ident "," extra:term "," start:num "," test:num "," pred:num ","
    combine:num "," cast:num "," stop:num "," page:ident "," st:ident "," strideRange:ident ","
    prefixCount:num "," position:term : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
      (hq : qOf L g < P.s_q) (hi : Inv P L g d) (hd : d.site = .waitFree $extra)
      (htag : isExtraBlock d.block (P.topkLen (eOf L g)) = $extra)
      (h : At t $start (liveFacts P L g d $start)) :
      ∃ t', run kernel asms L g ($prefixCount + 6) t = some t' ∧ At t' $stop
        (liveFacts P L g { d with site := .quad1 $extra } $stop) := by
    have hbody : d.site.inBody = true := by rw [hd]; rfl
    have hpair : d.site.hasPair = true := body_pair hbody
    have hslot := hi.slot1 hpair
    have hp := pos_word_bound hpre hbatch hi (b' := if $extra then
      d.block - numOrigBlocks d.len0 else d.block) (by simp)
    have hv := valid_compare_low hpre hbatch hq hi htag 1 hslot hp
    have hpos := $position hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hpos
    have hrow : rowBits P L g d.block (laneOf L g) 1 =
        ipat d.i1 / P.$page * (P.$st / bytesPerToken) + ipat d.i1 % P.$page := by
      simp [rowBits, slotPg, slotPage, slotStride, slotBlockStride, htag, ← hslot]
    have hr : 2 * (tidOf L g % 4) < 32 := by
      have := Nat.mod_lt (tidOf L g) (by decide : 0 < 4)
      omega
    have hdiv : ipat d.i1 / P.$page < 4294967296 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (ipat_bound d.i1)
    have hmod : ipat d.i1 % P.$page < 4294967296 :=
      lt_of_le_of_lt (Nat.mod_le _ _) (ipat_bound d.i1)
    have hst : P.$st / bytesPerToken < 4294967296 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by have := hpre.$strideRange; omega)
    have hblk := hi.block
    rw [hi.len0, hi.len1] at hblk
    have hbit : (if validBit P L g d.block (laneOf L g) 0 then 1 else 0) % 4294967296 =
        (if validBit P L g d.block (laneOf L g) 0 then 1 else 0) := by
      cases validBit P L g d.block (laneOf L g) 0 <;> rfl
    have hbit64 : (if validBit P L g d.block (laneOf L g) 0 then 1 else 0)
        % 18446744073709551616 = (if validBit P L g d.block (laneOf L g) 0 then 1 else 0) := by
      cases validBit P L g d.block (laneOf L g) 0 <;> rfl
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g $prefixCount t = some t1 ∧
        At t1 $test (($pred, .pred (validBit P L g d.block (laneOf L g) 1)) ::
          liveFacts P L g d $test) := by
      seg_fp h using
        all_goals idx_simp [hd, Site.hasPair, len1Reg, ite_true]
        all_goals simp only [hpos, truncBits_idem]
        all_goals simpa only [Bool.false_eq_true, ↓reduceIte] using congrArg Value.pred hv
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 4 t1 = some t2 ∧
        At t2 $combine (liveFacts P L g d $combine) := by
      cases hab : validBit P L g d.block (laneOf L g) 1
      · rw [hab] at h1
        seg_fp h1 using
          all_goals idx_values
          all_goals idx_bits [coordValue, hab, hbit, hbit64, Nat.mod_eq_of_lt hdiv,
            Nat.mod_eq_of_lt hmod, Nat.mod_eq_of_lt hst]
      · rw [hab] at h1
        have hword := valid_row_bound hpre hbatch hq hblk hab
        rw [hrow] at hword
        change _ < 4294967296 at hword
        have hword64 : ipat d.i1 / P.$page * (P.$st / bytesPerToken) +
            ipat d.i1 % P.$page < 18446744073709551616 := by omega
        seg_fp h1 using
          all_goals idx_values
          all_goals idx_bits [coordValue, hrow, hab, hbit, hbit64, Nat.mod_eq_of_lt hdiv,
            Nat.mod_eq_of_lt hmod, Nat.mod_eq_of_lt hst, Nat.mod_eq_of_lt hword,
            Nat.mod_eq_of_lt hword64]
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 $cast (liveFacts P L g d $cast) := by
      have hb := laneByte_of_masks P L g d.block
      have hbm : ((if validBit P L g d.block (laneOf L g) 1 then 2 else 0) |||
          (if validBit P L g d.block (laneOf L g) 0 then 1 else 0)) < 4294967296 := by
        cases validBit P L g d.block (laneOf L g) 0 <;>
          cases validBit P L g d.block (laneOf L g) 1 <;> decide
      have hshift : 2 * (tidOf L g % 4) < 4294967296 := by omega
      have hshift64 : 2 * (tidOf L g % 4) < 18446744073709551616 := by omega
      have hlt : ¬32 ≤ 2 * (tidOf L g % 4) := by omega
      have hbyte : laneByte P L g d.block (laneOf L g) < 4294967296 := by
        have := laneByte_lt P L g d.block (laneOf L g)
        omega
      seg_fp h2 using
        all_goals idx_values
        all_goals idx_bits [Nat.mod_eq_of_lt hshift, Nat.mod_eq_of_lt hshift64,
          Nat.mod_eq_of_lt hbm, hlt, hb, Nat.mod_eq_of_lt hbyte]
    obtain ⟨t4, hr4, h4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
        At t4 $stop (liveFacts P L g d $stop) := by
      seg_fp h3 using
        all_goals idx_values
        all_goals rw [sx8_value, laneWord]
    rw [body_live (pc := $stop) hbody (s := .quad1 $extra) rfl (by rw [hd]; rfl)] at h4
    exact ⟨t4, run_comp hr1 (run_comp hr2 (run_comp hr3 hr4)), h4⟩)

prove_high_coord high_coord_main, false, 2455, 2458, 26, 2462, 2463, 2464,
  page, blockStride, blockStrideRange, 3, main_second_pos

prove_high_coord high_coord_extra, true, 2543, 2547, 41, 2551, 2552, 2553,
  extraPage, extraBlockStride, extraBlockStrideRange, 4, extra_second_pos

private theorem main_index_tag {P : Params} {L : Launch} {g : Nat} {d : D}
    (hi : Inv P L g d) (hd : d.site = .waitFree false) :
    isExtraBlock d.block d.len0 = false :=
  isExtraBlock_false_iff.mpr (hi.tagMain (by rw [hd]; rfl))

private theorem extra_index_tag {P : Params} {L : Launch} {g : Nat} {d : D}
    (hi : Inv P L g d) (hd : d.site = .waitFree true) :
    isExtraBlock d.block d.len0 = true :=
  isExtraBlock_eq_true_iff.mpr (hi.tagExtra (by rw [hd]; rfl))

/-- A failed poll retries, and a successful poll computes coordinates up to the first shuffle. -/
macro "prove_wait_step" name:ident "," extra:term "," start:num "," fire:term "," retry:term ","
    bra:term "," low:term "," high:term "," tag:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q)
      (d : D) (hd : d.site = .waitFree $extra) : (code P L g).StepAt d := by
    apply stepAt_of
    intro t e u ins hat hi hc hf
    obtain ⟨ok, acq, sc, he, h⟩ := $fire hpre hd hi (atD_code.mp hat) hc hf
    cases ok
    · obtain ⟨t', hr, ht⟩ := $retry h
      have ha := atD_of_liveFacts (d := d) (by rw [hd]; rfl) (by rw [hd]; rfl)
        (by rw [accOf, hd]) ht
      exact .inl (.inr ⟨d, t', by simp [next, nextSite, hd, he], run_rtg hr,
        atD_code.mpr ha, hi⟩)
    · let d' := { d with site := Site.quad1 $extra }
      have hnext : next P L g d e = some (some d') := by simp [next, nextSite, hd, he, d']
      have htag : isExtraBlock d.block (P.topkLen (eOf L g)) = $extra := by
        rw [← hi.len0]
        exact $tag hi hd
      obtain ⟨t1, hr1, hb⟩ := bra_at (L := L) (g := g) (pick := true) $bra h
        (by simp) (by decide) (by decide)
      have hb' : At t1 $start (liveFacts P L g d $start) := at_of_cons hb (by lit_mem)
      obtain ⟨t2, hr2, h2⟩ := $low hpre hbatch hq hi hd htag hb'
      obtain ⟨t3, hr3, h3⟩ := $high hpre hbatch hq hi hd htag h2
      have ht := atD_of_liveFacts (d := d') rfl rfl rfl h3
      have hi' := inv_body_move (s := .quad1 $extra) hi (by rw [hd]; rfl) rfl (by rw [hd]; rfl)
      exact .inl (.inr ⟨d', t3, hnext, run_rtg (run_comp hr1 (run_comp hr2 hr3)),
        atD_code.mpr ht, hi'⟩))

prove_wait_step stepAt_waitFreeMain, false, 2449,
  fire_free_main, retry_free_main, Flow.code_2447, low_coord_main, high_coord_main,
  main_index_tag

prove_wait_step stepAt_waitFreeExtra, true, 2537,
  fire_free_extra, retry_free_extra, Flow.code_2535, low_coord_extra, high_coord_extra,
  extra_index_tag

/-! ## Writing the index ring -/

/-- The two-word shared store writes the current element at its aligned vector address. -/
private theorem fires_coord_word {L : Launch} {g : Nat} {t u : TState} {pc base a lo hi : Nat}
    {e : Event} {value : Nat} (hr : t.regs base = some (b32 a)) (ha : a + 221728 < 2 ^ 32)
    (hal : (a + 221728) % 8 = 0) (hs : t.sub < 2)
    (hv : t.regs (if t.sub = 0 then lo else hi) = some (b32 value))
    (hf : Fires pc (eventTmpl asms L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := 2,
        addr := ⟨.reg base 32, 221728⟩, srcs := [.reg lo, .reg hi] })) e (some u)) :
    ∃ acc, e.kind = .wr acc (b32 value).toBytes ∧
      acc.loc = ⟨.shared, ctaOf L g, a + 221728 + 4 * t.sub⟩ ∧ acc.size = 4 ∧
      u = afterStore t [.reg lo, .reg hi] := by
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32)
    rfl rfl rfl rfl rfl] at hf
  have heff : effAddr L g t .shared base 221728 =
      .ok ⟨.shared, g / L.block, a + 221728⟩ := effAddr_b32_off hr ha
  simp only [DType.width, storeTmpl, heff, bind, Except.bind] at hf
  have hacc := elemAcc_ok (loc := ⟨.shared, g / L.block, a + 221728⟩)
    (n := 32 / 8) (count := ([.reg lo, .reg hi] : List Opnd).length) (j := t.sub)
    (by decide) (by simpa using hal)
  rw [hacc] at hf
  have hsrc : ([.reg lo, .reg hi] : List Opnd)[t.sub]? =
      some (.reg (if t.sub = 0 then lo else hi)) := by
    have hs' : t.sub = 0 ∨ t.sub = 1 := by omega
    rcases hs' with h | h <;> simp [h]
  simp only [hsrc, readValue, readReg, hv, pure, Except.pure] at hf
  have hval : storeValue 32 (b32 value) = .ok (b32 value) := by rfl
  rw [hval] at hf
  simp only [Fires] at hf
  exact ⟨_, by rw [hf.1], by simp [Loc.at, ctaOf], rfl, Option.some.inj hf.2⟩

private theorem tid_mod_quad (L : Launch) (g : Nat) :
    tidOf L g % 4 = laneOf L g % 4 :=
  (Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 32)).symm

private theorem index_shared_align {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) : L.sharedBase % 8 = 0 := by
  rw [hpre.sharedBase]
  have h := hpre.sharedAlignment
  omega

/-- Recover the coordinate word, its byte footprint, and the vector store continuation. -/
macro "prove_coord_fire" name:ident "," extra:term "," pc:num "," base:num ","
    lo:num "," hiReg:num "," opcode:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
      {t u : TState} {ins : Instr} {e : Event} {high : Bool}
      (hpre : Pre P L mem0) (hd : d.site = .coord $extra high) (hi : Inv P L g d)
      (hat : AtD P L g d t) (hc : kernel.code[d.site.pc]? = some ins)
      (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
      ∃ acc, e.kind = .wr acc (b32 (coordValue P L g d.block (laneOf L g) d.site.sub)).toBytes ∧
        acc.loc = ⟨.shared, ctaOf L g, L.sharedBase + coordOff L g d.phase + 4 * d.site.sub⟩ ∧
        acc.size = 4 ∧
        u = if high then { PTX.next t with sub := 0 } else { t with sub := 1 } := by
    have hpc : d.site.pc = $pc := by rw [hd]; rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $opcode)
    subst ins
    have hholds := hat.2.2.2.2
    rw [facts_eq_liveFacts (d := d) rfl, hpc] at hholds
    have hbase : t.regs $base = some (sb L (8 * laneOf L g + 256 * d.phase)) :=
      holds_mem hholds (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
        (by decide +kernel) (by idx_values))
    have hwindow := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have hphase := hi.phase
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    have hbound : L.sharedBase + (8 * laneOf L g + 256 * d.phase) + 221728 < 2 ^ 32 := by
      omega
    have hal : (L.sharedBase + (8 * laneOf L g + 256 * d.phase) + 221728) % 8 = 0 := by
      have := index_shared_align hpre
      omega
    have hsub : t.sub = if high then 1 else 0 := by
      rw [hat.2.1, hd]
      cases high <;> rfl
    have hs : t.sub < 2 := by cases high <;> simp [hsub]
    have hval : t.regs (if t.sub = 0 then $lo else $hiReg) =
        some (b32 (coordValue P L g d.block (laneOf L g) d.site.sub)) := by
      cases high
      · simp only [hsub, hd, Site.sub, ite_true]
        exact holds_mem hholds (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
          (by decide +kernel) (by idx_values))
      · simp only [hsub, hd, Site.sub, Nat.one_ne_zero, ↓reduceIte]
        exact holds_mem hholds (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
          (by decide +kernel) (by idx_values))
    obtain ⟨acc, he, hl, hsize, hu⟩ := fires_coord_word hbase hbound hal hs hval hf
    refine ⟨acc, he, ?_, hsize, ?_⟩
    · rw [hl, hat.2.1]
      unfold coordOff
      congr 1
      omega
    · cases high
      · rw [hu, afterStore_mid (by simp [hsub])]
        simp [hsub]
      · rw [hu, afterStore_last (by simp [hsub])]
        rfl)

prove_coord_fire fires_coord_main, false, 2471, 612, 600, 604, Flow.code_2471
prove_coord_fire fires_coord_extra, true, 2560, 651, 638, 643, Flow.code_2560

/-- The validity-store instruction writes the low byte of the lane's reduced word. -/
macro "prove_valid_fire" name:ident "," extra:term "," pc:num "," base:num ","
    src:num "," opcode:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
      {t u : TState} {ins : Instr} {e : Event}
      (hpre : Pre P L mem0) (hd : d.site = .valid $extra) (hi : Inv P L g d)
      (hat : AtD P L g d t) (hc : kernel.code[d.site.pc]? = some ins)
      (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
      ∃ acc, e.kind = .wr acc (.bits 8
          (BitVec.ofNat 64 (validWord P L g d.block (laneOf L g) % 256)) : Value).toBytes ∧
        acc.loc = ⟨.shared, ctaOf L g, L.sharedBase + validOff L g d.phase⟩ ∧
        acc.size = 1 ∧ u = PTX.next t := by
    have hpc : d.site.pc = $pc := by rw [hd]; rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $opcode)
    subst ins
    have ht := at_body_event hat (by rw [hd]; rfl) (by rw [accOf, hd])
    rw [hpc] at ht
    have hbase : t.regs $base = some (sb L (8 * d.phase + laneOf L g / 4)) :=
      holds_mem ht.2.2.2.2 (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
        (by decide +kernel) (by idx_values))
    have hsrc : t.regs $src = some (b32 (validWord P L g d.block (laneOf L g))) :=
      holds_mem ht.2.2.2.2 (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
        (by decide +kernel) (by idx_values))
    have hwindow := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have hphase := hi.phase
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    have haddr : L.sharedBase + (8 * d.phase + laneOf L g / 4) + 221696 < 2 ^ 32 := by
      omega
    obtain ⟨w, hw, acc, he, hl, hsize⟩ :=
      fires_st_val (off := 221696) hbase haddr ht.2.1 hsrc hf
    have hword : storeValue 8 (b32 (validWord P L g d.block (laneOf L g))) =
        .ok (.bits 8 (BitVec.ofNat 64 (validWord P L g d.block (laneOf L g) % 256))) := by
      have hm (n : Nat) : n % 18446744073709551616 % 256 = n % 256 :=
        Nat.mod_mod_of_dvd _ (by decide)
      nf_simp [storeValue, Value.bitPattern, Value.bytes, pure, Except.pure, hm]
    have hweq := Except.ok.inj (hw.symm.trans hword)
    obtain ⟨hu, _⟩ := fires_stv_after
      (srcs := [.reg $src]) (lsp := .shared) rfl rfl hf
    refine ⟨acc, hweq ▸ he, ?_, hsize, ?_⟩
    · rw [hl]
      unfold validOff ctaOf
      congr 1
      omega
    · rw [hu, afterStore_last (by simp [ht.2.1])]
      simp [PTX.next, ht.2.1])

prove_valid_fire fires_valid_main, false, 2474, 613, 508, Flow.code_2474
prove_valid_fire fires_valid_extra, true, 2563, 652, 511, Flow.code_2563

/-- The byte written by the leader contains exactly the four lanes' validity masks. -/
theorem validWord_leader (P : Params) (L : Launch) (g b l : Nat)
    (hlane : l < 32) (hlead : l % 4 = 0) :
    validWord P L g b l % 256 = quadByte P L g b l := by
  have hx : l ^^^ 1 = l + 1 ∧ l ^^^ 2 = l + 2 ∧ (l + 2) ^^^ 1 = l + 3 := by
    interval_cases hl : l <;> first | decide | simp_all
  obtain ⟨h1, h2, h3⟩ := hx
  simp only [validWord, quadWord, pairWord, laneWord, quadByte, mod256_or, sx8_mod256,
    Nat.mod_eq_of_lt (laneByte_lt P L g b _), h1, h2, h3]
  rw [Nat.or_comm (laneByte P L g b (l + 1)) (laneByte P L g b l),
    Nat.or_assoc (laneByte P L g b l ||| laneByte P L g b (l + 1))
      (laneByte P L g b (l + 2)) (laneByte P L g b (l + 3))]

/-- From a valid-byte store, execution computes the ready barrier address. -/
macro "prove_valid_step" name:ident "," extra:term "," pc:num "," after:num ","
    stop:num "," fire:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      (hpre : Pre P L mem0) (d : D) (hd : d.site = .valid $extra) :
      (code P L g).StepAt d := by
    apply stepAt_of
    intro t e u ins hat hi hc hf
    have hat' := atD_code.mp hat
    obtain ⟨acc, he, hl, ha, hu⟩ := $fire hpre hd hi hat' hc hf
    let d' := { d with site := Site.ready $extra }
    have hpc : d.site.pc = $pc := by rw [hd]; rfl
    have hb : d.site.inBody = true := by rw [hd]; rfl
    have ht := at_body_event hat' (by rw [hd]; rfl) (by rw [accOf, hd])
    rw [hpc] at ht
    have hstart : At u $after (liveFacts P L g d $pc) := by rw [hu]; exact At.next ht
    have hwin := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have hphase := hi.phase
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel asms L g 1 u = some t' ∧
        At t' $stop (liveFacts P L g d $stop) := by
      seg_fp hstart using
        all_goals idx_values
        all_goals norm_bits [sb, readyOff]
    rw [body_live (pc := $stop) hb (s := .ready $extra) rfl (by rw [hd]; rfl)] at ht'
    have hAt := atD_of_liveFacts (d := d') rfl rfl rfl ht'
    have hi' := inv_body_move (s := .ready $extra) hi hb rfl (by rw [hd]; rfl)
    exact .inl (.inr ⟨d', t', by simp [next, nextSite, hd, he, hl, ha, d'],
      run_rtg hr, atD_code.mpr hAt, hi'⟩))

prove_valid_step stepAt_validMain, false, 2474, 2475, 2476, fires_valid_main
prove_valid_step stepAt_validExtra, true, 2563, 2564, 2565, fires_valid_extra

/-- The vector store's first element leaves its register facts and selects the second element. -/
private theorem at_coord_second {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    {extra : Bool} (hd : d.site = .coord extra false) (hat : AtD P L g d t) :
    AtD P L g { d with site := .coord extra true } { t with sub := 1 } := by
  have hp : d.site.pc = (Site.coord extra true).pc := by rw [hd]; cases extra <;> rfl
  have hb : d.site.inBody = true := by rw [hd]; rfl
  refine ⟨hat.1.trans hp, rfl, ?_, hat.2.2.2.1, ?_⟩
  · simp only [accOf]
    simpa [accOf, hd] using hat.2.2.1
  · have hf := hat.2.2.2.2
    rw [facts_eq_liveFacts rfl, hp, body_live (pc := (Site.coord extra true).pc) hb
      (s := .coord extra true) rfl (by rw [hd]; rfl)] at hf
    rw [facts_eq_liveFacts rfl]
    exact hf

/-- The last word continues to the designated lane's byte store or to the ready arrival. -/
macro "prove_coord_step" name:ident "," extra:term "," pc:num "," bran:num "," val:num ","
    valid:num "," readyBase:num "," ready:num "," p:num "," bra:term "," fire:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      (hpre : Pre P L mem0) (d : D) {high : Bool} (hd : d.site = .coord $extra high) :
      (code P L g).StepAt d := by
    apply stepAt_of
    intro t e u ins hat hi hc hf
    have hat' := atD_code.mp hat
    obtain ⟨acc, he, hl, ha, hu⟩ := $fire hpre hd hi hat' hc hf
    have hb : d.site.inBody = true := by rw [hd]; rfl
    cases high
    · let d' := { d with site := Site.coord $extra true }
      have hAt : AtD P L g d' u := by
        rw [hu]
        exact at_coord_second hd hat'
      have hi' := inv_body_move (s := .coord $extra true) hi hb rfl (by rw [hd]; rfl)
      exact .inl (.inr ⟨d', u, by simp [next, nextSite, hd, he, hl, ha, d'],
        .refl, atD_code.mpr hAt, hi'⟩)
    · have hpc : d.site.pc = $pc := by rw [hd]; rfl
      have ht : At u $bran (liveFacts P L g d $pc) := by
        rw [hu]
        refine ⟨?_, rfl, ?_, hat'.2.2.2.1, ?_⟩
        · change t.pc + 1 = $bran
          rw [hat'.1, hpc]
        · change t.acc = []
          rw [hat'.2.2.1, accOf, hd]
        · have h := hat'.2.2.2.2
          rw [facts_eq_liveFacts rfl, hpc] at h
          exact h
      have hwin := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
      have hphase := hi.phase
      have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
      by_cases hleader : laneOf L g % 4 = 0
      · let d' := { d with site := Site.valid $extra }
        have hp : ($p, .pred false) ∈ liveFacts P L g d $pc := by
          apply live_mem (by decide +kernel)
          idx_values
          simp [tid_mod_quad, hleader]
        obtain ⟨t1, hr1, h1⟩ := bra_at (L := L) (g := g) (pick := false) $bra ht hp
          (by decide) (by decide)
        have h1' : At t1 $val (liveFacts P L g d $pc) := h1
        obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
            At t2 $valid (liveFacts P L g d $valid) := by
          seg_fp h1' using
            all_goals idx_values
            all_goals norm_bits [sb]
        rw [body_live (pc := $valid) hb (s := .valid $extra) rfl (by rw [hd]; rfl)] at h2
        have hAt := atD_of_liveFacts (d := d') rfl rfl rfl h2
        have hi' := inv_body_move (s := .valid $extra) hi hb rfl (by rw [hd]; rfl)
        exact .inl (.inr ⟨d', t2, by simp [next, nextSite, hd, he, hl, ha, hleader, d'],
          run_rtg (run_comp hr1 hr2), atD_code.mpr hAt, hi'⟩)
      · let d' := { d with site := Site.ready $extra }
        have hp : ($p, .pred true) ∈ liveFacts P L g d $pc := by
          apply live_mem (by decide +kernel)
          idx_values
          simp [tid_mod_quad, hleader]
        obtain ⟨t1, hr1, h1⟩ := bra_at (L := L) (g := g) (pick := true) $bra ht hp
          (by decide) (by decide)
        have h1' : At t1 $readyBase (liveFacts P L g d $pc) := h1
        obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
            At t2 $ready (liveFacts P L g d $ready) := by
          seg_fp h1' using
            all_goals idx_values
            all_goals norm_bits [sb, readyOff]
        rw [body_live (pc := $ready) hb (s := .ready $extra) rfl (by rw [hd]; rfl)] at h2
        have hAt := atD_of_liveFacts (d := d') rfl rfl rfl h2
        have hi' := inv_body_move (s := .ready $extra) hi hb rfl (by rw [hd]; rfl)
        exact .inl (.inr ⟨d', t2, by simp [next, nextSite, hd, he, hl, ha, hleader, d'],
          run_rtg (run_comp hr1 hr2), atD_code.mpr hAt, hi'⟩))

prove_coord_step stepAt_coordMain, false, 2471, 2472, 2473, 2474, 2475, 2476, 20,
  Flow.code_2472, fires_coord_main

prove_coord_step stepAt_coordExtra, true, 2560, 2561, 2562, 2563, 2564, 2565, 35,
  Flow.code_2561, fires_coord_extra

/-! ## Publishing the ready slot -/

/-- The producer publishes one completed lane to the current ring slot. -/
macro "prove_ready_fire" name:ident "," extra:term "," pc:num "," after:num ","
    base:num "," opcode:term : command =>
  `(command| theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
      {t u : TState} {ins : Instr} {e : Event}
      (hpre : Pre P L mem0) (hd : d.site = .ready $extra) (hi : Inv P L g d)
      (hat : AtD P L g d t) (hc : kernel.code[d.site.pc]? = some ins)
      (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
      ∃ rel sc, e.kind = .arrive ⟨.shared, ctaOf L g, L.sharedBase + readyOff d.phase⟩
        0 1 rel sc ∧ At u $after (liveFacts P L g d $after) := by
    have hpc : d.site.pc = $pc := by rw [hd]; rfl
    rw [hpc] at hc hf
    have hins := Option.some.inj (hc.symm.trans $opcode)
    subst ins
    have ht := at_body_event hat (by rw [hd]; rfl) (by rw [accOf, hd])
    rw [hpc] at ht
    have hreg : t.regs $base = some (sb L (readyOff d.phase)) :=
      holds_mem ht.2.2.2.2 (live_mem (P := P) (L := L) (g := g) (d := d) (pc := $pc)
        (by decide +kernel) (by idx_values))
    have hphase := hi.phase
    have hwin := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.sharedBase_lt hpre
    have ha : L.sharedBase + readyOff d.phase < 2 ^ 32 := by
      unfold readyOff
      omega
    have ha8 : (L.sharedBase + readyOff d.phase) % 8 = 0 := by
      have := index_shared_align hpre
      unfold readyOff
      omega
    have hm := mbarLoc_b32 (L := L) (g := g) hreg ha ha8
    obtain ⟨rel, sc, he, hu⟩ := fires_arrive_at (cluster := false) hm rfl rfl hf
    have hAt := At.next ht
    have hframe := holds_factsFrom_mono hAt.2.2.2.2 (by
      show ∀ r ∈ preLive $after, r ∈ preLive $pc
      lit_mem)
    rw [← hu u rfl] at hAt hframe
    exact ⟨rel, sc, by rw [he]; rfl, hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, hframe⟩)

prove_ready_fire fires_ready_main, false, 2476, 2477, 614, Flow.code_2476
prove_ready_fire fires_ready_extra, true, 2565, 2566, 653, Flow.code_2565

/-- The ring slot and free-barrier parity advance after publishing a block. -/
private def advancePhase (d : D) : D :=
  { d with phase := (d.phase + 1) % 4, par := if d.phase == 3 then 1 - d.par else d.par }

/-- Both loops use an identical parity update and signed remainder by four. -/
macro "prove_ready_phase" name:ident "," start:num "," pcase:num "," pred1:num ","
    test:num "," pred2:num "," stop:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
      (hi : Inv P L g d) (h : At t $start (liveFacts P L g d $start)) :
      ∃ t', run kernel asms L g 11 t = some t' ∧
        At t' $stop (liveFacts P L g (advancePhase d) $stop) := by
    have hphase := hi.phase
    have hpar := hi.par
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
        At t1 $pcase (($pred1, .pred (decide (d.phase = 3))) :: liveFacts P L g d $pcase) := by
      seg_fp h using
        all_goals idx_values
        all_goals norm_signed
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 3 t1 = some t2 ∧
        At t2 $test (($pred2, .pred (decide ((advancePhase d).par = 1))) ::
          liveFacts P L g d $test) := by
      by_cases hb : d.phase = 3
      · simp only [hb, decide_true] at h1
        seg_fp h1 using
          all_goals idx_values
          all_goals (interval_cases hpar' : d.par <;> simp [advancePhase, hb, hpar'] <;> decide)
      · simp only [hb, decide_false] at h1
        seg_fp h1 using
          all_goals idx_values
          all_goals (interval_cases hpar' : d.par <;> simp [advancePhase, hb, hpar'] <;> decide)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 7 t2 = some t3 ∧
        At t3 $stop (liveFacts P L g (advancePhase d) $stop) := by
      have hnew : (advancePhase d).par < 2 := by
        simp only [advancePhase]
        split <;> omega
      by_cases hb : (advancePhase d).par = 1
      · simp only [hb, decide_true] at h2
        seg_fp h2 using
          all_goals idx_values
          all_goals first
            | (rw [hb]; rfl)
            | (interval_cases hph : d.phase <;> simp [advancePhase, hph] <;> decide)
      · simp only [hb, decide_false] at h2
        have hzero : (advancePhase d).par = 0 := by omega
        seg_fp h2 using
          all_goals idx_values
          all_goals first
            | (rw [hzero]; rfl)
            | (interval_cases hph : d.phase <;> simp [advancePhase, hph] <;> decide)
    exact ⟨t3, run_comp hr1 (run_comp hr2 hr3), h3⟩)

prove_ready_phase main_ready_phase, 2477, 2478, 29, 2481, 30, 2488
prove_ready_phase extra_ready_phase, 2566, 2567, 44, 2570, 45, 2577

/-! ## Continuing after publication -/

/-- Before the next loop head, the previous look-ahead words are the current pair. -/
private def advancePair (d : D) (extra : Bool) : D :=
  let haveNext := d.block + 1 < pairLimit d extra
  let afterPhase := advancePhase d
  { afterPhase with
    block := d.block + 1
    i0 := if haveNext then d.n0 else d.i0
    i1 := if haveNext then d.n1 else d.i1 }

private def loopEndValue (P : Params) (L : Launch) (g : Nat) (d : D) (extra : Bool)
    (r : Nat) : Value :=
  if r = (if extra then 2978 else 2970) then
    b32 ((d.block + 1 + (2 ^ 32 - pairLimit d extra)) % 2 ^ 32)
  else if r = 2972 ∨ r = 2980 then valueOf P L g (advancePhase d) r
  else if r = (if extra then 2983 else 2975) ∨ r = (if extra then 2984 else 2976) then
    valueOf P L g d r
  else valueOf P L g (advancePair d extra) r

private theorem loopEnd_nonzero {b limit : Nat} (h : b < limit) (hlt : limit < 2147483648) :
    PTX.compare .ne .b 32
      (truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 (b + (2 ^ 32 - limit))) +
        truncBits 32 (BitVec.ofInt 64 1)))) (truncBits 32 (BitVec.ofInt 64 0)) =
      decide (b + 1 < limit) := by
  norm_signed

private theorem ipat_select (p : Prop) [Decidable p] (x y : Int) :
    ipat (if p then x else y) = if p then ipat x else ipat y := by
  split <;> rfl

/-- The loop's position and current pair advance before the back-edge predicate is consumed. -/
macro "prove_ready_tail" name:ident "," extra:term "," start:num "," stop:num ","
    pred:num "," count:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
      (hd : d.site = .ready $extra) (hi : Inv P L g d)
      (h : At t $start (liveFacts P L g (advancePhase d) $start)) :
      ∃ t', run kernel asms L g $count t = some t' ∧
        At t' $stop (($pred, .pred (decide (d.block + 1 < pairLimit d $extra))) ::
          factsFrom (preLive $stop) (loopEndValue P L g d $extra)) := by
    have hcount := total_count_lt hpre hbatch hi
    have hlimit : pairLimit d $extra < 2147483648 := by
      have hm := numOrigBlocks_le_totalBlocks d.len0 d.len1
      simp only [pairLimit, Bool.false_eq_true, ↓reduceIte]
      omega
    have hblock : d.block < pairLimit d $extra := by
      first
      | exact hi.block
      | exact hi.tagMain (by rw [hd]; rfl)
    have htag := hi.tagExtra
    have hpred := congrArg Value.pred (loopEnd_nonzero hblock hlimit)
    have hp := hpre.paddedRange _ hbatch
    rw [← hi.len0, ← hi.len1] at hp
    have ht := Nat.div_mul_le_self (origPadded d.len0 + ceilToMultiple d.len1 topkBlock) 64
    change totalBlocks d.len0 d.len1 * 64 ≤ _ at ht
    have hblk := hi.block
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    have hpos (he : numOrigBlocks d.len0 ≤ d.block) :
        d.block - numOrigBlocks d.len0 + 1 = d.block + 1 - numOrigBlocks d.len0 := by
      omega
    seg_fp h using
      all_goals idx_simp [advancePhase, advancePair, loopEndValue, pairLimit, hd, Site.hasPair,
        len1Reg, countReg, ipat_select, Bool.false_eq_true, Nat.reduceEqDiff, true_or, false_or,
        ↓reduceIte, ite_true]
      all_goals (try rw [← hpos (htag (by rw [hd]; rfl))])
      all_goals first
        | exact hpred
        | (idx_bits [hpos, pairAddr, extraPairAddr]; done)
        | (nf_simp [hpos]; omega))

prove_ready_tail main_ready_tail, false, 2488, 2494, 31, 6
prove_ready_tail extra_ready_tail, true, 2577, 2582, 46, 5

/-- The terminal loop exit constructs the named-barrier operands. -/
private theorem run_index_final {P : Params} {L : Launch} {g : Nat}
    {t : TState} {d : D} (h : At t 2583 []) :
    ∃ u, run kernel asms L g 2 t = some u ∧ At u 2585 (liveFacts P L g d 2585) := by
  seg_fp h using
    all_goals idx_values
    all_goals decide

private def extraEntryWords (d : D) : D :=
  { advancePhase d with site := .pair true true false, block := d.block + 1, i0 := 0, i1 := 0 }

private theorem loop_branch_frame {P : Params} {L : Launch} {g pc src p : Nat}
    {t : TState} {d : D} {flag : Bool} {val : Nat → Value}
    (h : At t pc ((p, .pred flag) :: factsFrom (preLive src) val))
    (hl : ∀ r ∈ preLive pc, r ∈ preLive src)
    (hv : ∀ r ∈ preLive pc, val r = valueOf P L g d r) :
    At t pc (liveFacts P L g d pc) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  apply holds_of_pointwise
  intro r hr
  rw [← hv r hr]
  exact holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (mem_factsFrom (hl r hr)))

private theorem main_to_extra_raw {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (hd : d.site = .ready false)
    (h : At t 2495 ((31, .pred (decide (d.block + 1 < pairLimit d false))) ::
      factsFrom (preLive 2494) (loopEndValue P L g d false))) :
    At t 2495 (liveFacts P L g (extraEntryWords d) 2495) := by
  apply loop_branch_frame h (by lit_mem)
  intro r hr
  change r ∈ preLive 2495 at hr
  rw [show preLive 2495 = [456, 491, 496, 498, 500, 501, 502, 503, 505, 2969, 2977, 2980, 3014]
    from by decide +kernel] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    idx_simp [loopEndValue, advancePair, extraEntryWords, advancePhase, hd, Site.hasPair,
      len1Reg, countReg, Bool.false_eq_true, Nat.reduceEqDiff, true_or, false_or, ↓reduceIte]

private theorem main_to_extra {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (hd : d.site = .ready false) (hi : Inv P L g d)
    (hlast : ¬ d.block + 1 < numOrigBlocks d.len0)
    (h : At t 2495 (liveFacts P L g (extraEntryWords d) 2495)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧ AtD P L g (afterReady d) t' := by
  let w := extraEntryWords d
  have hcount := total_count_lt hpre hbatch hi
  have hle := numOrigBlocks_le_totalBlocks d.len0 d.len1
  have hnum : numOrigBlocks d.len0 < 2 ^ 31 := by omega
  have hpos := hi.tagMain (by rw [hd]; rfl)
  have heq : d.block + 1 = numOrigBlocks d.len0 := by omega
  obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 3 t = some t1 ∧
      At t1 2498 ((32, .pred (decide (totalBlocks d.len0 d.len1 ≤ numOrigBlocks d.len0))) ::
        liveFacts P L g w 2498) := by
    seg_fp h using
      all_goals idx_simp [w, extraEntryWords, advancePhase, Site.hasPair, countReg,
        Bool.false_eq_true, ↓reduceIte]
      all_goals norm_signed
  by_cases htail : d.block + 1 < totalBlocks d.len0 d.len1
  · have htail' : numOrigBlocks d.len0 < totalBlocks d.len0 d.len1 := by omega
    have hsite : afterReady d = w := by
      simp [w, extraEntryWords, advancePhase, afterReady, htail', heq]
    have ht : ¬ totalBlocks d.len0 d.len1 ≤ numOrigBlocks d.len0 := by omega
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2498 h1
      (by simp [ht]) (by decide) (by decide)
    have h2' : At t2 2499 (liveFacts P L g w 2499) := at_of_cons h2 (by lit_mem)
    have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 2501 (liveFacts P L g w 2501) := by
      seg_fp h2' using
        all_goals idx_bits [extraPairAddr, Nat.mul_zero, Nat.add_zero]
    rw [hsite]
    exact ⟨t3, run_rtg (run_comp hr1 (run_comp hr2 hr3)),
      atD_of_liveFacts (d := w) rfl rfl rfl h3⟩
  · have hsite : (afterReady d).site = .barrier := by simp [afterReady, hlast, htail]
    have ht : totalBlocks d.len0 d.len1 ≤ numOrigBlocks d.len0 := by omega
    obtain ⟨t2, hr2, h2⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2498 h1
      (by simp [ht]) (by decide) (by decide)
    have h2' : At t2 2502 (liveFacts P L g w 2502) := at_of_cons h2 (by lit_mem)
    obtain ⟨t3, hr3, h3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 2503 ((33, .pred true) :: liveFacts P L g w 2503) := by
      seg_fp h2' using
        all_goals idx_simp [w, extraEntryWords, advancePhase, countReg]
        all_goals norm_signed
    obtain ⟨t4, hr4, h4⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2503 h3
      (by simp) (by decide) (by decide)
    have h4' : At t4 2583 [] := ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, trivial⟩
    obtain ⟨t5, hr5, h5⟩ := run_index_final (d := afterReady d) h4'
    exact ⟨t5, run_rtg (run_comp (run_comp hr1 hr2) (run_comp hr3 (run_comp hr4 hr5))),
      atD_of_liveFacts (d := afterReady d) (by rw [hsite]; rfl)
        (by rw [hsite]; rfl) (by rw [accOf, hsite]) h5⟩

private theorem extra_finished {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    (hd : d.site = .ready true) (hi : Inv P L g d)
    (hlast : ¬ d.block + 1 < totalBlocks d.len0 d.len1)
    (h : At t 2582 ((46, .pred (decide (d.block + 1 < pairLimit d true))) ::
      factsFrom (preLive 2582) (loopEndValue P L g d true))) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧ AtD P L g (afterReady d) t' := by
  have hpos := hi.tagExtra (by rw [hd]; rfl)
  have hnot : ¬ d.block + 1 < numOrigBlocks d.len0 := by omega
  have hsite : (afterReady d).site = .barrier := by simp [afterReady, hnot, hlast]
  obtain ⟨t1, hr1, h1⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2582 h
    (by simp [pairLimit, hlast]) (by decide) (by decide)
  have h1' : At t1 2583 [] := ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, trivial⟩
  obtain ⟨t2, hr2, h2⟩ := run_index_final (d := afterReady d) h1'
  exact ⟨t2, run_rtg (run_comp hr1 hr2),
    atD_of_liveFacts (d := afterReady d) (by rw [hsite]; rfl)
      (by rw [hsite]; rfl) (by rw [accOf, hsite]) h2⟩

private def loopHeadValue (P : Params) (L : Launch) (g : Nat) (d : D) (extra : Bool)
    (r : Nat) : Value :=
  if r = (if extra then 2980 else 2972) then b32 (d.block + 1)
  else valueOf P L g (advancePair d extra) r

/-- The back edge has advanced all registers except the next-prefetch counter. -/
macro "prove_head_raw" name:ident "," extra:term "," src:num "," pc:num "," pred:num ","
    live:term : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
      (hd : d.site = .ready $extra) (hnext : d.block + 1 < pairLimit d $extra)
      (hlimit : pairLimit d $extra < 4294967296)
      (h : At t $pc (($pred, .pred (decide (d.block + 1 < pairLimit d $extra))) ::
        factsFrom (preLive $src) (loopEndValue P L g d $extra))) :
      At t $pc (factsFrom (preLive $pc) (loopHeadValue P L g d $extra)) := by
    have hv : ∀ r ∈ preLive $pc, loopEndValue P L g d $extra r =
        loopHeadValue P L g d $extra r := by
      intro r hr
      have hmod : (d.block + 1 + (2 ^ 32 - pairLimit d $extra)) % 2 ^ 32 =
          d.block + 1 + (2 ^ 32 - pairLimit d $extra) := Nat.mod_eq_of_lt (by omega)
      simp only [pairLimit, Bool.false_eq_true, ↓reduceIte] at hnext hmod
      change r ∈ preLive $pc at hr
      rw [show preLive $pc = $live from by decide +kernel] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      repeat' rcases hr with h | hr
      all_goals
        try subst r
        idx_simp [loopEndValue, loopHeadValue, advancePair, advancePhase, hd, countReg,
          pairLimit, hnext, hmod, ite_self, len1Reg, Site.hasPair, Bool.false_eq_true,
          Nat.reduceEqDiff, ↓reduceIte, ite_true, false_or, true_or]
        try omega
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    apply holds_of_pointwise
    have hm : ∀ r ∈ preLive $pc, r ∈ preLive $src := by lit_mem
    intro r hr
    rw [← hv r hr]
    exact holds_mem h.2.2.2.2 (List.mem_cons_of_mem _ (mem_factsFrom (hm r hr))))

prove_head_raw main_head_raw, false, 2494, 2426, 31,
  [456, 491, 496, 497, 498, 500, 501, 502, 503, 504, 505, 506, 2968, 2969, 2970, 2971, 2972,
    2973, 2974, 2975, 2976, 2977, 2980, 3014, 4029]

prove_head_raw extra_head_raw, true, 2582, 2512, 46,
  [456, 498, 500, 501, 502, 503, 505, 509, 2969, 2977, 2978, 2979, 2980, 2981, 2982,
    2983, 2984, 3014]

/-- The loop head increments the look-ahead counter and tests whether a pair follows. -/
macro "prove_loop_head" name:ident "," extra:term "," start:num "," mid:num "," stop:num ","
    pred:num : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {g : Nat}
      {d : D} {t : TState} (hd : d.site = .ready $extra)
      (hlimit : pairLimit d $extra < 2147483648) (hnext : d.block + 1 < pairLimit d $extra)
      (h : At t $start (factsFrom (preLive $start) (loopHeadValue P L g d $extra))) :
      ∃ t', run kernel asms L g 2 t = some t' ∧
        At t' $stop (($pred, .pred (decide (pairLimit d $extra ≤ d.block + 2))) ::
          liveFacts P L g (advancePair d $extra) $stop) := by
    have hcount : d.block + 2 < 2147483648 := by omega
    simp only [pairLimit, Bool.false_eq_true, ↓reduceIte] at hlimit
    obtain ⟨t1, hr1, h1⟩ : ∃ t1, run kernel asms L g 1 t = some t1 ∧
        At t1 $mid (liveFacts P L g (advancePair d $extra) $mid) := by
      seg_fp h using
        all_goals idx_simp [loopHeadValue, advancePair, advancePhase, hd, countReg,
          Bool.false_eq_true, Nat.reduceEqDiff, ↓reduceIte]
        all_goals idx_bits
    obtain ⟨t2, hr2, h2⟩ : ∃ t2, run kernel asms L g 1 t1 = some t2 ∧
        At t2 $stop (($pred, .pred (decide (pairLimit d $extra ≤ d.block + 2))) ::
          liveFacts P L g (advancePair d $extra) $stop) := by
      seg_fp h1 using
        all_goals idx_simp [advancePair, advancePhase, hd, countReg, pairLimit,
          Bool.false_eq_true, ↓reduceIte]
        all_goals norm_signed
    exact ⟨t2, run_comp hr1 hr2, h2⟩)

prove_loop_head main_loop_head, false, 2426, 2427, 2428, 19
prove_loop_head extra_loop_head, true, 2512, 2513, 2514, 34

private theorem ready_lookahead_live {P : Params} {L : Launch} {g pc : Nat} {d : D}
    {extra : Bool} (hd : d.site = .ready extra) :
    liveFacts P L g d pc = liveFacts P L g { d with site := .pair extra false false } pc := by
  have he : table P L g d = table P L g { d with site := .pair extra false false } := by
    cases extra <;> simp only [table, hd, Site.hasPair, ite_true, len1Reg, countReg]
  unfold liveFacts valueOf
  rw [he]

private def loopNextSite (d : D) (extra : Bool) : Site :=
  if d.block + 2 < pairLimit d extra then .pair extra false false else .waitFree extra

private theorem afterReady_main_continue (d : D) (hnext : d.block + 1 < numOrigBlocks d.len0) :
    afterReady d = { advancePair d false with site := loopNextSite d false } := by
  simp only [afterReady, advancePair, advancePhase, loopNextSite, pairLimit, Bool.false_eq_true,
    ↓reduceIte, hnext]
  split <;> rfl

private theorem afterReady_extra_continue {P : Params} {L : Launch} {g : Nat} {d : D}
    (hi : Inv P L g d) (hd : d.site = .ready true)
    (hnext : d.block + 1 < totalBlocks d.len0 d.len1) :
    afterReady d = { advancePair d true with site := loopNextSite d true } := by
  have hb := hi.tagExtra (by rw [hd]; rfl)
  have hnot : ¬ d.block + 1 < numOrigBlocks d.len0 := by omega
  have hne : ¬ d.block + 1 = numOrigBlocks d.len0 := by omega
  simp only [afterReady, advancePair, advancePhase, loopNextSite, pairLimit, hnext, hnot, hne,
    ↓reduceIte]
  split <;> rfl

private theorem main_prefetch_address {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t : TState} (_hpre : Pre P L mem0) (_hbatch : eOf L g < P.b)
    (_hd : d.site = .ready false) (_hi : Inv P L g d) (_hmore : d.block + 2 < pairLimit d false)
    (h : At t 2429 (liveFacts P L g (advancePair d false) 2429)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2429 (liveFacts P L g (advancePair d false) 2429) :=
  ⟨t, .refl, h⟩

private theorem extra_prefetch_address {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D}
    {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (hd : d.site = .ready true) (hi : Inv P L g d) (hmore : d.block + 2 < pairLimit d true)
    (h : At t 2515 (liveFacts P L g (advancePair d true) 2515)) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2517 (liveFacts P L g (advancePair d true) 2517) := by
  have hp := hpre.paddedRange _ hbatch
  rw [← hi.len0, ← hi.len1] at hp
  have hblocks := Nat.div_mul_le_self (origPadded d.len0 + ceilToMultiple d.len1 topkBlock) 64
  change totalBlocks d.len0 d.len1 * 64 ≤ _ at hblocks
  change d.block + 2 < totalBlocks d.len0 d.len1 at hmore
  have hn := hi.tagExtra (by rw [hd]; rfl)
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hsub : d.block + 1 + 1 - numOrigBlocks d.len0 =
      (d.block + 1 - numOrigBlocks d.len0) + 1 := by omega
  have hbound : 64 + 2 * laneOf L g + 64 * (d.block + 1 - numOrigBlocks d.len0) <
      4294967296 := by omega
  obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 2 t = some t' ∧
      At t' 2517 (liveFacts P L g (advancePair d true) 2517) := by
    seg_fp h using
      all_goals idx_simp [advancePair, advancePhase, extraPairAddr, hsub]
      all_goals norm_bits [Nat.mod_eq_of_lt hbound, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]
  exact ⟨t', run_rtg hr, ht⟩

/-- The next head either loads one more pair or goes directly back to the free barrier. -/
macro "prove_ready_choice" name:ident "," extra:term "," pc:num "," src:num "," pred:num ","
    noPair:num "," poll:num "," bra:term "," addr:term "," prepare:term : command =>
  `(command| private theorem $name {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
      {d : D} {t : TState} (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
      (hd : d.site = .ready $extra) (hi : Inv P L g d)
      (hs : afterReady d = { advancePair d $extra with site := loopNextSite d $extra })
      (h : At t $pc (($pred, .pred (decide (pairLimit d $extra ≤ d.block + 2))) ::
        liveFacts P L g (advancePair d $extra) $pc)) :
      ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧ AtD P L g (afterReady d) t' := by
    let d' := afterReady d
    have hready : (advancePair d $extra).site = .ready $extra := hd
    by_cases hmore : d.block + 2 < pairLimit d $extra
    · have hs' : d' = { advancePair d $extra with site := .pair $extra false false } := by
        simpa [d', loopNextSite, hmore] using hs
      obtain ⟨t1, hr1, h1⟩ := bra_at (L := L) (g := g) (pick := false) $bra h
        (by simp [Nat.not_le.mpr hmore]) (by decide) (by decide)
      have hstart : At t1 $src (liveFacts P L g (advancePair d $extra) $src) :=
        at_of_cons h1 (by lit_mem)
      obtain ⟨t2, hr2, ht⟩ := $addr hpre hbatch hd hi hmore hstart
      rw [ready_lookahead_live hready, ← hs'] at ht
      exact ⟨t2, (run_rtg hr1).trans hr2, atD_of_liveFacts (d := d') (by rw [hs']; rfl)
        (by rw [hs']; rfl) (by rw [hs']; rfl) ht⟩
    · have hs' : d' = { advancePair d $extra with site := .waitFree $extra } := by
        simpa [d', loopNextSite, hmore] using hs
      obtain ⟨t1, hr1, h1⟩ := bra_at (L := L) (g := g) (pick := true) $bra h
        (by simp [Nat.le_of_not_lt hmore]) (by decide) (by decide)
      have hstart : At t1 $noPair (liveFacts P L g (advancePair d $extra) $noPair) :=
        at_of_cons h1 (by lit_mem)
      rw [body_live (s := .waitFree $extra) (by rw [hready]; rfl)
        rfl (by rw [hready]; rfl), ← hs'] at hstart
      have hsite : d'.site = .waitFree $extra := by rw [hs']
      obtain ⟨t2, hr2, ht⟩ := $prepare hpre hbatch hsite (afterReady_inv hd hi) hstart
      exact ⟨t2, run_rtg (run_comp hr1 hr2), atD_of_liveFacts (d := d') (pc := $poll)
        (by rw [hsite]; rfl) (by rw [hsite]; rfl) (by rw [accOf, hsite]) ht⟩)

prove_ready_choice main_ready_choice, false, 2428, 2429, 19, 2430, 2446,
  Flow.code_2428, main_prefetch_address, prepare_wait_main

prove_ready_choice extra_ready_choice, true, 2514, 2515, 34, 2518, 2534,
  Flow.code_2514, extra_prefetch_address, prepare_wait_extra

/-- A main-cache publication stays in the main loop, switches caches, or reaches the final sync. -/
theorem stepAt_readyMain {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (d : D) (hd : d.site = .ready false) :
    (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  obtain ⟨rel, sc, he, hstart⟩ := fires_ready_main hpre hd hi (atD_code.mp hat) hc hf
  obtain ⟨t1, hr1, h1⟩ := main_ready_phase hi hstart
  obtain ⟨t2, hr2, h2⟩ := main_ready_tail hpre hbatch hd hi h1
  have hstate : next P L g d e = some (some (afterReady d)) := by
    simp [next, nextSite, hd, he]
  have hi' := afterReady_inv hd hi
  have hr := run_rtg (run_comp hr1 hr2)
  by_cases hnext : d.block + 1 < numOrigBlocks d.len0
  · have hlimit : pairLimit d false < 2147483648 :=
      lt_of_le_of_lt (numOrigBlocks_le_totalBlocks d.len0 d.len1) (total_count_lt hpre hbatch hi)
    obtain ⟨t3, hr3, h3⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2494 h2
      (by simp [pairLimit, hnext]) (by decide) (by decide)
    have h3' := main_head_raw hd hnext (by omega) h3
    obtain ⟨t4, hr4, h4⟩ := main_loop_head hd hlimit hnext h3'
    obtain ⟨t5, hr5, h5⟩ := main_ready_choice hpre hbatch hd hi
      (afterReady_main_continue d hnext) h4
    exact .inl (.inr ⟨afterReady d, t5, hstate,
      hr.trans ((run_rtg (run_comp hr3 hr4)).trans hr5), atD_code.mpr h5, hi'⟩)
  · obtain ⟨t3, hr3, h3⟩ := bra_at (L := L) (g := g) (pick := false) Flow.code_2494 h2
      (by simp [pairLimit, hnext]) (by decide) (by decide)
    obtain ⟨t4, hr4, h4⟩ := main_to_extra hpre hbatch hd hi hnext (main_to_extra_raw hd h3)
    exact .inl (.inr ⟨afterReady d, t4, hstate, hr.trans ((run_rtg hr3).trans hr4),
      atD_code.mpr h4, hi'⟩)

/-- An extra-cache publication either continues the extra loop or reaches the final sync. -/
theorem stepAt_readyExtra {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) (d : D) (hd : d.site = .ready true) :
    (code P L g).StepAt d := by
  apply stepAt_of
  intro t e u ins hat hi hc hf
  obtain ⟨rel, sc, he, hstart⟩ := fires_ready_extra hpre hd hi (atD_code.mp hat) hc hf
  obtain ⟨t1, hr1, h1⟩ := extra_ready_phase hi hstart
  obtain ⟨t2, hr2, h2⟩ := extra_ready_tail hpre hbatch hd hi h1
  have hstate : next P L g d e = some (some (afterReady d)) := by
    simp [next, nextSite, hd, he]
  have hi' := afterReady_inv hd hi
  have hr := run_rtg (run_comp hr1 hr2)
  by_cases hnext : d.block + 1 < totalBlocks d.len0 d.len1
  · have hlimit : pairLimit d true < 2147483648 := total_count_lt hpre hbatch hi
    obtain ⟨t3, hr3, h3⟩ := bra_at (L := L) (g := g) (pick := true) Flow.code_2582 h2
      (by simp [pairLimit, hnext]) (by decide) (by decide)
    have h3' := extra_head_raw hd hnext (by omega) h3
    obtain ⟨t4, hr4, h4⟩ := extra_loop_head hd hlimit hnext h3'
    obtain ⟨t5, hr5, h5⟩ := extra_ready_choice hpre hbatch hd hi
      (afterReady_extra_continue hi hd hnext) h4
    exact .inl (.inr ⟨afterReady d, t5, hstate,
      hr.trans ((run_rtg (run_comp hr3 hr4)).trans hr5), atD_code.mpr h5, hi'⟩)
  · obtain ⟨t3, hr3, h3⟩ := extra_finished hd hi hnext h2
    exact .inl (.inr ⟨afterReady d, t3, hstate, hr.trans hr3, atD_code.mpr h3, hi'⟩)

/-- Every event of the index producer satisfies its role machine's abstract transition. -/
theorem steps {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) (hlt : LaunchTest P L g)
    (hbatch : eOf L g < P.b) (hq : qOf L g < P.s_q) (d : D) :
    (code P L g).StepAt d := by
  cases hd : d.site with
  | lenOrig => exact stepAt_lenOrig hpre hbatch hlt d hd
  | lenExtra => exact stepAt_lenExtra hpre hbatch d hd
  | pair extra first high =>
    cases high
    · exact stepAt_pairLow d hd
    · cases first
      · exact stepAt_prefetchedPairHigh hpre hbatch d hd
      · cases extra
        · exact stepAt_mainFirstPairHigh hpre hbatch d hd
        · exact stepAt_extraFirstPairHigh hpre hbatch d hd
  | waitFree extra =>
    cases extra
    · exact stepAt_waitFreeMain hpre hbatch hq d hd
    · exact stepAt_waitFreeExtra hpre hbatch hq d hd
  | quad1 extra =>
    cases extra
    · exact stepAt_quad1Main hpre d hd
    · exact stepAt_quad1Extra hpre d hd
  | quad2 extra =>
    cases extra
    · exact stepAt_quad2Main hpre d hd
    · exact stepAt_quad2Extra hpre d hd
  | coord extra high =>
    cases extra
    · exact stepAt_coordMain hpre d hd
    · exact stepAt_coordExtra hpre d hd
  | valid extra =>
    cases extra
    · exact stepAt_validMain hpre d hd
    · exact stepAt_validExtra hpre d hd
  | ready extra =>
    cases extra
    · exact stepAt_readyMain hpre hbatch d hd
    · exact stepAt_readyExtra hpre hbatch d hd
  | barrier => exact stepAt_of P L g d (fun _ ht => step_barrier hpre hd (atD_code.mp ht))

end Wg1Index

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
