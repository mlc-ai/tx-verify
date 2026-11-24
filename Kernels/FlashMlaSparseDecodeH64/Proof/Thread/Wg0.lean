-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Prologue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Idle
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Run
public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers
import Kernels.FlashMlaSparseDecodeH64.Audit.DeadPack
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.Code
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerNumeric
public import Lemmas.Flow.Ex2Core
public import Lemmas.Flow.FmaPairCore
public import Lemmas.Flow.Segment
public import Lemmas.Flow.Store
public import Lemmas.Flow.StoreBytes
public import Lemmas.Flow.StoreValue
public import Lemmas.Flow.Events
import Lemmas.Flow.EventCont
import Lemmas.Flow.LoadShared
public import Lemmas.Flow.Next
public import Lemmas.Flow.Word
public import Lemmas.Flow.PointerReg
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # `wg0`: the scale-and-exp / O-epilogue warpgroup of the sparse decode kernel

Warpgroup 0 (pcs 103-1841, `kernel.cuh:165-400`) runs the online softmax of the FlashMLA sparse
decode kernel and its epilogue, one block of `B_TOPK = 64` sparse slots at a time:

* the loop body waits for the block's valid mask (`bar_valid_coord_ready[vslot]`) and for the QK
  GEMM (`bar_qk_done[slot]`), loads the block's QK scores from Tensor Memory with two
  `tcgen05.ld` per thread, masks the invalid slots to `-inf` with the `is_token_valid` word,
  exchanges its peer half through `p_exchange_buf`, and reduces to the row maximum
  (`retrieve_mask_and_reduce_p`, `common_subroutine.h:74-140`);
* it computes `p = 2^(scale * S - mi)` for its 32 slots, writes the block's bf16 P tile to
  shared memory (`p_exchange_buf`), which the PV GEMM of warpgroup 1 reads as its A operand, and
  keeps the thread's half of the row sum in `%r2497`;
* when some lane of the warp moved the reference by more than 6 binary orders, and the block is
  not the first, it rescales the O accumulator in Tensor Memory in four 64-column chunks
  (`rescale_O`, `common_subroutine.h:145-172`), then fences and arrives on `bar_so_ready[slot]`;
* after the last block it computes the LSE and writes it with one `st.global.b32`
  (`kernel.cuh:289-292`), waits for `bar_sv_done[slot]`, and for each of the four 64-column
  chunks of the accumulator reads O from Tensor Memory, multiplies by
  `o_scale = 1 / (li + 2^(sinkLog2 - mi))`, converts to bf16 and stages the tile in shared
  memory. The two epilogue warps then each issue four 4-D TMA stores, covering the eight
  64-column tiles of the CTA's `(b, s_q, 64, 512)` output; the last one commits the bulk group;
* the warpgroup passes `barrier.sync 12, 384` (`everyone_sync`), and warp 0 deallocates the
  Tensor Memory (`tcgen05.dealloc`) while the other warps leave the role.

## The sites

`Site` has one constructor per event instruction of the role: the three `.nc` reads (the sink and
the two runtime lengths), the bulk wait, the three mbarrier arrivals
(`bar_last_store_done`, `bar_valid_coord_free[vslot]`, `bar_so_ready[slot]`) and the three
mbarrier waits (`bar_valid_coord_ready[vslot]`, `bar_qk_done[slot]`, `bar_sv_done[slot]`), the
nine named barrier passes (id 9 `wg0_sync`, the warp pair's `10 | (warp & 1)`, the closing
`everyone_sync` 12), the six `tcgen05` fences and the five `fence.proxy.async.shared::cta`, the
twelve `tcgen05.ld` and four `tcgen05.st` with their nine waits, the `vote.sync.any` of the
rescale heuristic, the shared reads and stores (one `Site` per instruction; `sub` counts their
elements), the global LSE store, the four `elect.sync`, the four TMA store issues, the bulk
commit and the deallocation.

`Site.pc` is the program counter of each, `Site.elems`/`Site.elemBytes` the number and size of the
memory events an instruction performs, and `Site.width` the bytes one event covers.

## The invariant

`D` is the role's state: the next site and element, the block, the reference `mi`, the head's row
sum `li` with the two threads' halves `lh` (`%r2497`) and `lp` (the peer's), the running maximum
`peak` (`%r2427`), the block's P values `pw`, the O accumulator `o` and the rescale flag. `Inv`
fixes the thread's place in the warpgroup (warp, lane, head), the two ring positions
(`slot = block % 2` with its phase, `vslot = block % 4` with its phase), the block's bound, the
epilogue's and the rescale arm's sites, the current element and the score-load arm.

`Agrees` is the value layer the result theorems consume: `mi`, `li` and `o` are the row's `Run`
fields `c`, `l` and `O`, and the block's P values are `Spec.weight` against the reference —
`p = 2^(scale * S - mi)` for a valid slot and `0` for an invalid one, which is `Run.blockWeight`
times `2 ^ (-mi)`. The output scale `oScale` is the kernel's `1 / (li + 2^(sinkLog2 - mi))`, with
the sink term zero when `attn_sink` is `-inf` (`sinkTerm`).

## What is proved and what remains

Proved here: the site vocabulary, its pc table and that every site is an unguarded event
instruction (`eventPcs_length`, `site_event`); the invariant's initial state (`init_inv`), its
preservation by a change of the next event (`inv_setSite`), by the block hand-off
(`handoff_inv`) and by the hand-off to the epilogue (`epilogue_inv`), and the arithmetic of the
loop's bookkeeping (`ring_next`); the result layer's addresses and values: the LSE store's
location and its four f32 bytes (`lseLocOf_eq`, `lseByte_empty`, `lseByte_nonempty`,
`lseValue_eq`), the output scale and the staged output values (`oScale_mul_attn`,
`stageValue_attn`, and their no-sink and empty-row forms), the staged byte of an output element
(`stageOff_eq`, `stageRel_lt`, `stageOff_lt`, `stageOff_eq_stageWrite`) and the eight 64x64 tiles
of the four TMA stores covering the CTA's whole `(64, 512)` output (`tma_tiles_cover`,
`stageOff_oLoc`); the agreement of the role's mbarrier offsets and counts and of its named
barriers with `Protocol.Mbar` (`off_eq`, `count_eq`, `bar_eq`); and **five complete site steps**:
the exit's (`event_exit`, `nextSite_exit`, `step_exit`) — the role's last event,
`tcgen05.dealloc` at pc 1840, whose two operand registers are the facts at that pc and whose
deallocation ends the role — and the four ring events `step_maskReady`, `step_qkDone`,
`step_svDone` and `step_validFree`. The entry run's first part is here too: `entry_at` reads
`Entry` as the run's table at pc 104, and the segments and steps `run_104_110`, `run_110_111`,
`run_111_113`, `run_111_114`, `run_114_115`, the eight `run_swz{k}` chunks of the SW128 swizzle
and the seven `run_add{rd}` pointer moves between them carry the thread from pc 104 to pc 146.
From there the two parameter loads, the four tests and the pad arithmetic of pcs 146-198 carry
it to the first site (`run_146_147` through `run_194_198`, `start_of_entry`): the sink and the
two length pointers decide which site is first, and the block count `%r473` is `64 * blocksOf`
(`blocksOf_mul`). The swizzle's eight 64-bit words are `stageWord`, whose clean form
(`stageWord_bits`, `stageWord_bits'`) is the plain `(address / 8) & 112` xor; `at_next_set`
frames a one-register step, and `startFacts`/`startLive` are the run's fact list: the live
registers, without the prologue's two unknown words and with the sink register at its `-inf`
initializer (`startValue`), which is the value the two skips leave in it when the launch passes
no sink.

The two value corrections the run from the prologue needs, and one more step, are here too. The
scale register `%r467` is a `ld.param.b32` of `sm_scale_div_log2`, whose Core rule moves bits, so
the table states the pattern `paramWord L 28 4` and `scaleWord` decodes it to `P.scale`; the
sink register `%r2880` (the kernel's `%r2422`) is `sinkReg`: the exact product `sink * log2e` when
the launch passes a sink, and the `-inf` word pc 101 stores when it does not. The registers the
mask ring's wait recomputes at pcs 257-263 and the shared base word of pcs 260 and 270 are
tracked (`%r974`, `%r975`, `%r981`, and the phases `%r451`/`%r452` as before), because their
values are functions of the state's block. On those, `step_maskReady` is complete: the wait's
object and parity (`event_maskReady`, `mbarLoc_b32`, `readBits_b32`), the retry arm (pcs 265-266,
two local steps back to pc 264) and the pass arm (pc 265 then pcs 267-271 to the QK wait at
pc 272). `at_wait_next` is the poll's continuation state and `facts_maskReady` evaluates the
site's `Flow.live` so the two segments can be read from the table. The QK completion's wait is
the same shape at pc 272 (`%r977`, `%r978`, `event_qkDone`, `step_qkDone`), the PV completion's
wait at pc 1184 (`%r1736`, `%r2954`, `event_svDone`, `step_svDone`), and the mask ring's free
arrival at pc 571 names `%r1000` and continues at the partner's row maximum
(`step_validFree`).

Four findings about the remaining sites. First, the run from `Entry` crosses the staging address
arithmetic of pcs 104-145 only with the assumption and a wider `Entry`. The `cvta.shared.u64` at
pc 110 turns the shared base word into a generic shared pointer (`Core`'s
`.cvta toShared (.shared win)` case, `toShared = false`), and pcs 115-145 take the shift, mask
and xor of that pointer's 64-bit bits. `Assumptions.sharedBits` covers all sixteen sites (the
eight `shr.u64` sites and the eight `xor.b64` sites, which read the *pointer* registers again),
and `readBits` has no rule for `.ptr` (`Core/Thread/Local.lean`,
`| .ptr .. | .policy => throw .noRule`) outside it; `g < L.threads`, which `readSharedAddress`
requires at pc 110, is `Entry.threads`, and `Entry` carries `%r2880`, `%r2990` and `%r2991`, the
sink initializer and the two parameter pointers, at the prologue's values. On those the run's
segments and one-instruction steps below reach pc 146. Second, the sink register holds
`s * 0f3FB8AA3B`, with the same binary32 multiplier as `Result.sinkLog2`. Third,
`nextSite`'s `.soReady` successor is
`.maskReady`, but the decoded hand-off (pcs 1125-1146) branches back to 253 and pcs 253-256 pass
`bar.sync 9, 128` — the `.wg0Sync` site — before pcs 257-263 form the mask wait's operands, so
the successor of `.soReady` is `.wg0Sync` and `.wg0Sync` leads to `.maskReady` for every block.

Remaining, and stated as the second field of `Sound` (`sound_of_entry` assembles it from the
proved `start_of_entry` and the per-site steps): the per-site steps of the other 123 sites. The
steps the
body needs, in program order, are: the three `.nc` value checks; the waits' parity arguments
and their poll loops; the mask read and the 32 `selp`s that mask the scores; the exchange
stores, the pair barrier, the partner reads and the 32 `max.ftz.f32` of the row maximum; the
32 `ex2`, the 32 `cvt.rn.bf16x2.f32` and the four 16-byte stores of the P tile; the rescale's
four load/multiply/store chunks with their factor `2^(mi - mi')`; the `vote.sync.any` that
chooses the rescale; the LSE's `lg2`/`fma` and its address arithmetic; the epilogue's four
loads, the `o_scale` division and the 32 staged chunks; and the four elections and TMA issues
(which need the coordinates and the tensor-map spec). They need the Tensor Memory dataflow of
the QK and PV GEMMs (`Core` models `tcgen05.mma` and `tcgen05.ld` as events with open results),
the mask words the index warp produces, and the O accumulator's values — the `peak`, `lh`,
`lp`, `pw` and `o` fields of `D` are exactly those premises, and `Agrees` is what the
result-layer theorems consume. The two remaining arrivals need their objects in the table
(`%r938` of pc 199 for `bar_last_store_done` and `%r1717` of pcs 1121-1122 with `%r477`/`%r478`
for `bar_so_ready`); the `.lastStore` segment of pcs 201-255 also tests `%r473 < 64`, so `%r473`
(the padded total, `64 * blocksOf`) must be tracked before that step can be taken. The
reference register needs the model's reading. Pcs 202 and 249 initialize `%r2950` with the
`-1e30` f32 *bits* (`0fF149F2CA`, `negMax`), and pc 585 replaces it with the block's maximum
(`max(%r479, %r2950)`), which is the reference the block's P values and the rescale use. The
state therefore carries which side of that update it is on (`D.miUpd`): `miVal` states `%r2950`
as the `-1e30` word before the update — the `.lastStore` segment of pcs 201-255, which contains
both initializations — and as the reference `fl d.mi` after it. The update belongs to the
`.rescaleVote` step's segment (pc 585 lies between `.rescaleVote` at 578 and `.pStore 0` at 704),
so `nextSite` sets `miUpd` there; the sites after it are exactly the `.pStore` chunks, the
rescale's chunks and the `bar_so_ready` fence and arrival. `D.mi` itself is the block's
reference throughout (the `Run`'s `c` at the epilogue); the reference the *next* block reads is
the running maximum (`D.peak`, `%r2427`), which the block hand-off carries. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

open PTX PTX.Proof PTX.Flow Finset

noncomputable section
set_option maxRecDepth 100000
-- `seg_fp` always elaborates its value tactic, even for a segment that writes no register
-- (the poll's retry); its generated tactics then legitimately have no goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- The value tactics of the entry run's segments are written once for every register a segment
-- writes; a lemma a segment's goal does not mention is legitimately unused there.
set_option linter.unusedSimpArgs false

namespace Wg0

/-- The assumptions the role is evaluated under. -/
abbrev asms : List Assumption := Assumptions.all

/-! ## The thread's place in the launch

`Proof/Thread/Prologue.lean` defines a thread's CTA and thread index (`ctaOf`, `tidOf`,
`laneOf`, `warpOf`, `wgOf`), the CTA's `%ctaid` coordinates (`ctaidX`, `ctaidY`) and the shared
address `sb` of a byte above the dynamic shared base. -/

/-- The batch whose row the thread's CTA computes (`%ctaid.y`). -/
def eOf (L : Launch) (g : Nat) : Nat := ctaidY L g

/-- The query the thread's CTA computes (`%ctaid.x`). -/
def qOf (L : Launch) (g : Nat) : Nat := ctaidX L g

/-- The head the thread's 32 slots belong to: its lane, offset by 32 for the odd warps
(`%r5 = %tid.x % 128` is below 64 exactly for warps 0 and 1). -/
def head (L : Launch) (g : Nat) : Nat := tidOf L g % 64

/-- The slot half the thread holds: warps 0 and 1 hold slots 0-31, warps 2 and 3 slots 32-63
(`local_warp_idx >= 2` selects the mask word at byte 4). -/
def half (L : Launch) (g : Nat) : Nat := warpOf L g / 2

/-- The QK-score load arm: warps 0 and 1 load their own half first, warps 2 and 3 the peer half
first (`kernel.cuh`'s `if (local_warp_idx < 2)`; the branch of pc 276). -/
def arm (L : Launch) (g : Nat) : Nat := if 2 ≤ warpOf L g then 1 else 0

theorem head_eq (L : Launch) (g : Nat) : head L g = laneOf L g + 32 * (warpOf L g % 2) := by
  unfold head laneOf warpOf
  omega

theorem head_lt (L : Launch) (g : Nat) : head L g < 64 :=
  Nat.mod_lt _ (by decide)

theorem warpLt {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hwg : wgOf L g = 0) : warpOf L g < 4 := by
  have ht : tidOf L g = g % 384 := tidOf_eq hpre g
  have h1 : warpOf L g = tidOf L g / 32 := rfl
  have h2 : wgOf L g = tidOf L g / 128 := rfl
  rw [h1, ht]
  rw [h2, ht] at hwg
  have hm : g % 384 < 384 := Nat.mod_lt _ (by decide)
  omega

theorem laneLt (L : Launch) (g : Nat) : laneOf L g < 32 :=
  Nat.mod_lt _ (by decide)

theorem halfLt {L : Launch} {g : Nat} (hw : warpOf L g < 4) : half L g < 2 := by
  have h1 : half L g = warpOf L g / 2 := rfl
  rw [h1]
  omega

theorem armLt (L : Launch) (g : Nat) : arm L g < 2 := by
  unfold arm
  split <;> decide

theorem head_tid (L : Launch) (g : Nat) : head L g = tidOf L g % 128 % 64 := by
  unfold head
  rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 128)]

/-! ## The sites -/

/-- One state per event instruction of the role. `scoreLoad a k` is the `k`-th QK-score load of
arm `a` (warps 0 and 1 take arm 0, warps 2 and 3 arm 1), `exchStore i` and `peerRead i` the
`i`-th 16-byte write of the score exchange and the `i`-th 16-byte read of the peer's, `pStore k`
the `k`-th 16-byte chunk of the block's bf16 P tile, `rescaleLoad j`/`rescaleStore j` the O
chunks of the rescale, `oLoad j`/`oWait j` the epilogue's O chunks, `oStage j k` the `k`-th
16-byte chunk of staging group `j`, and `tmaStore j` the TMA store of group `j`. -/
inductive Site where
  /-- The optional per-head sink, `ld.global.nc.f32` (156). -/
  | sink
  /-- The row's runtime main-cache length, `ld.global.nc.s32` (168). -/
  | lenOrig
  /-- The row's runtime extra-cache length, `ld.global.nc.s32` (181). -/
  | lenExtra
  /-- `cp.async.bulk.wait_group.read 0` (198). -/
  | bulkWait
  /-- The arrival on `bar_last_store_done` (200). -/
  | lastStore
  /-- `bar.sync 9, 128` before the loop (256). -/
  | wg0Sync
  /-- The wait on `bar_valid_coord_ready[vslot]` with the ring's phase (264). -/
  | maskReady
  /-- The wait on `bar_qk_done[slot]` with the ring's phase (272). -/
  | qkDone
  /-- `tcgen05.fence::after_thread_sync` (275). -/
  | fenceLoad
  /-- The `k`-th QK-score load of arm `a`, `tcgen05.ld.32x32b.x32` (278, 280, 283, 285). -/
  | scoreLoad (a : Fin 2) (k : Fin 2)
  /-- `tcgen05.wait::ld` (286). -/
  | scoreWait
  /-- `tcgen05.fence::before_thread_sync` (287). -/
  | fenceBefore
  /-- The `is_token_valid` word of the block and half, `ld.shared.b32` (289). -/
  | maskRead
  /-- The `i`-th 16-byte chunk of the peer scores, `st.shared.b128` (403, ..., 473). -/
  | exchStore (i : Fin 8)
  /-- `bar.sync 10 | (warp & 1), 64` (475). -/
  | pairBar
  /-- The `i`-th 16-byte read of the peer's scores, `ld.shared.v2.b64` (477, ..., 512). -/
  | peerRead (i : Fin 8)
  /-- The row maximum above the reference, `st.shared.b32` (566). -/
  | rowMax
  /-- `bar.sync 9, 128` (569). -/
  | wg0Sync2
  /-- The arrival on `bar_valid_coord_free[vslot]` (571). -/
  | validFree
  /-- The partner thread's row maximum, `ld.shared.b32` (572). -/
  | maxRead
  /-- The `vote.sync.any` of the rescale heuristic (578). -/
  | rescaleVote
  /-- The `k`-th 16-byte chunk of the block's bf16 P tile, `st.shared.v4.b32` (704-707). -/
  | pStore (k : Fin 4)
  /-- `tcgen05.fence::after_thread_sync` before the rescale (711). -/
  | rescaleFence
  /-- The `j`-th O chunk load of the rescale, `tcgen05.ld.32x32b.x64` (716, 817, 918, 1019). -/
  | rescaleLoad (j : Fin 4)
  /-- `tcgen05.wait::ld` (717, 818, 919, 1020). -/
  | rescaleWait (j : Fin 4)
  /-- The `j`-th O chunk store of the rescale, `tcgen05.st.32x32b.x64` (814, 915, 1016, 1117). -/
  | rescaleStore (j : Fin 4)
  /-- `tcgen05.wait::st` (815, 916, 1017, 1118). -/
  | rescaleWaitSt (j : Fin 4)
  /-- `tcgen05.fence::before_thread_sync` after the rescale (1119). -/
  | rescaleFenceB
  /-- `fence.proxy.async.shared::cta` before the arrival (1120). -/
  | soFence
  /-- The arrival on `bar_so_ready[slot]` (1122). -/
  | soReady
  /-- `bar.sync 9, 128` before the LSE (1154). -/
  | lseBar
  /-- The thread's half row sum to `rowwise_max_buf`, `st.shared.b32` (1155). -/
  | lseStore0
  /-- `bar.sync 9, 128` (1156). -/
  | lseBar2
  /-- The partner's half row sum, `ld.shared.b32` (1157). -/
  | lseRead
  /-- The LSE, `st.global.b32` (1178). -/
  | lseStore
  /-- The wait on `bar_sv_done[slot]` with the ring's phase (1184). -/
  | svDone
  /-- `tcgen05.fence::after_thread_sync` before the epilogue (1187). -/
  | fenceEpilogue
  /-- The `j`-th O chunk read of the epilogue, `tcgen05.ld.32x32b.x64` (1201, 1361, 1519, 1676). -/
  | oLoad (j : Fin 4)
  /-- `tcgen05.wait::ld` (1202, 1362, 1520, 1677). -/
  | oWait (j : Fin 4)
  /-- The `k`-th 16-byte chunk of staging group `j`, `st.shared.v4.b32` (1331-1338, ...). -/
  | oStage (j : Fin 4) (k : Fin 8)
  /-- `fence.proxy.async.shared::cta` before the TMA store of group `j` (1339, ...). -/
  | stageFence (j : Fin 4)
  /-- `bar.sync 9, 128` before the store of group `j` (1342, ...). -/
  | epiBar (j : Fin 4)
  /-- The election of the lane that issues the store of group `j` (1350, ...). -/
  | elect (j : Fin 4)
  /-- The 4-D TMA store of group `j` (1358, 1516, 1673, 1831). -/
  | tmaStore (j : Fin 4)
  /-- `cp.async.bulk.commit_group` (1832). -/
  | commit
  /-- `barrier.sync 12, 384`, the CTA's `everyone_sync` (1835). -/
  | everyone
  /-- `tcgen05.dealloc` of the allocated columns (1840). -/
  | exit
  deriving DecidableEq, Repr

/-- The program counter of a site. -/
def Site.pc : Site → Nat
  | .sink => 156
  | .lenOrig => 168
  | .lenExtra => 181
  | .bulkWait => 198
  | .lastStore => 200
  | .wg0Sync => 256
  | .maskReady => 264
  | .qkDone => 272
  | .fenceLoad => 275
  | .scoreLoad a k => ([[278, 280], [283, 285]].getD a.val []).getD k.val 0
  | .scoreWait => 286
  | .fenceBefore => 287
  | .maskRead => 289
  | .exchStore i => 403 + 10 * i.val
  | .pairBar => 475
  | .peerRead i => 477 + 5 * i.val
  | .rowMax => 566
  | .wg0Sync2 => 569
  | .validFree => 571
  | .maxRead => 572
  | .rescaleVote => 578
  | .pStore k => 704 + k.val
  | .rescaleFence => 711
  | .rescaleLoad j => 716 + 101 * j.val
  | .rescaleWait j => 717 + 101 * j.val
  | .rescaleStore j => 814 + 101 * j.val
  | .rescaleWaitSt j => 815 + 101 * j.val
  | .rescaleFenceB => 1119
  | .soFence => 1120
  | .soReady => 1122
  | .lseBar => 1154
  | .lseStore0 => 1155
  | .lseBar2 => 1156
  | .lseRead => 1157
  | .lseStore => 1178
  | .svDone => 1184
  | .fenceEpilogue => 1187
  | .oLoad j => [1201, 1361, 1519, 1676].getD j.val 0
  | .oWait j => [1202, 1362, 1520, 1677].getD j.val 0
  | .oStage j k => [1331, 1491, 1649, 1806].getD j.val 0 + k.val
  | .stageFence j => [1339, 1499, 1657, 1814].getD j.val 0
  | .epiBar j => [1342, 1502, 1659, 1817].getD j.val 0
  | .elect j => [1350, 1507, 1664, 1822].getD j.val 0
  | .tmaStore j => [1358, 1516, 1673, 1831].getD j.val 0
  | .commit => 1832
  | .everyone => 1835
  | .exit => 1840

/-- The memory events one instruction performs: a `v4.b32` store has four, a `v2.b64` read two. -/
def Site.elems : Site → Nat
  | .peerRead _ => 2
  | .pStore _ => 4
  | .oStage _ _ => 4
  | _ => 1

/-- The bytes of one memory event. -/
def Site.elemBytes : Site → Nat
  | .sink | .lenOrig | .lenExtra => 4
  | .lastStore | .maskReady | .qkDone | .validFree | .soReady | .svDone => 8
  | .maskRead | .rowMax | .maxRead | .lseStore0 | .lseRead | .lseStore => 4
  | .exchStore _ => 16
  | .peerRead _ => 8
  | .pStore _ | .oStage _ _ => 4
  | _ => 0

/-- The bytes a site's access covers in one event. -/
def Site.width : Site → Nat
  | .sink | .lenOrig | .lenExtra => 4
  | .lastStore | .maskReady | .qkDone | .validFree | .soReady | .svDone => 8
  | .maskRead | .rowMax | .maxRead | .lseStore0 | .lseRead | .lseStore => 4
  | .exchStore _ => 16
  | .peerRead _ => 8
  | .pStore _ | .oStage _ _ => 4
  | _ => 0

/-- The staging group a site belongs to. -/
def Site.stageGroup : Site → Option Nat
  | .oStage j _ | .stageFence j | .epiBar j | .elect j | .tmaStore j => some j.val
  | _ => none

/-- Whether a site belongs to the conditional rescale arm (pcs 711-1118). -/
def Site.inRescale : Site → Bool
  | .rescaleFence | .rescaleFenceB | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _
  | .rescaleWaitSt _ => true
  | _ => false

/-- Whether a site belongs to the epilogue, which runs after the last block. -/
def Site.inEpilogue : Site → Bool
  | .lseBar | .lseStore0 | .lseBar2 | .lseRead | .lseStore | .svDone | .fenceEpilogue
  | .oLoad _ | .oWait _ | .oStage _ _ | .stageFence _ | .epiBar _ | .elect _ | .tmaStore _
  | .commit | .everyone | .exit => true
  | _ => false

/-- The epilogue sites reached after computing the complete row sum. -/
@[simp] def Site.needsRowTotal : Site → Bool
  | .lseStore | .svDone | .fenceEpilogue | .oLoad _ | .oWait _ | .oStage _ _ | .stageFence _
  | .epiBar _ | .elect _ | .tmaStore _ | .commit | .everyone | .exit => true
  | _ => false

/-- At these sites the packed exchange consumes the site's loaded score words. -/
@[simp] def Site.needsExchangeReady : Site → Bool
  | .exchStore _ | .pairBar | .peerRead _ => true
  | _ => false

/-! ## The shared layout the role addresses

`SharedMemoryPlan` (`config.h:141-172`, as recorded by `Data/Barriers.lean`): `u` (204800 bytes)
holds the KV tiles and the raw blocks of the dequantizer and the `qo` member, `s_p`
(`p_exchange_buf`, 4 x 32 x 32 floats) is the f32 score exchange buffer at 204800,
`rowwise_max_buf` (128 floats) is at 221184, `is_token_valid` (4 x 8 bytes) is at 221696, and the
barrier block starts at 222768. The epilogue stages its bf16 output tiles at 65536, in `u.qo`. -/

/-- The slots of one KV block (`B_TOPK`, `config.h:48`). -/
def slotsPerBlock : Nat := 64

/-! ## The staging address the swizzle forms

The eight chunks of the thread's staging row are written at the addresses pcs 114-145 form: the
dynamic shared base, the thread's quadrant of the staging region (`16384 * half`), its row
(`128 * head`), the region's base `65536` and the chunk's 16 bytes, xored with the row's position
in its eight-row atom (`(address / 8) & 112`, the SW128 swizzle). The xor is a 64-bit
`xor.b64`, and leaves a generic shared pointer to the resulting byte, as needed by the stores. -/

/-- The thread's byte offset in the staging region before the region's base: the quadrant of its
half (`16384 * half`) and its row (`128 * head`). -/
def quadOff (L : Launch) (g : Nat) : Nat :=
  2 * (64 * head L g + 8192 * half L g)

/-- The unswizzled byte of chunk `k` of the thread's staging row. -/
def stagePtr (L : Launch) (g : Nat) (k : Nat) : Nat :=
  L.sharedBase + quadOff L g + (65536 + 16 * k)

/-- The swizzle's mask of chunk `k`: the row's position in its eight-row atom, shifted into the
16-byte chunk index. -/
def stageMask (L : Launch) (g : Nat) (k : Nat) : Nat := (stagePtr L g k / 8) &&& 112

/-- The generic shared pointer in the staging chunk register `%r2992 + k`. -/
def stageWord (L : Launch) (g : Nat) (k : Nat) : Value :=
  .ptr 64 true (.shared (g / L.block) (g / L.block))
    (BitVec.ofNat 64 (stageMask L g k ^^^ stagePtr L g k))

/-- A generic shared pointer at byte `off` of the thread's own CTA's window. -/
def shPtr (L : Launch) (g : Nat) (off : Nat) : Value :=
  .ptr 64 true (.shared (g / L.block) (g / L.block)) (BitVec.ofNat 64 off)

theorem stagePtr_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat)
    {k : Nat} (hk : k < 8) : stagePtr L g k < 2 ^ 32 := by
  have hb := sharedBase_lt hpre
  have h1 : head L g < 64 := head_lt L g
  have hw := warpOf_lt (g := g) hpre
  have h2 : half L g < 6 := by
    unfold half
    omega
  unfold stagePtr quadOff
  omega

/-- The `setp.ge.s32` of the sink-path head test (pc 152): the thread's head against `h_q`. -/
def headGe (L : Launch) (g : Nat) : Bool :=
  compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 (head L g)))
    (truncBits 32 (BitVec.ofNat 64 (Thread.paramWord L 8 4)))

/-! ## The bit identities of the swizzle and the address words

`norm_bits` (`Lemmas/Flow/Bits.lean`) normalizes the integer semantics to `Nat` arithmetic but
knows only the masks that duplicate a byte (`255`, `1`) and the signed ceiling's (`-64`). The
staging addresses' swizzle and the head words need three more: a mask of consecutive bits, the
xor of a shifted index, and the xor of a 16-shifted three-bit field. -/

/-- A mask of `m` bits shifted by `n` selects the bits `n` to `n + m - 1`. -/
theorem land_shift (x n m : Nat) :
    x &&& (2 ^ n * (2 ^ m - 1)) = 2 ^ n * (x / 2 ^ n % 2 ^ m) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  rw [show (2 ^ n * (2 ^ m - 1)) = (2 ^ m - 1) * 2 ^ n from Nat.mul_comm _ _]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  rw [show (2 ^ n * (x / 2 ^ n % 2 ^ m)) = (x / 2 ^ n % 2 ^ m) * 2 ^ n from
    Nat.mul_comm _ _]
  rw [Nat.testBit_mul_two_pow]
  by_cases hj : n ≤ j
  · rw [decide_eq_true hj]
    rw [Nat.testBit_mod_two_pow]
    rw [show x.testBit j = (x / 2 ^ n).testBit (j - n) from by
      rw [← Nat.testBit_add]; congr 1; omega]
    by_cases hm : j - n < m
    · rw [decide_eq_true hm]
      simp
    · rw [decide_eq_false hm]
      simp
  · rw [decide_eq_false hj]
    simp

/-- The mask `4032` of the head word: `(tid << 6) & 4032 = 64 * (tid % 64)`. -/
theorem land_4032 (x : Nat) : x &&& 4032 = 64 * (x / 64 % 64) := by
  have h := land_shift x 6 6
  simpa using h

/-- The mask `8192` of the warp-half word: `(tid << 7) & 8192 = 8192 * (tid / 64 % 2)`. -/
theorem land_8192 (x : Nat) : x &&& 8192 = 8192 * (x / 8192 % 2) := by
  have h := land_shift x 13 1
  simpa using h

/-- The swizzle's mask `112` of a 16-byte address: the row's position in its eight-row atom. -/
theorem land_112 (x : Nat) : x &&& 112 = 16 * (x / 16 % 8) := by
  have h := land_shift x 4 3
  simpa using h

/-- A shift by four distributes over the xor of three-bit fields. -/
theorem mul16_xor (x y : Nat) : 16 * x ^^^ 16 * y = 16 * (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  rw [show (16 * x) = x * 2 ^ 4 from by rw [Nat.mul_comm]; rfl]
  rw [show (16 * y) = y * 2 ^ 4 from by rw [Nat.mul_comm]; rfl]
  rw [show (16 * (x ^^^ y)) = (x ^^^ y) * 2 ^ 4 from by rw [Nat.mul_comm]; rfl]
  rw [Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  by_cases h : 4 ≤ j
  · rw [decide_eq_true h, Nat.testBit_xor]
    cases hx : x.testBit (j - 4) <;> cases hy : y.testBit (j - 4) <;> rfl
  · rw [decide_eq_false h]
    rfl

/-- The sum of a multiple of eight and a three-bit field, xored with a three-bit field. -/
theorem add8_xor {C k h : Nat} (hk : k < 8) (hh : h < 8) :
    (8 * C + k) ^^^ h = 8 * C + (k ^^^ h) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  have hkh : k ^^^ h < 8 := by
    have := Nat.xor_lt_two_pow (n := 3) hk hh
    simpa using this
  rw [show (8 * C + k) = 2 ^ 3 * C + k from rfl,
    show (8 * C + (k ^^^ h)) = 2 ^ 3 * C + (k ^^^ h) from rfl]
  rw [Nat.testBit_two_pow_mul_add _ hk, Nat.testBit_two_pow_mul_add _ hkh]
  by_cases hj : j < 3
  · rw [ite_eq_left hj, ite_eq_left hj, Nat.testBit_xor]
  · rw [ite_eq_right hj, ite_eq_right hj]
    have hhbit : h.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hhbit, Bool.xor_false]

/-- **The swizzle's xor**: an address `B + 16 * k` with `B` 128-byte aligned, xored with the
row's three-bit position `h` shifted to the chunk index, is `B + 16 * (k ^^^ h)`. -/
theorem swz_xor {B k h : Nat} (hB : B % 128 = 0) (hk : k < 8) (hh : h < 8) :
    B + 16 * k ^^^ (16 * h) = B + 16 * (k ^^^ h) := by
  have hB' : B = 128 * (B / 128) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hB)).symm
  have e1 : 128 * (B / 128) + 16 * k = 16 * (8 * (B / 128) + k) := by omega
  have e2 : 128 * (B / 128) + 16 * (k ^^^ h) = 16 * (8 * (B / 128) + (k ^^^ h)) := by omega
  rw [hB', e1, e2, mul16_xor, add8_xor hk hh]

/-- **The swizzle's mask is the row's position**: the staging pointer is 128-byte aligned above
the row, so the `112`-mask of its eighth is the head's position in its eight-row atom. -/
theorem stageMask_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (g : Nat)
    {k : Nat} (hk : k < 8) : stageMask L g k = 16 * (head L g % 8) := by
  have hS1024 : L.sharedBase % 1024 = 0 := by rw [hpre.sharedBase]; exact hpre.sharedAlignment
  have hS8 : L.sharedBase / 128 % 8 = 0 := by omega
  have hB : L.sharedBase % 128 = 0 := by omega
  unfold stageMask stagePtr
  rw [land_112]
  rw [show (L.sharedBase + quadOff L g + (65536 + 16 * k)) / 8 / 16 =
      (L.sharedBase + 128 * head L g + 16384 * half L g + 65536 + 16 * k) / 128 from by
    rw [Nat.div_div_eq_div_mul]
    congr 1
    unfold quadOff
    omega]
  rw [show L.sharedBase + 128 * head L g + 16384 * half L g + 65536 + 16 * k =
      128 * (L.sharedBase / 128 + head L g + 128 * half L g + 512) + 16 * k from by
    have hb : L.sharedBase = 128 * (L.sharedBase / 128) :=
      (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hB)).symm
    rw [hb]; omega]
  rw [Nat.mul_add_div (by decide : 0 < 128)]
  rw [show 16 * k / 128 = 0 from by
    apply Nat.div_eq_of_lt
    omega]
  rw [Nat.add_zero]
  congr 1
  omega

/-- The shared byte offset of `s_p`, the f32 score exchange buffer. -/
def exchangeBase : Nat := 204800

/-- The byte offset of one warp's quadrant of `s_p`: `p_exchange_buf[4][32 * 32]`. -/
def exchangeQuad : Nat := 4096

/-- The byte stride between the four-float chunks of one quadrant (`i * 32 * 4`). -/
def exchangeChunk : Nat := 512

/-- The shared byte offset of the block's bf16 P tile (the first 8192 bytes of `s_p`). -/
def pTileBase : Nat := 204800

/-- The shared byte stride between the four 16-byte chunks of one thread's P row (`local_col_idx
* B_TOPK * 2 * 8`): a chunk is eight slots and the tile has 64 rows. -/
def pChunkStride : Nat := 1024

/-- The shared byte offset of `rowwise_max_buf`. -/
def rowMaxBase : Nat := 221184

/-- The shared byte offset of `is_token_valid`. -/
def maskBase : Nat := 221696

/-- The byte stride of the mask ring: four 8-byte words, one per block slot. -/
def maskStride : Nat := 8

/-- The shared byte offset of the O staging region (`u.qo`). -/
def stageBase : Nat := 65536

/-- The bytes of one staged O tile: 64 heads x 64 columns of bf16. -/
def stageTileBytes : Nat := 8192

/-- The bytes of the whole O staging region: the eight 64 x 64 tiles of the CTA's output. -/
def stageBytes : Nat := 65536

/-- The plane of the staging region of group `j` inside a warp's two tiles: the four groups are
stored at planes `0`, `1`, `4` and `5` of the eight. -/
def planeAdd (j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 4 else 5

theorem planeAdd_lt {j : Nat} (hj : j < 4) : planeAdd j < 8 := by
  interval_cases j <;> decide

/-- The byte offset of the staging group `j` inside a warp's tiles. -/
def groupOff (j : Nat) : Nat := stageTileBytes * planeAdd j

/-- The shared byte offset of the output tile sent by epilogue warp `w` in group `j`. -/
def tmaSrc (j w : Nat) : Nat := stageBase + 16384 * w + groupOff j

/-- The first output column of that tile, from the kernel's folded Tensor Memory layout. -/
def tmaX (j w : Nat) : Nat := 64 * (planeAdd j + 2 * w)

/-- The group that stages logical tile `t`. -/
def stageGroup (t : Nat) : Nat := 2 * (t / 4) + t % 2

/-- The producing warpgroup half and the issuing TMA warp for logical tile `t`. -/
def stageHalf (t : Nat) : Nat := t / 2 % 2

theorem stageTile_inverse (t : Nat) (ht : t < 8) :
    planeAdd (stageGroup t) + 2 * stageHalf t = t := by
  interval_cases t <;> decide

/-- The offset within staging of row `h` and column `d` in its SW128 output tile. -/
def stageRel (h d : Nat) : Nat :=
  stageTileBytes * (d / 64) + 128 * h +
    16 * ((d % 64) / 8 ^^^ (h % 8)) + 2 * (d % 8)

/-- The shared byte of element `(h, d)` of the CTA's output. The producer stores element
`(h, d)` at this byte of the staging region and the TMA store of its tile copies it to
`oLoc P e q h d`. -/
def stageOff (h d : Nat) : Nat := stageBase + stageRel h d

/-- The byte a thread writes for its `k`-th 16-byte chunk of staging group `j`: the swizzled
address of pcs 114-145 with the group's offset of pcs 1331, 1491, 1649 and 1806. -/
def stageWrite (L : Launch) (g : Nat) (j k sub : Nat) : Nat :=
  stageBase + groupOff j + 16384 * half L g + 128 * (tidOf L g % 64) +
    16 * (k ^^^ (tidOf L g % 64 % 8)) + 4 * sub

/-- The staged byte is in the tile read by the TMA warp and group for its logical column. -/
theorem stageOff_eq (h d : Nat) (hd : d < 512) :
    stageOff h d =
      tmaSrc (stageGroup (d / 64)) (stageHalf (d / 64)) +
        (128 * h + 16 * ((d % 64) / 8 ^^^ (h % 8)) + 2 * (d % 8)) := by
  have hp := stageTile_inverse (d / 64) (by omega)
  unfold stageOff stageRel tmaSrc groupOff stageTileBytes
  omega

/-- A three-bit xor of two three-bit numbers is three bits: the swizzle's xor of the 16-byte
chunk index with the row's position in its eight-row atom stays inside the atom row. -/
theorem xor_lt_eight {a b : Nat} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 := by
  interval_cases a <;> interval_cases b <;> decide

/-- A staged offset stays inside the staging region: the eight tiles of 8192 bytes. -/
theorem stageRel_lt {h d : Nat} (hh : h < 64) (hd : d < 512) : stageRel h d < stageBytes := by
  have h1 : 128 * h ≤ 8064 := by omega
  have hm : d % 64 < 64 := Nat.mod_lt _ (by decide)
  have h8 : (d % 64) / 8 < 8 := by omega
  have h9 : h % 8 < 8 := Nat.mod_lt _ (by decide)
  have hx := xor_lt_eight h8 h9
  have h2 : 16 * ((d % 64) / 8 ^^^ (h % 8)) ≤ 112 := by omega
  have hd8 : d % 8 < 8 := Nat.mod_lt _ (by decide)
  have h3 : 2 * (d % 8) ≤ 14 := by omega
  have ht : d / 64 < 8 := by omega
  unfold stageRel stageTileBytes stageBytes
  omega

/-- The staged byte lies inside the staging region, above the shared base. -/
theorem stageOff_lt {h d : Nat} (hh : h < 64) (hd : d < 512) :
    stageOff h d < stageBase + stageBytes := by
  have := stageRel_lt hh hd
  unfold stageOff
  omega

/-- The role's abstract state: the next site and element, the block, the reference exponent
`mi` (`%r2492`, an arbitrary real: the kernel's `-1e30` and its `> 6` rescale heuristic only
choose it), the head's row sum `li` with the two halves `lh` (`%r2497`, this thread's 32 slots)
and `lp` (the peer thread's), the running maximum `peak` (`%r2427`), the block's P values `pw`,
the O accumulator `o` and the flag of the block's rescale arm. -/
structure D where
  /-- The next event instruction. -/
  site : Site
  /-- The element of a multi-element access the thread is about to perform. -/
  sub : Nat
  /-- The block of the loop. -/
  block : Nat
  /-- The reference exponent of the softmax (`%r2492`). -/
  mi : ℝ
  /-- The head's row sum, accumulated over the blocks (`Run.l`). -/
  li : ℝ
  /-- This thread's half of the row sum (`%r2497`). -/
  lh : ℝ
  /-- The peer thread's half of the row sum (the value the pair barrier exchanges). -/
  lp : ℝ
  /-- The running maximum over the blocks (`%r2427`). -/
  peak : WithBot ℝ
  /-- The block's P values, by head and slot. -/
  pw : Nat → Nat → ℝ
  /-- The O accumulator in Tensor Memory, by head and head dimension. -/
  o : Nat → Nat → ℝ
  /-- Whether the block's rescale arm runs (`rescale_O`, pcs 711-1118). -/
  rescale : Bool
  /-- Whether the block's reference register has been updated from the block's maximum (pc 585,
  in the `.rescaleVote` step's segment): `%r2950` is the `-1e30` word before and the reference
  after. -/
  miUpd : Bool
  /-- The half-row sum has completed at least one block update. -/
  sumUpd : Bool := false
  /-- The representation of the gain used by the rescale arm. -/
  gainWord : Value := b32 1065353216
  /-- The 64 unscaled O words read by the current rescale tile. -/
  rescaleWords : List Value := []
  /-- The QK score words returned for the half this thread normalizes. -/
  ownScores : List Value := []
  /-- The QK score words this thread passes to its peer in the other half. -/
  peerScores : List Value := []
  /-- The words returned for the current epilogue tile. -/
  oWords : List Value := []
  /-- The low-order 32 mask bits for this thread's half of the current block. -/
  maskWord : BitVec 64 := 0
  /-- The first word of a two-word read, while the second event is pending. -/
  peerPending : List Value := []
  /-- The sixteen pairs reconstructed by the peer additions. -/
  scoreSums : Nat → Value := fun _ => b32 0
  /-- The current block maximum after exchanging maxima with the peer warp. -/
  blockMax : Value := b32 4286578688
  /-- This lane's predicate supplied to the warp vote for reference updates. -/
  voteTest : Bool := false
  /-- The collective result of the current block's reference-update vote. -/
  voteTaken : Bool := false
  /-- The optional original length read replaced the static padded length. -/
  origLenRead : Bool := false

/-- The block's slot in the two-slot ring of `bar_qk_done`/`bar_sv_done` (`%r2495`). -/
def D.slotOf (d : D) : Nat := d.block % 2

/-- The phase of the two-slot ring (`%rs313`). -/
def D.parOf (d : D) : Nat := d.block / 2 % 2

/-- The block's slot in the four-slot ring of `bar_valid_coord_ready`/`-free` (`%r2494`). -/
def D.vslotOf (d : D) : Nat := d.block % 4

/-- The phase of the four-slot ring (`%rs312`). -/
def D.vparOf (d : D) : Nat := d.block / 4 % 2

/-- The `-1e30` f32 pattern the kernel initializes the reference register with at pcs 202 and
249 (`0fF149F2CA`), as the `.b32` move writes its bits. -/
def negMax : Value := b32 4048155338

/-- The reference register `%r2950`: the `-1e30` initializer before the block's maximum updates
it (pcs 202 and 249) and the state's reference `mi` after the `.rescaleVote` step's segment,
which performs pc 585 (`d.miUpd`). -/
def miVal (d : D) : Value := if d.miUpd then fl d.mi else negMax

/-- The exact finite value of the initial binary32 reference word. -/
def negMaxReal : ℝ := -1000000015047466219876688855040

/-- The exponent reference before or after the first warp vote to update it. -/
def reference (d : D) : ℝ := if d.miUpd then d.mi else negMaxReal

/-- Both the initial immediate word and an updated register read as the effective reference. -/
theorem valFloat_miVal (d : D) : valFloat .f32 (miVal d) = .ok (reference d) := by
  cases h : d.miUpd
  · have hd : f32Value 4048155338 = some (-1000000015047466219876688855040 : ℚ) := by
      decide +kernel
    have hr := valFloat_b32 (by decide : 4048155338 < 2 ^ 64) hd
    simpa [miVal, reference, h, negMax, negMaxReal] using hr
  · simp [miVal, reference, h, fl, valFloat, pure, Except.pure]

/-- The half-row sum is an immediate zero until the first update's floating-point arithmetic. -/
def halfSumVal (d : D) : Value := if d.sumUpd then fl d.lh else b32 0

theorem slotOf_lt (d : D) : d.slotOf < 2 := Nat.mod_lt _ (by decide)

theorem parOf_lt (d : D) : d.parOf < 2 := Nat.mod_lt _ (by decide)

theorem vslotOf_lt (d : D) : d.vslotOf < 4 := Nat.mod_lt _ (by decide)

/-- The shared location of a byte above the dynamic shared base. -/
def shLoc (L : Launch) (g : Nat) (off : Nat) : Loc := ⟨.shared, ctaOf L g, L.sharedBase + off⟩

/-- The location at which the role's site accesses memory at element `sub`. The three `.nc`
reads name global addresses of the parameter pointers and the TMA stores name the O tensor map;
their locations are the parameter and map bindings of `Pre`, so they have none here. -/
def siteLoc (L : Launch) (g : Nat) (s : Site) (block sub : Nat) : Option Loc :=
  match s with
  | .maskRead =>
    some (shLoc L g (maskBase + maskStride * (block % 4) + 4 * half L g))
  | .exchStore i =>
    some (shLoc L g (exchangeBase + exchangeQuad * (warpOf L g ^^^ 2) + 16 * laneOf L g +
      exchangeChunk * i.val))
  | .peerRead i =>
    some (shLoc L g (exchangeBase + exchangeQuad * warpOf L g + 16 * laneOf L g +
      exchangeChunk * i.val + 8 * sub))
  | .rowMax | .lseStore0 => some (shLoc L g (rowMaxBase + 4 * (tidOf L g % 128)))
  | .maxRead | .lseRead => some (shLoc L g (rowMaxBase + 4 * (tidOf L g % 128 ^^^ 64)))
  | .pStore k =>
    some (shLoc L g (pTileBase + pChunkStride * k.val + 4096 * half L g +
      512 * (warpOf L g % 2) + 16 * laneOf L g + 4 * sub))
  | .oStage j k => some (shLoc L g (stageWrite L g j.val k.val sub))
  | .sink | .lenOrig | .lenExtra | .bulkWait | .lastStore | .wg0Sync | .wg0Sync2
  | .maskReady | .qkDone
  | .fenceLoad | .scoreLoad _ _ | .scoreWait | .fenceBefore | .pairBar | .validFree
  | .rescaleVote | .rescaleFence | .rescaleLoad _ | .rescaleWait _ | .rescaleStore _
  | .rescaleWaitSt _ | .rescaleFenceB | .soFence | .soReady | .lseBar | .lseBar2 | .lseStore
  | .svDone | .fenceEpilogue | .oLoad _ | .oWait _ | .stageFence _ | .epiBar _ | .elect _
  | .tmaStore _ | .commit | .everyone | .exit => none

/-- The global location of the LSE word the thread writes: `Spec.lseLoc` at the thread's
`(batch, query, head)` (`%rd585` of pc 1178, built from the `stride_lse_b` and `stride_lse_sq`
parameters at pcs 1169-1176). -/
def lseLocOf (P : Params) (L : Launch) (g : Nat) : Loc := lseLoc P (eOf L g) (qOf L g) (head L g)

theorem lseLocOf_eq (P : Params) (L : Launch) (g : Nat) :
    lseLocOf P L g = ⟨.global, 0, P.lseBase + 4 * ((eOf L g * P.s_q + qOf L g) * 64 +
      head L g)⟩ := rfl

/-- The global location of an output element the epilogue stages: `Spec.oLoc`. -/
theorem oLoc_eq (P : Params) (e q h d : Nat) :
    oLoc P e q h d = ⟨.global, 0, P.outBase + 2 * (((e * P.s_q + q) * 64 + h) * 512 + d)⟩ := rfl

/-! ## The parameter words and the sink reference

The scale and the two optional pointers are read from the scalar parameter object `param_0` with
`ld.param`, whose Core rule moves bits: the register that receives a `float` field holds the
four bytes' pattern, not the number the pattern encodes. `Thread.paramWord` (from
`Proof/Thread/Wg1Idle.lean`) is the little-endian word of the object's bytes; the table below
states `%r2422`-style registers by their words and `scaleWord` decodes the scale's.

`%r2880` (the kernel's `%r2422`) is the sink reference `attn_sink * log2 e`: the prologue stores
the `-inf` pattern in it at pc 101, the sink path multiplies the loaded sink by the f32 constant
`0f3FB8AA3B` at pc 157, and the epilogue subtracts the reference at pc 1192. The multiplication
is exact (`Assumptions.idealArith`), so the register's value is `s * log2e` with `log2e` the
constant's exact value. -/

/-- The little-endian `n`-byte word at byte `off` of `param_0` (`Thread.paramWord`). -/
abbrev paramWord (L : Launch) (off n : Nat) : Nat := Thread.paramWord L off n

/-- The `sm_scale_div_log2` word is the pattern of the launch's scale. -/
theorem scaleWord {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    (f32Value (paramWord L 28 4)).map (fun q : ℚ => (q : ℝ)) = some P.scale := by
  obtain ⟨bits, hbits, hb, hdec⟩ := hpre.paramScale
  have hw : paramWord L 28 4 = bits := by
    show Thread.paramWord L 28 4 = bits
    rw [Thread.paramWord_four (L := L) (off := 28) (x := bits) fun k hk => by
      simpa using hb k hk]
    exact Nat.mod_eq_of_lt hbits
  rw [hw]
  exact hdec

/-- `0f3FB8AA3B`, the kernel's `log2 e` constant (`kernel.cuh:183`): the exact value of its
binary32 pattern. -/
abbrev log2e : ℝ := sinkLog2Factor

theorem f32Value_log2e : f32Value 1069066811 = some (1.44269502162933349609375 : ℚ) := by
  norm_num [f32Value, FloatFmt.decode_eq, FloatFmt.magnitude_eq, FloatFmt.mantBits,
    FloatFmt.expBits, FloatFmt.bias, FloatFmt.layout]

/-- The `-inf` f32 pattern the kernel initializes the reference and the running maximum with
(`%r2427` and `%r2492` start at `0fFF800000`). -/
def negInf : Value := .bits 32 (BitVec.ofNat 64 0xFF800000)

/-- The `+inf` f32 pattern the empty row's LSE store selects. -/
def posInf : Value := .bits 32 (BitVec.ofNat 64 0x7F800000)

/-- The value of the kernel's sink register at pc 168 and later: the exact product
`attn_sink * log2 e` when the launch passes a sink, and the `-inf` initializer of pc 101 when it
does not (the sink load and the multiplication are skipped, so the register keeps that word). -/
def sinkReg (P : Params) (L : Launch) (g : Nat) : Value :=
  match P.sink (head L g) with
  | some s => .float .f32 (s * log2e)
  | none => negInf

theorem sinkReg_some {P : Params} {L : Launch} {g : Nat} {s : ℝ}
    (h : P.sink (head L g) = some s) : sinkReg P L g = .float .f32 (s * log2e) := by
  simp [sinkReg, h]

theorem sinkReg_none {P : Params} {L : Launch} {g : Nat}
    (h : P.sink (head L g) = none) : sinkReg P L g = negInf := by
  simp [sinkReg, h]

/-- The LSE value of a non-empty row with the compiled binary32 multiplier. -/
def lseValue (d : D) : ℝ :=
  reference d * lseLog2Factor + (Real.log d.li / Real.log 2) * lseLog2Factor

/-- Finite normalization state after adding the two half-row sums. -/
def RowTotal (d : D) : Prop :=
  0 ≤ d.li ∧ (d.li = 0 ↔ d.peak = ⊥)

instance (d : D) : Decidable (RowTotal d) := by
  unfold RowTotal
  infer_instance

/-- The own half sum kept by the last-block empty-row selection. -/
def lseOwnSum (d : D) : ℝ := if d.peak = ⊥ ∨ ¬ d.sumUpd then 0 else d.lh

/-- The value of the running-maximum register `%r2427`: `-inf` before the first block's maximum
and a number afterwards. -/
def peakVal : WithBot ℝ → Value
  | ⊥ => negInf
  | some x => .float .f32 x

/-- Read a canonical finite or negative-infinity maximum produced by the ideal rule. -/
def decodePeak (v : Value) : Option (WithBot ℝ) :=
  if v = negInf then some ⊥
  else (valFloat .f32 v).toOption.bind fun x => if fl x = v then some (some x) else none

/-- The emitted pairwise maximum and scale that supply the lane's shared maximum. -/
def rowLocalMax (L : Launch) (d : D) : Value :=
  (peerRowMax d.scoreSums (b32 (paramWord L 28 4))).toOption.getD (b32 0)

/-- Combine the two maxima, extend the running maximum, and compute the actual vote operand. -/
def withPeerMax (L : Launch) (d : D) (peer : Value) : Option D := do
  let m ← (peerMaxE (rowLocalMax L d) peer).toOption
  let p ← (peerMaxE (peakVal d.peak) m).toOption
  let peak ← decodePeak p
  let gap ← (subE true m (miVal d)).toOption
  let voteTest ← (setpE (.ord .gt) true gap (b32 1086324736)).toOption
  pure { d with blockMax := m, peak, voteTest }

/-- Apply the collective vote exactly once to the exponent reference and its gain. -/
def afterReferenceVote (d : D) (take : Bool) : Option D :=
  if take then do
    let ref ← (peerMaxE d.blockMax (miVal d)).toOption
    let mi ← (valFloat .f32 ref).toOption
    if ref = fl mi then
      let delta ← (subE true (miVal d) ref).toOption
      let gainWord ← (ex2E true delta).toOption
      pure { d with mi, gainWord, miUpd := true }
    else none
  else some { d with gainWord := b32 1065353216 }

/-- The value of `%r23`, the reference the LSE uses: `-inf` for an empty row (`peak = ⊥`) and
the reference `mi` otherwise (the `selp` of pc 1151). -/
def lseRefVal (d : D) : Value := if d.peak = ⊥ then negInf else miVal d

/-- The value of the LSE register `%r1275`: `+inf` for an empty row and `lseValue d`
otherwise (the `fma`/`lg2` of pcs 1162-1164 and the `selp` of pc 1166). -/
def lseReg (d : D) : Value := if d.peak = ⊥ then posInf else .float .f32 (lseValue d)

/-- The kernel's sink term `2^(attn_sink * log2 e - mi)` of the output denominator: zero
without a sink, where `%r2422` stays at its `-inf` initializer and `2^-inf` is zero. -/
def sinkTerm (P : Params) (L : Launch) (g : Nat) (d : D) : ℝ :=
  match P.sink (head L g) with
  | some _ => (2 : ℝ) ^ (Result.sinkLog2 P (head L g) - reference d)
  | none => 0

/-- The output scale the epilogue divides by: `1 / (li + 2^(sinkLog2 - mi))` for a non-empty
row, and zero for an empty one (the kernel branches around the division at pc 1191 and leaves
`%r2498` at its zero initializer). -/
def oScale (P : Params) (L : Launch) (g : Nat) (d : D) : ℝ :=
  if d.li = 0 then 0 else 1 / (d.li + sinkTerm P L g d)

/-- The number of blocks of the thread's row: `total_topk_padded / B_TOPK` (`Result.blocks`). -/
def blocksOf (P : Params) (L : Launch) (g : Nat) : Nat := Result.blocks P (eOf L g)

theorem blocksOf_pos (P : Params) (L : Launch) (g : Nat) : 0 < blocksOf P L g :=
  Result.blocks_pos P (eOf L g)

/-! ## The first site and the two skips before it

The sink and the two runtime lengths are read only when their parameter pointers are non-null
(`Pre`'s `paramSink`, `paramTopkLen`, `paramExtraTopkLen`); the branch of pc 160 (the batch
bounds test) is never taken under `Pre`. -/

/-- The site after the two numbers before the loop: the extra length if its pointer is present,
else the bulk wait. -/
def afterLen (P : Params) : Site := if P.extraTopkLenBase.isSome then .lenExtra else .bulkWait

/-- The site after the sink: the main length if its pointer is present, else the above. -/
def afterSink (P : Params) : Site :=
  if P.topkLenBase.isSome then .lenOrig else afterLen P

/-- The role's first event under the parameters' pointers. -/
def firstSite (P : Params) : Site := if P.sinkBase.isSome then .sink else afterSink P

/-- All loaded scores have the four-byte representation used by integer selectors and packs. -/
def exchangeReady (d : D) : Bool :=
  d.ownScores.all (fun v => decide (Assumptions.scoreHalf v)) &&
    d.peerScores.all (fun v => decide (Assumptions.scoreHalf v))

/-! ## The invariant -/

/-- **The role's invariant**: the thread is in warpgroup 0 with a warp, lane and head, the block
is a block of the row with its positions in the two rings, the epilogue sites follow the last
block, the rescale sites belong to the rescale arm, the current element fits the instruction,
and the score-load arm is the thread's. -/
structure Inv (P : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  /-- The thread is in warpgroup 0. -/
  wg : wgOf L g = 0
  /-- The warp is one of the warpgroup's four. -/
  warpLt : warpOf L g < 4
  /-- The lane is one of the warp's 32. -/
  laneLt : laneOf L g < 32
  /-- The head is the lane offset by 32 for the odd warps. -/
  headEq : head L g = laneOf L g + 32 * (warpOf L g % 2)
  /-- The block's positions in the two rings. -/
  ring : d.slotOf = d.block % 2 ∧ d.parOf = d.block / 2 % 2 ∧ d.vslotOf = d.block % 4 ∧
    d.vparOf = d.block / 4 % 2
  /-- The block is one of the row's blocks. -/
  blockLt : d.block < blocksOf P L g
  /-- The epilogue's sites belong to the last block. -/
  epilogueLast : d.site.inEpilogue = true → d.block + 1 = blocksOf P L g
  /-- The rescale's sites belong to the rescale arm. -/
  rescaleArm : d.site.inRescale = true → d.rescale = true
  /-- The current element fits the instruction. -/
  subLt : d.sub < d.site.elems
  /-- The score-load arm is the thread's: warps 0 and 1 take arm 0, warps 2 and 3 arm 1. -/
  armSite : (∃ a k, d.site = .scoreLoad a k) →
    ∃ k, d.site = .scoreLoad ⟨arm L g, armLt L g⟩ k
  /-- Only warp 0 deallocates the Tensor Memory. -/
  exitWarp : d.site = .exit → warpOf L g = 0
  /-- The sites before the block loop see the role's initial row: no block, no running maximum,
  no half row sum, and the reference register at its `-1e30` initializer. -/
  preloop : (d.site = .bulkWait ∨ d.site = .lastStore) →
    d.block = 0 ∧ d.peak = ⊥ ∧ d.lh = 0 ∧ d.miUpd = false ∧ d.sumUpd = false
  /-- The epilogue's LSE and reciprocal consume a well-formed complete row sum. -/
  rowTotal : d.site.needsRowTotal = true → RowTotal d
  /-- The exchange selectors and packs operate on the original four-byte load representation. -/
  exchangeWords : d.site.needsExchangeReady = true → exchangeReady d = true

/-- The initial state: the first site, block 0, zero reference and row sums, no maximum, no
values, and no rescale. -/
def init (P : Params) (_L : Launch) (_g : Nat) : D where
  site := firstSite P
  sub := 0
  block := 0
  mi := negMaxReal
  li := 0
  lh := 0
  lp := 0
  peak := ⊥
  pw := fun _ _ => 0
  o := fun _ _ => 0
  rescale := false
  miUpd := false

/-! ## The register table

The registers the role tracks, valued by the state: the launch reads, the softmax's reference,
row sum and running maximum, the two ring positions and phases, the loop counters, the shared
addresses the role forms (`rowwise_max_buf`, the exchange quadrants, the P tile, the mask, the
staging region), the LSE's register and address, and the four TMA stores' coordinates, sources
and map. The registers the memory events return — the mask word, the scores, the O chunks — are
carried separately as each of their issuing sites is verified. -/

def scoreFirst (own : Bool) : Nat := if own then 2918 else 2886

def scoreDsts (own : Bool) : List Nat := List.range' (scoreFirst own) 32

theorem scoreDst_mem (own : Bool) (r : Nat) :
    r ∈ scoreDsts own ↔ scoreFirst own ≤ r ∧ r < scoreFirst own + 32 :=
  List.mem_range'_1

/-- Record the exact values returned by the load of one QK half. -/
def loadScores (d : D) (own : Bool) (words : List Value) : D :=
  if own then { d with ownScores := words } else { d with peerScores := words }

/-- The selected score's destination. -/
def maskSelectDst (j : Fin 32) : Nat := 1009 + j.val + j.val / 8

/-- The score of a valid slot, or the actual PTX negative-infinity word. -/
def ownMaskedValue (d : D) (i : Nat) : Value :=
  if d.maskWord.toNat.testBit i then d.ownScores.getD i (b32 0) else negInf

/-- The packed own scores added to the matching peer word. -/
def ownScorePair (d : D) (i : Nat) : Value :=
  joinValue (ownMaskedValue d (2 * i)) (ownMaskedValue d (2 * i + 1))

/-- Registers holding the sixteen two-lane sums of matching local and peer QK words. -/
def scoreSumRegs : List Nat :=
  [3242, 3247, 3252, 3256, 3260, 3264, 3268, 3272, 3276, 3280, 3284, 3288,
    3292, 3296, 3300, 3304]

/-- Assemble the four peer QK words in the order of the shared exchange store. -/
def exchangeValue (d : D) (i : Nat) : Value :=
  let word j := d.peerScores.getD (4 * i + j) (b32 0)
  .pair (.pair (word 0) (word 1)) (.pair (word 2) (word 3))

/-- The duplicated launch scale used in the packed softmax fma. -/
def probScale (L : Launch) : Value :=
  let s := b32 (paramWord L 28 4)
  joinValue s s

/-- The two exponents in the order of the emitted packed fma, unpack and exponentials. -/
def probPair (L : Launch) (d : D) (i : Nat) : Option (ℝ × ℝ) := do
  let bias := fl (-reference d)
  let args ← (fma2E (d.scoreSums i) (probScale L) (joinValue bias bias)).toOption
  let (lo, hi) ← (unpackE 64 args).toOption
  let vlo ← (ex2E true lo).toOption
  let vhi ← (ex2E true hi).toOption
  let p ← (valFloat .f32 vlo).toOption
  let q ← (valFloat .f32 vhi).toOption
  pure (p, q)

/-- The two lane sums join the reference-scaled half-row sum at the final fma. -/
def probabilityUpdate (L : Launch) (g : Nat) (d : D) : Option D := do
  let pairs ← (List.finRange 16).mapM fun i => probPair L d i.val
  let gain ← (valFloat .f32 d.gainWord).toOption
  let first := 32 * half L g
  pure { d with
    sumUpd := true
    lh := (if d.sumUpd then d.lh else 0) * gain +
      ((pairs.map Prod.fst).sum + (pairs.map Prod.snd).sum)
    pw := fun h slot => if h = head L g ∧ first ≤ slot ∧ slot < first + 32 then
      let i := slot - first
      let p := pairs.getD (i / 2) (0, 0)
      if i % 2 = 0 then p.1 else p.2
    else d.pw h slot }

/-- The exact two bf16 payloads stored to shared P for the selected pair of slots. -/
def pPacked (L : Launch) (g : Nat) (d : D) (i : Nat) : Value :=
  let first := 32 * half L g + 2 * i
  Assumptions.bf16Pair (d.pw (head L g) first) (d.pw (head L g) (first + 1))

/-- The compiled first-block test suppresses O rescale even if a reference update was voted. -/
def wantsRescale (d : D) : Bool := (d.block != 0) && d.voteTaken

/-- The first destination of a 64-word epilogue tile load. -/
def outputFirst (j : Fin 4) : Nat := [1745, 1916, 2086, 2255].getD j.val 0

/-- The 64 destination registers of a tile load. -/
def outputDsts (j : Fin 4) : List Nat := List.range' (outputFirst j) 64

/-- The first packed bfloat16 word of a tile prepared for staging. -/
def stageFirst (j : Fin 4) : Nat := [1810, 1981, 2151, 2320].getD j.val 0

/-- Register supplying one word of a four-word staging store. -/
def stageReg (j : Fin 4) (k sub : Nat) : Nat := stageFirst j + 3 * (4 * k + sub)

/-- A word used by the epilogue's finite f32 conversion. -/
def outputWord (v : Value) : Bool :=
  decide (Assumptions.scoreHalf v) && (valFloat .f32 v).toOption.isSome

/-- The 64 words a tile conversion can consume. -/
def goodOutputWords (words : List Value) : Bool := words.length == 64 && words.all outputWord

/-- The float represented by the given register word of an O load. -/
def outputReal (words : List Value) (i : Nat) : ℝ :=
  ((valFloat .f32 (words.getD i (b32 0))).toOption).getD 0

/-- The TMEM address register shared by a rescale tile's load and store. -/
def rescaleAddressReg (j : Fin 4) : Nat := 1263 + 129 * j.val

/-- The registers filled by the rescale tile's load. -/
def rescaleLoadRegs (j : Fin 4) : List Nat := List.range' (1199 + 129 * j.val) 64

/-- The registers read by the rescale tile's store. -/
def rescaleStoreRegs (j : Fin 4) : List Nat := List.range' (1264 + 129 * j.val) 64

/-- The rescale multiplication keeps the loaded f32 word's ideal value. -/
def rescaleValue (d : D) (i : Nat) : Value :=
  let gain := (valFloat .f32 d.gainWord).toOption.getD 0
  fl (outputReal d.rescaleWords i * gain)

/-- The output scale duplicated into the two lanes of the packed multiply. -/
def oScaleWord (P : Params) (L : Launch) (g : Nat) (d : D) : Value :=
  let v := if d.li = 0 then b32 0 else fl (oScale P L g d)
  joinValue v v

/-- The packed result of converting two consecutive scaled O words to bfloat16. -/
def stagePair (P : Params) (L : Launch) (g : Nat) (d : D) (i : Nat) : Value :=
  let scale := oScale P L g d
  .pair (.float .bf16 (scale * outputReal d.oWords (2 * i)))
    (.float .bf16 (scale * outputReal d.oWords (2 * i + 1)))

/-- Record the columns of an observed TMEM tile for this thread's head. -/
def tileOutput (L : Launch) (g : Nat) (d : D) (j : Fin 4) (words : List Value) : Nat → Nat → ℝ :=
  let col := tmaX j.val (half L g)
  fun h i => if h = head L g ∧ col ≤ i ∧ i < col + 64 then
    outputReal words (i - col)
  else d.o h i

/-- Record the returned epilogue tile and its columns for this thread's head. -/
def loadOutput (L : Launch) (g : Nat) (d : D) (j : Fin 4) (words : List Value) : D :=
  { d with oWords := words, o := tileOutput L g d j words }

/-- Read a tile register and recover its index within its loaded or staged words. -/
def outputIndex (first : Fin 4 → Nat) (size stride r : Nat) : Option Nat :=
  (List.finRange 4).findSome? fun j =>
    let base := first j
    if base ≤ r ∧ r < base + size * stride ∧ (r - base) % stride = 0 then
      some ((r - base) / stride)
    else none

/-- The registers the role tracks. -/
def tracked : List Nat :=
  [459, 460, 461, 463, 465, 466, 467, 471, 472, 474, 475, 481, 482, 553, 961, 988, 989, 990, 991,
   992, 993, 994, 995, 1001, 1733, 1913, 1914, 1915, 2082, 2083, 2084, 2251, 2252, 2253, 2421,
   2422, 2423, 2427, 2428, 2880, 2883, 2884, 2885, 2950, 2952, 2953, 2954, 2955, 2992, 2993,
   2994, 2995, 2996, 2997, 2998, 2999, 3574, 3832, 974, 975, 977, 978, 981, 451, 452, 1736, 1000,
   473, 938, 940, 972, 973, 76, 476, 477, 478, 984, 985, 986, 987, 996, 998, 999, 1717,
   2425, 2426, 3243, 997, 1109, 2951, 3312, 479, 109, 110, 1112] ++ (List.range' 1115 16 3) ++
    (List.finRange 32).map maskSelectDst ++ (List.range' 3145 8 4) ++
    (List.range' 4031 8) ++ scoreSumRegs ++
    [469, 483, 121, 123, 125, 127, 1725, 1726, 1727, 1809, 1906, 1907, 1911, 1912, 1980,
     2077, 2078, 2080, 2081, 2150, 2247, 2249, 2250, 2319, 2416, 2417, 2419, 2420, 2991, 3001] ++
    [2990, 3138, 3140, 3142, 470] ++
    scoreDsts false ++ scoreDsts true ++ [3577] ++
    (List.finRange 4).flatMap (fun j => rescaleAddressReg j :: rescaleLoadRegs j ++
      rescaleStoreRegs j) ++
    (List.finRange 4).flatMap (fun j => outputDsts j ++ List.range' (stageFirst j) 32 3)

/-- The registers of state `d` with their values. -/
def table (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  let t := tidOf L g
  let w := warpOf L g
  let l := laneOf L g
  [(459, b32 (qOf L g)), (460, b32 (eOf L g)), (461, b32 t), (463, b32 (t % 128)),
   (465, b32 w), (466, b32 l), (553, sb L 0),
   (467, b32 (paramWord L 28 4)), (2880, sinkReg P L g),
   (2885, peakVal d.peak), (2950, miVal d), (2955, halfSumVal d),
   (3577, oScaleWord P L g d),
   (2951, d.gainWord), (3312, joinValue d.gainWord d.gainWord),
   (1263, b32 0), (1392, b32 64), (1521, b32 128), (1650, b32 192),
   (481, lseRefVal d), (482, fl d.li), (483, sb L (16384 * w)),
   (1725, b32 9), (1726, b32 128),
   (1727, if d.peak = ⊥ then b32 0 else halfSumVal d),
   (2883, b32 (d.block + 1)),
   (2884, b32 ((d.block + 1 + (2 ^ 32 - blocksOf P L g)) % 2 ^ 32)),
   (2952, b32 (d.block % 4)), (2953, b32 (d.block % 2)), (2954, b32 (d.block / 2 % 2)),
   (451, .bits 16 (BitVec.ofNat 64 (d.block / 4 % 2))),
   (452, .bits 16 (BitVec.ofNat 64 (d.block / 2 % 2))),
   (961, sb L 0),
   (471, sb L (4 * (t % 128))), (472, sb L (4 * (t % 128) ^^^ 256)),
   (474, sb L (4096 * half L g + 512 * (w % 2) + 16 * l)),
   (475, sb L (4096 * w + 16 * l)),
   (1001, sb L (maskStride * (d.block % 4) + 4 * half L g)),
   (1000, sb L (222872 + 8 * (d.block % 4))),
   (974, sb L (222840 + 8 * (d.block % 4))), (975, b32 (d.block / 4 % 2)),
   (977, sb L (222904 + 8 * (d.block % 2))), (978, b32 (d.block / 2 % 2)),
   (981, sb L 0),
   (988, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l)),
   (989, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + exchangeChunk)),
   (990, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 2 * exchangeChunk)),
   (991, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 3 * exchangeChunk)),
   (992, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 4 * exchangeChunk)),
   (993, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 5 * exchangeChunk)),
   (994, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 6 * exchangeChunk)),
   (995, sb L (exchangeBase + exchangeQuad * (w ^^^ 2) + 16 * l + 7 * exchangeChunk)),
   (1733, lseReg d), (1736, sb L (222936 + 8 * (d.block % 2))),
   (3574, .bits 64 (BitVec.ofNat 64 (P.lseBase + 4 *
     ((eOf L g * P.s_q + qOf L g) * 64 + head L g)))),
   (2992, stageWord L g 0), (2993, stageWord L g 1),
   (2994, stageWord L g 2), (2995, stageWord L g 3),
   (2996, stageWord L g 4), (2997, stageWord L g 5),
   (2998, stageWord L g 6), (2999, stageWord L g 7),
   (3832, .bits 64 (BitVec.ofNat 64 (P.param1Base + 512))),
   (121, .pred (decide (2 ≤ w))), (123, .pred (decide (2 ≤ w))),
   (125, .pred (decide (2 ≤ w))), (127, .pred (decide (2 ≤ w))),
   (1809, b32 0), (1980, b32 64), (2150, b32 128), (2319, b32 192),
   (1906, b32 9), (1907, b32 128), (1911, b32 0), (1912, b32 (2 ^ 32 - 1)),
   (2077, b32 9), (2078, b32 128), (2080, b32 0), (2081, b32 (2 ^ 32 - 1)),
   (2247, b32 9), (2249, b32 0), (2250, b32 (2 ^ 32 - 1)),
   (2416, b32 9), (2417, b32 128), (2419, b32 0), (2420, b32 (2 ^ 32 - 1)),
   (1913, sb L (tmaSrc 0 w)), (1914, b32 (tmaX 0 w)), (1915, b32 0),
   (2082, sb L (tmaSrc 1 w)), (2083, b32 (tmaX 1 w)), (2084, b32 0),
   (2251, sb L (tmaSrc 2 w)), (2252, b32 (tmaX 2 w)), (2253, b32 0),
   (2421, sb L (tmaSrc 3 w)), (2422, b32 (tmaX 3 w)), (2423, b32 0),
   (2425, b32 12), (2426, b32 384), (2427, b32 0), (2428, b32 512),
   -- The registers the run from the entry forms before the loop. None of them is tracked at a
   -- site where the role is not at an instruction of that run, so they only value the entry run's
   -- segments (the two parameter pointers and the launch reads are the prologue's table).
   (2990, .ptr 64 false (.param (param "1")) 0),
   (2991, .ptr 64 false (.param (param "0")) 0),
   (926, b32 (64 * head L g)), (928, b32 (8192 * half L g)),
   (3110, b64 L.sharedBase), (3111, shPtr L g L.sharedBase),
   (3112, b64 (quadOff L g)),
   (3113, shPtr L g (L.sharedBase + quadOff L g)),
   (3114, shPtr L g (stagePtr L g 0)),
   (3117, shPtr L g (stagePtr L g 1)), (3120, shPtr L g (stagePtr L g 2)),
   (3123, shPtr L g (stagePtr L g 3)), (3126, shPtr L g (stagePtr L g 4)),
   (3129, shPtr L g (stagePtr L g 5)), (3132, shPtr L g (stagePtr L g 6)),
   (3135, shPtr L g (stagePtr L g 7)),
   (3000, b64 (paramWord L 88 8)), (69, .pred (Thread.ptrIsNull L 88)),
   (468, b32 (head L g)), (931, b32 (paramWord L 8 4)), (70, .pred (headGe L g)),
   (933, b32 (paramWord L 0 4)), (71, .pred (Thread.geBatch L g)),
   (942, b32 (paramWord L 120 4 + 63)),
   (945, b32 (paramWord L 120 4 + 63)),
   (946, b32 ((paramWord L 120 4 + 63) / 64 * 64)),
   (3139, b64 (4 * head L g)),
   (3138, b64 ((paramWord L 88 8 + 4 * head L g) % 2 ^ 64)),
   (469, b32 (2 * w)),
   (3001, .ptr 64 true (.param (param "1")) 0),
   (3002, b64 (paramWord L 80 8)), (72, .pred (Thread.ptrIsNull L 80)),
   (3141, b64 (4 * eOf L g)),
   (3140, b64 ((paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64)),
   (2881, b32 (paramWord L 40 4)),
   (470, if d.origLenRead then b32 (Result.ceilToMultiple (P.topkLen (eOf L g)) 64)
      else b32 (((paramWord L 40 4) + 63) / 64 * 64)),
   (3003, b64 (paramWord L 144 8)), (73, .pred (Thread.ptrIsNull L 144)),
   (3143, b64 (4 * eOf L g)),
   (3142, b64 ((paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64)),
   (2882, b32 (paramWord L 120 4)),
   (939, b32 (4 * (t % 128))), (940, b32 L.sharedBase),
   (941, b32 (4 * (t % 128) ^^^ 256)),
   (942, b32 (paramWord L 120 4 + 63)),
   (943, b32 0), (944, b32 0),
   (945, b32 (paramWord L 120 4 + 63)),
   (946, b32 ((paramWord L 120 4 + 63) / 64 * 64)),
   (947, b32 (Result.origPadded (paramWord L 40 4))),
   (948, b32 (paramWord L 120 4 + 63 + Result.origPadded (paramWord L 40 4))),
   (949, b32 ((paramWord L 120 4 + 63) / 64 * 64 - (paramWord L 120 4 + 63))),
   (473, b32 (64 * blocksOf P L g)),
   (938, sb L 222768),
   (972, b32 9), (973, b32 128), (998, b32 9), (999, b32 128), (76, .pred (decide (2 ≤ w))),
   (476, b32 (4 * half L g)), (477, sb L (maskStride * (d.block % 4))),
   (478, sb L (8 * (d.block % 2))), (1717, sb L (222920 + 8 * (d.block % 2))),
   (1109, rowLocalMax L d), (479, d.blockMax), (109, .pred d.voteTest),
   (110, .pred (!d.voteTaken)), (1112, b32 (2 ^ 32 - 1)),
   (997, b32 64), (984, b32 400), (985, b32 432), (986, b32 400), (987, b32 432),
   (996, b32 (10 + w % 2)),
   (3243, probScale L)]

/-- The value of a register at state `d`, with the two score ranges valued by the loads. -/
def valueOf (P : Params) (L : Launch) (g : Nat) (d : D) (r : Nat) : Value :=
  if 2918 ≤ r ∧ r < 2950 then d.ownScores.getD (r - 2918) (b32 0)
  else if 2886 ≤ r ∧ r < 2918 then d.peerScores.getD (r - 2886) (b32 0)
  else if 1009 ≤ r ∧ r ≤ 1043 then
    match (List.finRange 32).find? (fun i => maskSelectDst i == r) with
    | some i => ownMaskedValue d i.val
    | none => ((table P L g d).lookup r).getD (b32 0)
  else if 3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0 then
    ownScorePair d (2 * ((r - 3145) / 4))
  else if 4031 ≤ r ∧ r < 4039 then exchangeValue d (r - 4031)
  else if 3242 ≤ r ∧ r ≤ 3304 then
    match scoreSumRegs.idxOf? r with
    | some i => d.scoreSums i
    | none => ((table P L g d).lookup r).getD (b32 0)
  else if 1115 ≤ r ∧ r ≤ 1160 ∧ (r - 1115) % 3 = 0 then
    pPacked L g d ((r - 1115) / 3)
  else if 1199 ≤ r ∧ r ≤ 1714 then
    match outputIndex (fun j => 1199 + 129 * j.val) 64 1 r,
      outputIndex (fun j => 1264 + 129 * j.val) 64 1 r with
    | some i, _ => d.rescaleWords.getD i (b32 0)
    | none, some i => rescaleValue d i
    | none, none => ((table P L g d).lookup r).getD (b32 0)
  else if 1745 ≤ r ∧ r ≤ 2413 then
    match outputIndex outputFirst 64 1 r, outputIndex stageFirst 32 3 r with
    | some i, _ => d.oWords.getD i (b32 0)
    | none, some i => stagePair P L g d i
    | none, none => ((table P L g d).lookup r).getD (b32 0)
  else ((table P L g d).lookup r).getD (b32 0)

/-- The facts of state `d`: the live registers the role tracks, with their table values. -/
def facts (P : Params) (L : Launch) (g : Nat) (d : D) : List (Nat × Value) :=
  factsFrom ((Flow.live d.site.pc).filter fun r => tracked.contains r) (valueOf P L g d)

/-- A register's value at the role's initial state. The sink register `%r2880` is the exception:
the prologue stores the `-inf` word in it at pc 101, and the sink path replaces it with the
product `sink * log2 e` at pc 157; the entry run reaches the sink load with the initializer, and
the two skips before the loop leave it there when the launch passes no sink, where
`sinkReg` is `-inf` too. -/
def startValue (P : Params) (L : Launch) (g : Nat) (r : Nat) : Value :=
  if r = 2880 then negInf else valueOf P L g (init P L g) r

/-- The registers the entry run does not carry: the two the prologue leaves unknown
(`Prologue.skipRegs`). -/
def startFree : List Nat := [950, 1715]

/-- The registers live at `pc` that the entry run carries. -/
def startLive (pc : Nat) : List Nat := (Flow.live pc).filter fun r => !startFree.contains r

/-- The registers of a state of the entry run: the live ones, valued by the role's table. -/
def startFacts (P : Params) (L : Launch) (g : Nat) (pc : Nat) : List (Nat × Value) :=
  factsFrom (startLive pc) (startValue P L g)

theorem startValue_of_ne (P : Params) (L : Launch) (g : Nat) {r : Nat} (h : r ≠ 2880) :
    startValue P L g r = valueOf P L g (init P L g) r := by
  simp [startValue, h]

theorem startValue_2880 (P : Params) (L : Launch) (g : Nat) :
    startValue P L g 2880 = negInf := rfl

/-- Only the middle element of a peer vector load carries already returned values. -/
def siteAcc (d : D) : List Value :=
  match d.site with
  | .peerRead _ => if d.sub = 0 then [] else d.peerPending
  | _ => []

theorem siteAcc_nil (d : D) (h : d.sub = 0) : siteAcc d = [] := by
  cases hs : d.site <;> simp [siteAcc, h, hs]

/-- A concrete state of an abstract state: at the site's program counter and element, with the
site's facts. -/
def AtD (P : Params) (L : Launch) (g : Nat) (d : D) (t : TState) : Prop :=
  t.pc = d.site.pc ∧ t.sub = d.sub ∧ t.acc = siteAcc d ∧ t.fault = none ∧
    Holds t.regs (facts P L g d)

/-! ## The successor relation -/

/-- The successor of a wait: the next site on success and the same wait otherwise. -/
def waitStep (d : D) (nxt : Site) (e : Event) : Option (Option D) :=
  match e.kind with
  | .wait _ _ ok _ _ => some (some (if ok then { d with site := nxt } else d))
  | _ => none

/-- The successor of a write at the site's location: its next element, or `nxt`. -/
def writeStep (L : Launch) (g : Nat) (d : D) (nxt : Site) (e : Event) : Option (Option D) :=
  match e.kind with
  | .wr a _ =>
    if siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = d.site.elemBytes then
      if d.sub + 1 < d.site.elems then some (some { d with sub := d.sub + 1 })
      else some (some { d with site := nxt, sub := 0 })
    else some none
  | _ => none

/-- The site after the store group's barrier: the two epilogue warps elect the lane that issues
the group's TMA store, the other two go on to the next chunk (pc 1346, `@%p121 bra`). -/
def epiAfterBar (L : Launch) (g : Nat) (j : Fin 4) : Site :=
  if 2 ≤ warpOf L g then (if h : j.val + 1 < 4 then .oLoad ⟨j.val + 1, h⟩ else .commit)
  else .elect j

def afterScoreSite (a k : Fin 2) : Site :=
  if h : k.val + 1 < 2 then .scoreLoad a ⟨k.val + 1, h⟩ else .scoreWait

/-- The abstract successor after event `e`: the site decides it. The two waits of the mask and
the QK GEMM poll until they succeed; the score loads follow the thread's arm; the rescale arm is
taken from the state's flag; the block hand-off advances the block or opens the epilogue; the
TMA store of a group is issued only by an elected lane of the two epilogue warps; and the role
ends at `everyone_sync` for warps 1-3 and at the deallocation for warp 0. -/
def nextSite (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  match d.site with
  | .sink =>
    match e.kind with
    | .nc _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        match P.sink (head L g) with
        | some s =>
          if (valFloat .f32 v).toOption = some s then
            some (some { init P L g with site := afterSink P })
          else some none
        | none => some none
      | .error _ => some none
    | _ => none
  | .lenOrig =>
    match e.kind with
    | .nc _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v = b32 (P.topkLen (eOf L g)) then
          some (some { init P L g with site := afterLen P, origLenRead := true })
        else some none
      | .error _ => some none
    | _ => none
  | .lenExtra =>
    match e.kind with
    | .nc _ bs =>
      match rebuild 3 bs with
      | .ok v =>
        if v = b32 (P.extraTopkLen (eOf L g)) ∧ d.origLenRead = P.topkLenBase.isSome then
          some (some { init P L g with site := .bulkWait })
        else some none
      | .error _ => some none
    | _ => none
  | .bulkWait =>
    match e.kind with
    | .bulkWait _ _ => some (some { d with site := .lastStore })
    | _ => none
  | .lastStore =>
    match e.kind with
    | .arrive _ _ _ _ _ => some (some { d with site := .wg0Sync })
    | _ => none
  | .wg0Sync =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := .maskReady })
    | _ => none
  | .maskReady => waitStep d .qkDone e
  | .qkDone => waitStep d .fenceLoad e
  | .fenceLoad =>
    match e.kind with
    | .tc .fenceAfter =>
      some (some { d with site := .scoreLoad ⟨arm L g, armLt L g⟩ 0 })
    | _ => none
  | .scoreLoad a k =>
    match e.kind with
    | .tc (.ld _ words _) =>
      if a.val = arm L g then
        let d' := loadScores d (a.val == k.val) words
        some (some { d' with site := afterScoreSite a k })
      else some none
    | _ => none
  | .scoreWait =>
    match e.kind with
    | .tc .waitLd => some (some { d with site := .fenceBefore })
    | _ => none
  | .fenceBefore =>
    match e.kind with
    | .tc .fenceBefore => some (some { d with site := .maskRead })
    | _ => none
  | .maskRead =>
    match e.kind with
    | .rd a bytes =>
      if siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = d.site.elemBytes then
        match rebuild 3 bytes with
        | .ok (.bits 32 w) =>
          some (if exchangeReady d then some { d with site := .exchStore 0, maskWord := w }
            else none)
        | _ => some none
      else some none
    | _ => none
  | .exchStore i =>
    writeStep L g d (if h : i.val + 1 < 8 then .exchStore ⟨i.val + 1, h⟩ else .pairBar) e
  | .pairBar =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := .peerRead 0 })
    | _ => none
  | .peerRead i =>
    match e.kind with
    | .rd a bytes =>
      if siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = d.site.elemBytes then
        match rebuild 3 bytes with
        | .ok word =>
          if d.sub = 0 then some (some { d with sub := 1, peerPending := [word] })
          else
            match d.peerPending with
            | [first] =>
              let k := 2 * i.val
              match peerAddE (ownScorePair d k) first, peerAddE (ownScorePair d (k + 1)) word with
              | .ok a, .ok b =>
                let sums := Function.update (Function.update d.scoreSums k a) (k + 1) b
                let d' := { d with sub := 0, peerPending := [], scoreSums := sums }
                if h : i.val + 1 < 8 then some (some { d' with site := .peerRead ⟨i.val + 1, h⟩ })
                else if (peerRowMax sums (b32 (paramWord L 28 4))).toOption.isSome then
                  some (some { d' with site := .rowMax })
                else some none
              | _, _ => some none
            | _ => some none
        | .error _ => some none
      else some none
    | _ => none
  | .rowMax => writeStep L g d .wg0Sync2 e
  | .wg0Sync2 =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := .validFree })
    | _ => none
  | .validFree =>
    match e.kind with
    | .arrive _ _ _ _ _ => some (some { d with site := .maxRead })
    | _ => none
  | .maxRead =>
    match e.kind with
    | .rd a bytes =>
      if siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = d.site.elemBytes then
        some ((rebuild 3 bytes).toOption.bind fun peer =>
          (withPeerMax L d peer).map fun d' => { d' with site := .rescaleVote })
      else some none
    | _ => none
  | .rescaleVote =>
    match e.kind with
    | .voteMode _ _ _ r =>
      some ((afterReferenceVote d r).bind fun d' =>
        (probabilityUpdate L g { d' with voteTaken := r }).map fun v =>
          { v with site := .pStore 0, rescale := wantsRescale v })
    | _ => none
  | .pStore k =>
    if h : k.val + 1 < 4 then writeStep L g d (.pStore ⟨k.val + 1, h⟩) e
    else
      let rescale := wantsRescale d
      writeStep L g { d with rescale } (if rescale then .rescaleFence else .soFence) e
  | .rescaleFence =>
    match e.kind with
    | .tc .fenceAfter =>
      some (if outputWord d.gainWord then some { d with site := .rescaleLoad 0 } else none)
    | _ => none
  | .rescaleLoad j =>
    match e.kind with
    | .tc (.ld _ words _) => some (some { d with site := .rescaleWait j, rescaleWords := words })
    | _ => none
  | .rescaleWait j =>
    match e.kind with
    | .tc .waitLd =>
      some (if goodOutputWords d.rescaleWords && outputWord d.gainWord then
        some { d with site := .rescaleStore j }
      else none)
    | _ => none
  | .rescaleStore j =>
    match e.kind with
    | .tc (.st _ words _) =>
      some (some { d with site := .rescaleWaitSt j, o := tileOutput L g d j words })
    | _ => none
  | .rescaleWaitSt j =>
    match e.kind with
    | .tc .waitSt =>
      some (some { d with site :=
        if h : j.val + 1 < 4 then .rescaleLoad ⟨j.val + 1, h⟩ else .rescaleFenceB })
    | _ => none
  | .rescaleFenceB =>
    match e.kind with
    | .tc .fenceBefore => some (some { d with site := .soFence })
    | _ => none
  | .soFence =>
    match e.kind with
    | .fenceProxy _ _ => some (some { d with site := .soReady })
    | _ => none
  | .soReady =>
    match e.kind with
    | .arrive _ _ _ _ _ =>
      some (some (if d.block + 1 < blocksOf P L g then
        { d with block := d.block + 1, site := .wg0Sync, sub := 0 }
      else { d with site := .lseBar }))
    | _ => none
  | .lseBar =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := .lseStore0 })
    | _ => none
  | .lseStore0 => writeStep L g d .lseBar2 e
  | .lseBar2 =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := .lseRead })
    | _ => none
  | .lseRead =>
    match e.kind with
    | .rd a bytes =>
      if siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = d.site.elemBytes then
        match (rebuild 3 bytes).toOption.bind (fun v => (valFloat .f32 v).toOption) with
        | some peer =>
          let d' := { d with
            site := if tidOf L g % 128 < 64 then .lseStore else .svDone
            sub := 0, li := lseOwnSum d + peer, lp := peer }
          if RowTotal d' then some (some d') else some none
        | none => some none
      else some none
    | _ => none
  | .lseStore =>
    match e.kind with
    | .wr a _ =>
      if a.loc = lseLocOf P L g ∧ a.size = 4 then
        some (some { d with site := .svDone, sub := 0 })
      else some none
    | _ => none
  | .svDone => waitStep d .fenceEpilogue e
  | .fenceEpilogue =>
    match e.kind with
    | .tc .fenceAfter => some (some { d with site := .oLoad 0 })
    | _ => none
  | .oLoad j =>
    match e.kind with
    | .tc (.ld _ words _) => some (some { loadOutput L g d j words with site := .oWait j })
    | _ => none
  | .oWait j =>
    match e.kind with
    | .tc .waitLd =>
      some (if goodOutputWords d.oWords then some { d with site := .oStage j 0 } else none)
    | _ => none
  | .oStage j k =>
    writeStep L g d (if h : k.val + 1 < 8 then .oStage j ⟨k.val + 1, h⟩ else .stageFence j) e
  | .stageFence j =>
    match e.kind with
    | .fenceProxy _ _ => some (some { d with site := .epiBar j })
    | _ => none
  | .epiBar j =>
    match e.kind with
    | .bar _ _ _ => some (some { d with site := epiAfterBar L g j })
    | _ => none
  | .elect j =>
    match e.kind with
    | .elect _ _ leader =>
      if leader ≠ laneOf L g then
        some (some { d with site :=
          if h : j.val + 1 < 4 then .oLoad ⟨j.val + 1, h⟩ else .commit })
      else some (some { d with site := .tmaStore j })
    | _ => none
  | .tmaStore j =>
    match e.kind with
    | .tensorStore _ _ =>
      some (some { d with site := if h : j.val + 1 < 4 then .oLoad ⟨j.val + 1, h⟩ else .commit })
    | _ => none
  | .commit =>
    match e.kind with
    | .bulkCommit => some (some { d with site := .everyone })
    | _ => none
  | .everyone =>
    match e.kind with
    | .bar _ _ _ =>
      some (if warpOf L g = 0 then some { d with site := .exit } else none)
    | _ => none
  | .exit =>
    match e.kind with
    | .tc (.resource _ _ _) => some none
    | _ => none

/-- The abstract successor after event `e`: the state's site decides it. -/
def next (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  nextSite P L g d e

/-- **The role's code machine.** -/
def code (P : Params) (L : Launch) (g : Nat) : Code kernel asms L g where
  D := D
  init := init P L g
  pc := fun d => d.site.pc
  sub := fun d => d.sub
  acc := siteAcc
  facts := facts P L g
  inv := Inv P L g
  next := next P L g

/-! ## The role's mbarrier objects

The role's three waits and three arrivals are the protocol layer's objects (`Data/Barriers.mbars`,
`Proof/Protocol/Mbar.lean`): `bar_last_store_done` (222768, 128 arrivals), the four-slot ring of
`bar_valid_coord_ready`/`-free` (222840/222872, counts 32 and 129), the two-slot ring of
`bar_qk_done` (222904, 1), `bar_so_ready` (222920, 128) and `bar_sv_done` (222936, 1). -/

/-- The shared byte offset of `bar_last_store_done`. -/
def lastStoreOff : Nat := 222768

/-- The shared byte offset of `bar_valid_coord_ready[vslot]`. -/
def validReadyOff (vslot : Nat) : Nat := 222840 + 8 * vslot

/-- The shared byte offset of `bar_valid_coord_free[vslot]`. -/
def validFreeOff (vslot : Nat) : Nat := 222872 + 8 * vslot

/-- The shared byte offset of `bar_qk_done[slot]`. -/
def qkDoneOff (buf : Nat) : Nat := 222904 + 8 * buf

/-- The shared byte offset of `bar_so_ready[slot]`. -/
def soReadyOff (buf : Nat) : Nat := 222920 + 8 * buf

/-- The shared byte offset of `bar_sv_done[slot]`. -/
def svDoneOff (buf : Nat) : Nat := 222936 + 8 * buf

/-! ## The sites are events -/

/-- The pcs of the role's event instructions, in program order. -/
def eventPcs : List Nat :=
  [156, 168, 181, 198, 200, 256, 264, 272, 275, 278, 280, 283, 285, 286, 287, 289, 403, 413, 423,
   433, 443, 453, 463, 473, 475, 477, 482, 487, 492, 497, 502, 507, 512, 566, 569, 571, 572, 578,
   704, 705, 706, 707, 711, 716, 817, 918, 1019, 717, 818, 919, 1020, 814, 915, 1016, 1117, 815,
   916, 1017, 1118, 1119, 1120, 1122, 1154, 1155, 1156, 1157, 1178, 1184, 1187, 1201, 1361, 1519,
   1676, 1202, 1362, 1520, 1677, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1491, 1492, 1493,
   1494, 1495, 1496, 1497, 1498, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1806, 1807, 1808,
   1809, 1810, 1811, 1812, 1813, 1339, 1499, 1657, 1814, 1342, 1502, 1659, 1817, 1350, 1507, 1664,
   1822, 1358, 1516, 1673, 1831, 1832, 1835, 1840]

/-- Every pc of `eventPcs` holds an unguarded event instruction. -/
theorem eventPcs_ok :
    eventPcs.all (fun pc => match codeAt pc with
      | some i => !i.op.isLocal && i.guard.isNone
      | none => false) = true := by
  decide +kernel

/-- A site's pc is one of the role's event pcs. -/
theorem mem_eventPcs (s : Site) : s.pc ∈ eventPcs := by
  cases s <;>
    first
      | decide
      | (rename_i a; fin_cases a <;> decide)
      | (rename_i a b; fin_cases a <;> fin_cases b <;> decide)

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
    exact ⟨ins, h, hok.1, by rw [hok.2]; trivial⟩

/-! ## The ring arithmetic of the loop's bookkeeping

The body's last instructions before the back edge (pcs 1125-1142) advance the two ring
positions: `%r2495 = ~%r2495 & 1` flips the two-slot ring's slot, `%rs313` toggles when the
block leaves its slot, `%r2494 = (b + 1) mod 4` steps the four-slot ring of the valid masks and
`%rs312` toggles after the slot `3`. The four theorems below are that arithmetic. -/

/-! ## The invariant's preservation -/

/-- The initial site is not in the epilogue. -/
theorem firstSite_notEpilogue (P : Params) : (firstSite P).inEpilogue = false := by
  unfold firstSite afterSink afterLen
  repeat' split_ifs <;> rfl

/-- The initial site does not belong to the rescale arm. -/
theorem firstSite_notRescale (P : Params) : (firstSite P).inRescale = false := by
  unfold firstSite afterSink afterLen
  repeat' split_ifs <;> rfl

/-- The initial site is not the exit. -/
theorem firstSite_ne_exit (P : Params) : firstSite P ≠ .exit := by
  unfold firstSite afterSink afterLen
  repeat' split_ifs <;> simp

/-- The initial site is not a QK-score load. -/
theorem firstSite_notScore (P : Params) : ¬ ∃ a k, firstSite P = .scoreLoad a k := by
  rintro ⟨a, k, hk⟩
  unfold firstSite afterSink afterLen at hk
  repeat' split_ifs at hk

/-- Every site performs at least one event. -/
theorem elems_pos (s : Site) : 0 < s.elems := by
  unfold Site.elems
  split <;> decide

/-- **The initial state satisfies the invariant**, for a thread of warpgroup 0. -/
theorem init_inv {P : Params} {L : Launch} {mem0 : Mem0} (g : Nat) (hpre : Pre P L mem0)
    (hwg : wgOf L g = 0) : Inv P L g (init P L g) := by
  refine ⟨hwg, warpLt hpre hwg, laneLt L g, head_eq L g, ⟨rfl, rfl, rfl, rfl⟩,
    blocksOf_pos P L g, ?_, ?_, elems_pos _, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [show (init P L g).site = firstSite P from rfl] at h
    rw [firstSite_notEpilogue] at h
    simp at h
  · intro h
    rw [show (init P L g).site = firstSite P from rfl] at h
    rw [firstSite_notRescale] at h
    simp at h
  · intro h
    exact absurd h (firstSite_notScore P)
  · intro h
    exact absurd h (firstSite_ne_exit P)
  · intro _
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    have he := firstSite_notEpilogue P
    cases hsite : firstSite P <;> simp_all [init, Site.needsRowTotal, Site.inEpilogue]
  · intro h
    change (firstSite P).needsExchangeReady = true at h
    unfold firstSite afterSink afterLen at h
    split_ifs at h <;> cases h

/-- The invariant does not depend on the state's next event beyond the site's kind: every body
step of the machine changes the site, the element and the block and nothing else, so its
successor keeps the position and value facts. -/
theorem inv_setSite {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d) (s : Site)
    (hs : s.inEpilogue = true → d.block + 1 = blocksOf P L g)
    (hr : s.inRescale = true → d.rescale = true)
    (ha : (∃ a k, s = .scoreLoad a k) → ∃ k, s = .scoreLoad ⟨arm L g, armLt L g⟩ k)
    (he : s = .exit → warpOf L g = 0)
    (hp : (s = .bulkWait ∨ s = .lastStore) → d.block = 0 ∧ d.peak = ⊥ ∧ d.lh = 0 ∧
      d.miUpd = false ∧ d.sumUpd = false)
    (hn : s.needsRowTotal = true → RowTotal d := by
      intro hsite
      simp [Site.needsRowTotal] at hsite)
    (hx : s.needsExchangeReady = true → exchangeReady d = true := by
      intro hsite
      simp [Site.needsExchangeReady] at hsite) :
    Inv P L g { d with site := s, sub := 0 } :=
  ⟨h.wg, h.warpLt, h.laneLt, h.headEq, h.ring, h.blockLt, hs, hr, elems_pos s, ha, he, hp, hn, hx⟩

/-- **The block hand-off preserves the invariant**: the next block is one of the row's, and the
epilogue's sites still follow the last block. -/
theorem handoff_inv {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d)
    (hb : d.block + 1 < blocksOf P L g) :
    Inv P L g { d with block := d.block + 1, site := .maskReady, sub := 0 } := by
  refine
    { wg := h.wg, warpLt := h.warpLt, laneLt := h.laneLt, headEq := h.headEq, ring := ?_,
      blockLt := hb, epilogueLast := ?_, rescaleArm := ?_, subLt := ?_, armSite := ?_,
      exitWarp := ?_, preloop := ?_, rowTotal := ?_, exchangeWords := ?_ }
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro hs
    exact absurd hs (by simp [Site.inEpilogue])
  · intro hs
    exact absurd hs (by simp [Site.inRescale])
  · show 0 < (Site.elems Site.maskReady)
    exact elems_pos _
  · intro hs
    exact absurd hs (by simp)
  · intro hs
    simp at hs
  · rintro (hs | hs) <;> exact absurd hs (by simp)
  · simp [Site.needsRowTotal]
  · simp [Site.needsExchangeReady]

/-- The hand-off to the epilogue preserves the invariant: the epilogue's sites follow the last
block of the row. -/
theorem epilogue_inv {P : Params} {L : Launch} {g : Nat} {d : D} (h : Inv P L g d)
    (hb : ¬ d.block + 1 < blocksOf P L g) :
    Inv P L g { d with site := .lseBar, sub := 0 } := by
  refine
    { wg := h.wg, warpLt := h.warpLt, laneLt := h.laneLt, headEq := h.headEq, ring := h.ring,
      blockLt := h.blockLt, epilogueLast := ?_, rescaleArm := ?_, subLt := ?_, armSite := ?_,
      exitWarp := ?_, preloop := ?_, rowTotal := ?_, exchangeWords := ?_ }
  · intro _
    have h1 := h.blockLt
    have h2 := hb
    show d.block + 1 = blocksOf P L g
    unfold blocksOf at h1 h2 ⊢
    omega
  · intro hs
    exact absurd hs (by simp [Site.inRescale])
  · show 0 < (Site.elems Site.lseBar)
    exact elems_pos _
  · intro hs
    exact absurd hs (by simp)
  · intro hs
    simp at hs
  · rintro (hs | hs) <;> exact absurd hs (by simp)
  · simp [Site.needsRowTotal]
  · simp [Site.needsExchangeReady]

/-! ## The dataflow agreement with the `Run`

`Proof/Result/Run.lean` describes the row's online softmax as a `Run`: the reference exponents
`c`, the row sums `l` and the O accumulators `O`. The role's state agrees with it: `mi` is `c`,
`li` is `l` and `o` is `O`, at the epilogue's last block. -/

/-- The role's dataflow agreement with the row's `Run`. -/
structure Agrees (P : Params) (L : Launch) (g : Nat)
    (run : Result.Run P (eOf L g) (qOf L g) (head L g)) (d : D) : Prop where
  /-- The epilogue's block is the row's last. -/
  last : d.block + 1 = blocksOf P L g
  /-- The reference is the `Run`'s. -/
  c : reference d = run.c d.block
  /-- The row sum is the `Run`'s. -/
  l : d.li = run.l d.block
  /-- The O accumulator is the `Run`'s. -/
  O : ∀ dd, d.o (head L g) dd = run.O d.block dd
  /-- The block's P values are `Spec.weight` against the reference: `2^(scale * S - mi)` for a
  valid slot and zero for an invalid one (`Run.blockWeight` is that weight). -/
  pw : ∀ j < slotsPerBlock, d.pw (head L g) j =
    Result.blockWeight P (eOf L g) (qOf L g) (head L g) d.block j * (2 : ℝ) ^ (-reference d)

theorem Agrees.block_eq {P : Params} {L : Launch} {g : Nat}
    {run : Result.Run P (eOf L g) (qOf L g) (head L g)} {d : D} (h : Agrees P L g run d) :
    d.block = Result.blocks P (eOf L g) - 1 := by
  have hp := Result.blocks_pos P (eOf L g)
  have hl := h.last
  unfold blocksOf at hl
  omega

/-! ## The result layer: LSE and O

The role's last value facts, from the pcs named in each theorem: the LSE's four f32 bytes, the
output scale and the staged bf16 output values. -/

/-- The row sum the `Run` holds at the epilogue's block is a real multiple of `rowSum`, so it is
nonzero when the row is non-empty. -/
theorem run_l_ne_zero {P : Params} {L : Launch} {g : Nat}
    {run : Result.Run P (eOf L g) (qOf L g) (head L g)}
    (htopk : P.topkLen (eOf L g) ≤ P.topk) (hextra : P.extraTopkLen (eOf L g) ≤ P.extra_topk)
    (hpos : 0 < rowSum P (eOf L g) (qOf L g) (head L g)) :
    run.l (Result.blocks P (eOf L g) - 1) ≠ 0 := by
  have hτ := Result.lastBlock_lt P (eOf L g)
  have hsum := Result.Run.sum run hτ
  rw [Result.lastBlock_succ, Result.sum_blockWeight_eq_rowSum P _ _ _ htopk hextra] at hsum
  rw [hsum]
  exact mul_ne_zero (PTX.Numeric.two_rpow_pos _).ne' (ne_of_gt hpos)

/-- The producer of this head and tile writes its element at the swizzled staging byte. -/
theorem stageOff_eq_stageWrite {L : Launch} {g : Nat} {h dd : Nat} (hd : dd < 512)
    (hhalf : half L g = stageHalf (dd / 64)) (hh : head L g = h) :
    stageOff h dd =
      stageWrite L g (stageGroup (dd / 64)) ((dd % 64) / 8) ((dd % 8) / 2) +
        2 * ((dd % 8) % 2) := by
  rw [stageOff_eq h dd hd]
  unfold stageWrite tmaSrc
  unfold head at hh
  rw [hh, hhalf]
  omega

/-! ## The entry interface and the role's soundness -/

/-- The prologue's hand-off to the role: a thread state at pc 104, after the prologue's
`setmaxnreg.inc 224` at pc 103, with the prologue's registers.

`Proof/Thread/Prologue.lean` stops at warpgroup 0's first event (pc 103) and its table
(`Prologue.values`) gives these values there; none of these registers is written again in the
program, so they hold at 104 too. `%r2 = %ctaid.y`, `%r3 = %tid.x`, `%r5 = %tid % 128`,
`%r7` (the warp index) and `%rd2` (the `param_0` pointer) are the registers the role's first
instructions read; `%r2880` is the sink register's `-inf` initializer (pc 101) and `%rd1` the
`param_1` pointer the TMA coordinates and the descriptor prefetches use.

The thread bound `g < L.threads` is the launch's: `readSharedAddress` requires it for the
`cvta.shared.u64` of pc 110, and the prologue's hand-off (`MachineSound.wg0Entry_of_handoff`)
has it in scope. -/
structure Entry (P : Params) (L : Launch) (g : Nat) (t : TState) : Prop where
  /-- The thread is at pc 104, after the prologue's `setmaxnreg.inc 224`. -/
  pc : t.pc = 104
  /-- The state is at an instruction boundary. -/
  sub : t.sub = 0
  acc : t.acc = []
  fault : t.fault = none
  /-- The prologue's launch reads, the sink register's initializer
  and the two parameter pointers, at the prologue's own values (`Prologue.values`). -/
  regs : Holds t.regs (factsFrom [459, 460, 461, 463, 465, 466, 2880, 2990, 2991]
    (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g))
  /-- The thread's warpgroup: the prologue's dispatch falls through to the role. -/
  wg : wgOf L g = 0
  /-- The thread is one of the launch's. -/
  threads : g < L.threads
  /-- The CTA is a batch index of the grid. -/
  batch : ctaidY L g < P.b
  /-- The CTA is a query index of the grid. -/
  query : ctaidX L g < P.s_q

/-- The entry state is a concrete state at pc 104 with the prologue's facts. -/
theorem Entry.at {P : Params} {L : Launch} {g : Nat} {t : TState} (h : Entry P L g t) :
    At t 104 (factsFrom [459, 460, 461, 463, 465, 466, 2880, 2990, 2991]
      (_root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g)) :=
  ⟨h.pc, h.sub, h.acc, h.fault, h.regs⟩

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

/-! ## The exit's step

The role's last event is `tcgen05.dealloc.cta_group::1.sync.aligned.b32` at pc 1840, executed by
warp 0 (`@%p129 bra` at 1837 sends the other warps to the program's `ret`). Its step is complete:
the two operand registers are the state's facts, the deallocation is the event of Core's
`tcgen05` rule, and the machine stops there — the thread's next instruction is the branch to the
`done` role. -/

theorem facts_exit {d : D} (hpc : d.site.pc = 1840) :
    2427 ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r) ∧
      2428 ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r) := by
  rw [hpc]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- **The exit's event**: `tcgen05.dealloc` of the 512 columns the prologue allocated, against
the two operand registers the state's table gives. -/
theorem event_exit {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState} {mem0 : Mem0}
    (hpre : Pre P L mem0) (hat : (code P L g).AtD d t) (hd : d.site = .exit) :
    eventTmpl asms L g t (.tcDealloc .one (.reg 2427) (.reg 2428)) =
      .tc (.resource .one none (.dealloc 0 512)) (PTX.next t) := by
  obtain ⟨h1, h2⟩ := facts_exit (d := d) (by rw [hd]; rfl)
  have hm := hat.2.2.2.2
  have h0 : t.regs 2427 = some (b32 0) := by
    have h := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 2427) h1)
    simpa [facts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h
  have h512 : t.regs 2428 = some (b32 512) := by
    have h := holds_mem hm (mem_factsFrom (val := valueOf P L g d) (r := 2428) h2)
    simpa [facts, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h
  have hr0 : readBits L g t 32 (.reg 2427) = .ok (BitVec.ofNat 64 0) :=
    readBits_b32 h0 (by decide)
  have hr512 : readBits L g t 32 (.reg 2428) = .ok (BitVec.ofNat 64 512) :=
    readBits_b32 h512 (by decide)
  have hblock : L.block % 32 = 0 := by rw [hpre.block]
  simp only [eventTmpl, tcTmpl, hblock, hr0, hr512]
  rfl

/-- The machine stops at the deallocation: the exit site's successor is the role's end. -/
theorem nextSite_exit (P : Params) (L : Launch) (g : Nat) (d : D) (grp : CtaGroup)
    (dst : Option Loc) (req : Tmem.Request) (h : d.site = .exit) :
    nextSite P L g d ⟨d.site.pc, .tc (.resource grp dst req)⟩ = some none := by
  unfold nextSite
  rw [h]

/-- **The exit's step**: the deallocation event ends the role. -/
theorem step_exit {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .exit) : (code P L g).StepAt d :=
  stepAt_of P L g d fun ins hat hinv hc hf => by
    have hpc : d.site.pc = 1840 := by rw [hd]; rfl
    rw [hpc] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
    rw [event_exit hpre hat hd] at hf
    obtain ⟨he, -⟩ := hf
    refine Or.inl (Or.inl ?_)
    rw [he]
    exact nextSite_exit P L g d _ _ _ hd

/-! ## The mask-ready wait

pc 264 polls `bar_valid_coord_ready[vslot]` of the four-slot ring with the ring's phase. Both
operands are recomputed from the ring registers at pcs 257-263: the address is
`sb + 222840 + 8 * vslot` and the parity is the phase `%r451`, so the table carries them as
functions of the state's block. The poll's two arms are the retry (pcs 265-266, the failed
predicate falling through to `bra 264`) and the pass (pc 265 then pcs 267-271, which form the
QK completion's address and parity). -/

theorem sharedBase_mod8 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    L.sharedBase % 8 = 0 := by
  have h := hpre.sharedAlignment
  rw [hpre.sharedBase]
  omega

theorem maskAddr_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {vslot : Nat} (hv : vslot < 4) :
    L.sharedBase + (222840 + 8 * vslot) < 2 ^ 32 := by
  have h := sharedBase_lt hpre
  omega

theorem maskAddr_mod8 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (vslot : Nat) : (L.sharedBase + (222840 + 8 * vslot)) % 8 = 0 := by
  have h := sharedBase_mod8 hpre
  omega

section
variable {P : Params} {L : Launch} {g : Nat}

/-- **A tracked register's value at a state's site**: the fact the table gives a register that is
live there. -/
theorem reg_value {d : D} {t : TState} (hat : (code P L g).AtD d t) {r : Nat}
    (hr : r ∈ (Flow.live d.site.pc).filter (fun r => tracked.contains r)) :
    t.regs r = some (valueOf P L g d r) := by
  have h := holds_mem hat.2.2.2.2 (mem_factsFrom (val := valueOf P L g d) hr)
  simpa [facts, code] using h

/-- `%r974`, the address of the mask ring's ready word, at the mask-ready site. -/
theorem reg974 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .maskReady) :
    t.regs 974 = some (b32 (L.sharedBase + (222840 + 8 * (d.block % 4)))) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 974) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, sb, PTX.Flow.lookupLit, Option.getD_some] using h

/-- `%r975`, the mask ring's parity. -/
theorem reg975 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .maskReady) :
    t.regs 975 = some (b32 (d.block / 4 % 2)) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 975) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h

/-- **The mask-ready poll's template**: the wait on `bar_valid_coord_ready[vslot]` at the
four-slot ring's parity. -/
theorem event_maskReady {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} {t : TState}
    (hat : (code P L g).AtD d t) (hd : d.site = .maskReady) :
    ∃ sc', eventTmpl asms L g t (.mbarWait 4075 974 0 (.reg 975) true .cta) =
      .wait ⟨.shared, g / L.block, L.sharedBase + (222840 + 8 * (d.block % 4))⟩
        ((BitVec.ofNat 64 (d.block / 4 % 2)).toNat % 2)
        (fun ok => PTX.next (setReg t 4075 (.pred ok))) true sc' := by
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 974)
    (a := L.sharedBase + (222840 + 8 * (d.block % 4))) (reg974 hat hd)
    (maskAddr_lt hpre (vslotOf_lt d)) (maskAddr_mod8 hpre (d.block % 4))
  have hq := readBits_b32 (L := L) (g := g) (t := t) (r := 975) (a := d.block / 4 % 2)
    (reg975 hat hd) (by omega)
  obtain ⟨sc', h⟩ := eventTmpl_mbarWait_next (A := asms) hm hq
  exact ⟨sc', h⟩

/-- The mask-ready site's facts, with the site's program counter evaluated: a symbolic site's
`Flow.live` is not reducible, so the local segments of the poll state it concretely. -/
theorem facts_maskReady {d : D} (hd : d.site = .maskReady) :
    facts P L g d = factsFrom ((Flow.live 264).filter (fun r => tracked.contains r))
      (valueOf P L g d) := by
  simp only [facts, hd]
  rfl

/-- A small natural in a byte mask: the `and` of the parity word with `255` (pcs 257-258, 267-268
compute `cvt.u32.u16` of the phase and mask it to a byte). -/
theorem land255 (a : Nat) : a &&& 255 = a % 256 := Nat.and_two_pow_sub_one_eq_mod a 8

/-- The state after the poll: the thread is at the branch of pc 265 and `%r4075` holds the
outcome. -/
theorem at_wait_next {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .maskReady)
    (hs : d.sub = 0) (ok : Bool) :
    At (PTX.next (setReg t 4075 (.pred ok))) 265
      ((4075, .pred ok) :: factsFrom ((Flow.live 264).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := hat
  have hpc : t.pc = d.site.pc := hpc
  have hsub : t.sub = d.sub := hsub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t.pc + 1 = 265
    rw [hpc, hd]
    rfl
  · show t.sub = 0
    rw [hsub, hs]
  · show t.acc = []
    exact hacc.trans (siteAcc_nil d hs)
  · show t.fault = none
    exact hf
  · have hregs' : Holds t.regs (factsFrom ((Flow.live 264).filter
        (fun r => tracked.contains r)) (valueOf P L g d)) := by
      simpa [code, facts_maskReady hd] using hregs
    refine ⟨?_, holds_update hregs' ?_⟩
    · show (Function.update t.regs 4075 (some (Value.pred ok)) : Nat → Option Value) 4075 =
        some (.pred ok)
      exact Function.update_self ..
    · refine not_mem_factsFrom ?_
      decide +kernel

/-- **The mask-ready wait's step**: the poll's outcome selects the retry (back to pc 264) or
the QK completion's wait (pc 272). -/
theorem step_maskReady {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .maskReady)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 264 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      show d.sub = 0
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_264)
    obtain ⟨sc', hev⟩ := event_maskReady hpre hat hd
    rw [hev] at hf
    obtain ⟨ok, he, hu⟩ := fires_wait_next hf
    have hstep : next P L g d e =
        some (some (if ok then { d with site := .qkDone } else d)) := by
      rw [he]
      simp [next, nextSite, hd, waitStep]
    rcases hok : ok with _ | _
    · have hu' : u = PTX.next (setReg t 4075 (.pred false)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4075 (.pred false))) 265
          ((4075, .pred false) :: factsFrom ((Flow.live 264).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next hat hd hsub false
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 2
          (PTX.next (setReg t 4075 (.pred false))) = some t' ∧
          At t' 264 (factsFrom ((Flow.live 264).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := by
        seg_fp hstart using skip
      have hstep' : next P L g d e = some (some d) := by
        rw [hok] at hstep
        simpa using hstep
      rw [hstep']
      refine Or.inl (Or.inr ⟨d, t', rfl, ?_, ⟨?_, hinv⟩⟩)
      · rw [hu']
        exact run_rtg hr
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show t'.pc = d.site.pc
          rw [hpc]
          exact hat'.1
        · change t'.sub = d.sub
          rw [hsub]
          exact hat'.2.1
        · exact hat'.2.2.1.trans (siteAcc_nil d hsub).symm
        · exact hat'.2.2.2.1
        · simpa [code, facts_maskReady hd] using hat'.2.2.2.2
    · have hu' : u = PTX.next (setReg t 4075 (.pred true)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4075 (.pred true))) 265
          ((4075, .pred true) :: factsFrom ((Flow.live 264).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next hat hd hsub true
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 6
          (PTX.next (setReg t 4075 (.pred true))) = some t' ∧
          At t' 272 (facts P L g { d with site := .qkDone }) := by
        have hB : L.sharedBase + 222952 < 2 ^ 32 := sharedBase_lt hpre
        seg_fp hstart using
          (try simp only [valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
            Nat.reduceLeDiff, Nat.reduceLT, false_and, true_and, ite_false])
          (try (unfold sb b32))
          (try norm_bits [land255, Nat.add_zero])
          (try skip)
      set d' : D := { d with site := .qkDone } with hd'def
      have hstep' : next P L g d e = some (some d') := by
        rw [hok] at hstep
        simpa [hd'def] using hstep
      rw [hstep']
      have hgood : (code P L g).Good (some d') t' := by
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show t'.pc = 272
            exact hat'.1
          · change t'.sub = d.sub
            rw [hsub]
            exact hat'.2.1
          · exact hat'.2.2.1
          · exact hat'.2.2.2.1
          · simpa [code, facts_maskReady hd, hsub, hd'def] using hat'.2.2.2.2
        · have h := inv_setSite hinv .qkDone (by intro h; exact absurd h (by decide))
            (by intro h; exact absurd h (by decide))
            (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
            (by intro h; exact absurd h (by decide))
            (by rintro (h | h) <;> exact absurd h (by simp))
          simpa [code, hsub, hd'def] using h
      exact Or.inl (Or.inr ⟨d', t', rfl, run_rtg (by rw [hu']; exact hr), hgood⟩)

/-! ## The QK-completion wait

pc 272 polls `bar_qk_done[slot]` of the two-slot ring with the ring's phase, the second of the
body's two ring waits. The mask wait's pass arm forms both operands at pcs 267-271: `%r978` is
the phase `%r452` masked to a byte and `%r977` is `sb + 222904 + 8 * slot` (`qkDoneOff`), so the
table carries them as functions of the state's block. The poll's arms are the retry (pcs 273-274,
back to 272) and the pass (pc 273 to the Tensor Memory fence at pc 275). -/

theorem ringAddr_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {off buf : Nat} (ho : off + 8 * buf ≤ 222952) :
    L.sharedBase + (off + 8 * buf) < 2 ^ 32 := by
  have h := sharedBase_lt hpre
  omega

theorem ringAddr_mod8 {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {off buf : Nat} (ho : off % 8 = 0) :
    (L.sharedBase + (off + 8 * buf)) % 8 = 0 := by
  have h := sharedBase_mod8 hpre
  omega

/-- `%r977`, the address of the QK completion's word, at the QK-completion site. -/
theorem reg977 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .qkDone) :
    t.regs 977 = some (b32 (L.sharedBase + (222904 + 8 * (d.block % 2)))) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 977) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, sb, PTX.Flow.lookupLit, Option.getD_some] using h

/-- `%r978`, the two-slot ring's parity, at the QK-completion site. -/
theorem reg978 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .qkDone) :
    t.regs 978 = some (b32 (d.block / 2 % 2)) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 978) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h

/-- **The QK-completion poll's template**: the wait on `bar_qk_done[slot]` at the two-slot
ring's parity. -/
theorem event_qkDone {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} {t : TState}
    (hat : (code P L g).AtD d t) (hd : d.site = .qkDone) :
    ∃ sc', eventTmpl asms L g t (.mbarWait 4076 977 0 (.reg 978) true .cta) =
      .wait ⟨.shared, g / L.block, L.sharedBase + (222904 + 8 * (d.block % 2))⟩
        ((BitVec.ofNat 64 (d.block / 2 % 2)).toNat % 2)
        (fun ok => PTX.next (setReg t 4076 (.pred ok))) true sc' := by
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 977)
    (a := L.sharedBase + (222904 + 8 * (d.block % 2))) (reg977 hat hd)
    (ringAddr_lt hpre (buf := d.block % 2) (by omega))
    (ringAddr_mod8 hpre (off := 222904) (by decide))
  have hq := readBits_b32 (L := L) (g := g) (t := t) (r := 978) (a := d.block / 2 % 2)
    (reg978 hat hd) (by omega)
  obtain ⟨sc', h⟩ := eventTmpl_mbarWait_next (A := asms) hm hq
  exact ⟨sc', h⟩

/-- The QK-completion site's facts, with the site's program counter evaluated. -/
theorem facts_qkDone {d : D} (hd : d.site = .qkDone) :
    facts P L g d = factsFrom ((Flow.live 272).filter (fun r => tracked.contains r))
      (valueOf P L g d) := by
  simp only [facts, hd]
  rfl

/-- The state after the QK-completion poll: the thread is at the branch of pc 273 and `%r4076`
holds the outcome. -/
theorem at_wait_next_qk {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .qkDone)
    (hs : d.sub = 0) (ok : Bool) :
    At (PTX.next (setReg t 4076 (.pred ok))) 273
      ((4076, .pred ok) :: factsFrom ((Flow.live 272).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := hat
  have hpc : t.pc = d.site.pc := hpc
  have hsub : t.sub = d.sub := hsub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t.pc + 1 = 273
    rw [hpc, hd]
    rfl
  · show t.sub = 0
    rw [hsub, hs]
  · show t.acc = []
    exact hacc.trans (siteAcc_nil d hs)
  · show t.fault = none
    exact hf
  · have hregs' : Holds t.regs (factsFrom ((Flow.live 272).filter
        (fun r => tracked.contains r)) (valueOf P L g d)) := by
      simpa [code, facts_qkDone hd] using hregs
    refine ⟨?_, holds_update hregs' ?_⟩
    · show (Function.update t.regs 4076 (some (Value.pred ok)) : Nat → Option Value) 4076 =
        some (.pred ok)
      exact Function.update_self ..
    · refine not_mem_factsFrom ?_
      decide +kernel

/-- **The QK-completion wait's step**: the poll's outcome selects the retry (back to pc 272) or
the Tensor Memory fence (pc 275). -/
theorem step_qkDone {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .qkDone)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 272 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      show d.sub = 0
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_272)
    obtain ⟨sc', hev⟩ := event_qkDone hpre hat hd
    rw [hev] at hf
    obtain ⟨ok, he, hu⟩ := fires_wait_next hf
    have hstep : next P L g d e =
        some (some (if ok then { d with site := .fenceLoad } else d)) := by
      rw [he]
      simp [next, nextSite, hd, waitStep]
    rcases hok : ok with _ | _
    · have hu' : u = PTX.next (setReg t 4076 (.pred false)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4076 (.pred false))) 273
          ((4076, .pred false) :: factsFrom ((Flow.live 272).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next_qk hat hd hsub false
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 2
          (PTX.next (setReg t 4076 (.pred false))) = some t' ∧
          At t' 272 (factsFrom ((Flow.live 272).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := by
        seg_fp hstart using skip
      have hstep' : next P L g d e = some (some d) := by
        rw [hok] at hstep
        simpa using hstep
      rw [hstep']
      refine Or.inl (Or.inr ⟨d, t', rfl, ?_, ⟨?_, hinv⟩⟩)
      · rw [hu']
        exact run_rtg hr
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show t'.pc = d.site.pc
          rw [hpc]
          exact hat'.1
        · change t'.sub = d.sub
          rw [hsub]
          exact hat'.2.1
        · exact hat'.2.2.1.trans (siteAcc_nil d hsub).symm
        · exact hat'.2.2.2.1
        · simpa [code, facts_qkDone hd] using hat'.2.2.2.2
    · have hu' : u = PTX.next (setReg t 4076 (.pred true)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4076 (.pred true))) 273
          ((4076, .pred true) :: factsFrom ((Flow.live 272).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next_qk hat hd hsub true
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 1
          (PTX.next (setReg t 4076 (.pred true))) = some t' ∧
          At t' 275 (facts P L g { d with site := .fenceLoad }) := by
        seg_fp hstart using skip
      set d' : D := { d with site := .fenceLoad } with hd'def
      have hstep' : next P L g d e = some (some d') := by
        rw [hok] at hstep
        simpa [hd'def] using hstep
      rw [hstep']
      have hgood : (code P L g).Good (some d') t' := by
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show t'.pc = 275
            exact hat'.1
          · change t'.sub = d.sub
            rw [hsub]
            exact hat'.2.1
          · exact hat'.2.2.1
          · exact hat'.2.2.2.1
          · simpa [code, facts_qkDone hd, hsub, hd'def] using hat'.2.2.2.2
        · have h := inv_setSite hinv .fenceLoad (by intro h; exact absurd h (by decide))
            (by intro h; exact absurd h (by decide))
            (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
            (by intro h; exact absurd h (by decide))
            (by rintro (h | h) <;> exact absurd h (by simp))
          simpa [code, hsub, hd'def] using h
      exact Or.inl (Or.inr ⟨d', t', rfl, run_rtg (by rw [hu']; exact hr), hgood⟩)

/-- The softmax warpgroup's opening barrier leads to the current index-ring wait. -/
theorem step_wg0Sync {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .wg0Sync)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 256 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_1)
    have hr972 : t.regs 972 = some (b32 9) :=
      reg_value hat (by rw [hd]; decide +kernel)
    have hr973 : t.regs 973 = some (b32 128) :=
      reg_value hat (by rw [hd]; decide +kernel)
    have h9 := readBits_b32 (L := L) (g := g) hr972 (by decide : 9 < 2 ^ 32)
    have h128 := readBits_b32 (L := L) (g := g) hr973 (by decide : 128 < 2 ^ 32)
    have hbar : eventTmpl asms L g t (.barSyncN (.reg 972) (.reg 973) true) =
        .bar 9 (PTX.next t) (some 128) .sync := by
      simp [eventTmpl, barTmpl, h9, h128, hpre.block]
    rw [hbar] at hf
    obtain ⟨he, hu⟩ := hf
    let d' : D := { d with site := .maskReady, sub := 0 }
    have hu' : u = PTX.next t := Option.some.inj hu
    have hstart : At u 257
        (factsFrom ((Flow.live 256).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
      rw [hu']
      refine ⟨?_, ?_, hat.2.2.1.trans (siteAcc_nil d hsub), hat.2.2.2.1, ?_⟩
      · change t.pc + 1 = 257
        rw [show t.pc = d.site.pc from hat.1, hpc]
      · change t.sub = 0
        exact hat.2.1.trans hsub
      · simpa only [code, facts, hd, Site.pc, PTX.next] using hat.2.2.2.2
    have hB := sharedBase_lt hpre
    obtain ⟨t', hr, ht⟩ : ∃ t', run kernel asms L g 7 u = some t' ∧
        At t' 264 (facts P L g d') := by
      seg_fp hstart using
        (try simp only [d', valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
          Nat.reduceLeDiff, Nat.reduceLT, false_and, true_and, ite_false])
        (try (unfold sb b32))
        (try norm_bits [land255, Nat.add_zero, maskStride])
        (try omega)
    have hn : next P L g d e = some (some d') := by
      rw [he]
      simp [next, nextSite, hd, d', hsub]
    refine Or.inl (Or.inr ⟨d', t', hn, run_rtg hr, ?_, ?_⟩)
    · exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
    · apply inv_setSite hinv .maskReady <;> simp [Site.inEpilogue, Site.inRescale]

/-! ## The PV-completion wait

pc 1184 polls `bar_sv_done[slot]` of the two-slot ring with the ring's phase, the epilogue's
wait: the PV GEMM of warpgroup 1 must have read the last P tile before the epilogue overwrites
the staging region. The address is formed at pcs 1179-1182 (`sb + 222936 + 8 * slot`,
`svDoneOff`) on both arms of the row-sum exchange's branch, so the table carries `%r1736` as a
function of the state's block; the parity `%r2954` is the ring's phase. The poll's arms are the
retry (pcs 1185-1186, back to 1184) and the pass (pc 1185 to the epilogue's Tensor Memory fence
at pc 1187). -/

/-- `%r1736`, the address of the PV completion's word, at the PV-completion site. -/
theorem reg1736 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .svDone) :
    t.regs 1736 = some (b32 (L.sharedBase + (222936 + 8 * (d.block % 2)))) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 1736) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, sb, PTX.Flow.lookupLit, Option.getD_some] using h

/-- `%r2954`, the two-slot ring's parity, at the PV-completion site. -/
theorem reg2954_sv {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .svDone) :
    t.regs 2954 = some (b32 (d.block / 2 % 2)) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 2954) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using h

/-- **The PV-completion poll's template**: the wait on `bar_sv_done[slot]` at the two-slot
ring's parity. -/
theorem event_svDone {mem0 : Mem0} (hpre : Pre P L mem0) {d : D} {t : TState}
    (hat : (code P L g).AtD d t) (hd : d.site = .svDone) :
    ∃ sc', eventTmpl asms L g t (.mbarWait 4077 1736 0 (.reg 2954) true .cta) =
      .wait ⟨.shared, g / L.block, L.sharedBase + (222936 + 8 * (d.block % 2))⟩
        ((BitVec.ofNat 64 (d.block / 2 % 2)).toNat % 2)
        (fun ok => PTX.next (setReg t 4077 (.pred ok))) true sc' := by
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 1736)
    (a := L.sharedBase + (222936 + 8 * (d.block % 2))) (reg1736 hat hd)
    (ringAddr_lt hpre (buf := d.block % 2) (by omega))
    (ringAddr_mod8 hpre (off := 222936) (by decide))
  have hq := readBits_b32 (L := L) (g := g) (t := t) (r := 2954) (a := d.block / 2 % 2)
    (reg2954_sv hat hd) (by omega)
  obtain ⟨sc', h⟩ := eventTmpl_mbarWait_next (A := asms) hm hq
  exact ⟨sc', h⟩

/-- The PV-completion site's facts, with the site's program counter evaluated. -/
theorem facts_svDone {d : D} (hd : d.site = .svDone) :
    facts P L g d = factsFrom ((Flow.live 1184).filter (fun r => tracked.contains r))
      (valueOf P L g d) := by
  simp only [facts, hd]
  rfl

/-- The state after the PV-completion poll: the thread is at the branch of pc 1185 and `%r4077`
holds the outcome. -/
theorem at_wait_next_sv {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .svDone)
    (hs : d.sub = 0) (ok : Bool) :
    At (PTX.next (setReg t 4077 (.pred ok))) 1185
      ((4077, .pred ok) :: factsFrom ((Flow.live 1184).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  obtain ⟨hpc, hsub, hacc, hf, hregs⟩ := hat
  have hpc : t.pc = d.site.pc := hpc
  have hsub : t.sub = d.sub := hsub
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show t.pc + 1 = 1185
    rw [hpc, hd]
    rfl
  · show t.sub = 0
    rw [hsub, hs]
  · show t.acc = []
    exact hacc.trans (siteAcc_nil d hs)
  · show t.fault = none
    exact hf
  · have hregs' : Holds t.regs (factsFrom ((Flow.live 1184).filter
        (fun r => tracked.contains r)) (valueOf P L g d)) := by
      simpa [code, facts_svDone hd] using hregs
    refine ⟨?_, holds_update hregs' ?_⟩
    · show (Function.update t.regs 4077 (some (Value.pred ok)) : Nat → Option Value) 4077 =
        some (.pred ok)
      exact Function.update_self ..
    · refine not_mem_factsFrom ?_
      decide +kernel

/-- **The PV-completion wait's step**: the poll's outcome selects the retry (back to pc 1184) or
the epilogue's Tensor Memory fence (pc 1187). -/
theorem step_svDone {mem0 : Mem0} (hpre : Pre P L mem0) (d : D) (hd : d.site = .svDone)
    : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 1184 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      show d.sub = 0
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1184)
    obtain ⟨sc', hev⟩ := event_svDone hpre hat hd
    rw [hev] at hf
    obtain ⟨ok, he, hu⟩ := fires_wait_next hf
    have hstep : next P L g d e =
        some (some (if ok then { d with site := .fenceEpilogue } else d)) := by
      rw [he]
      simp [next, nextSite, hd, waitStep]
    rcases hok : ok with _ | _
    · have hu' : u = PTX.next (setReg t 4077 (.pred false)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4077 (.pred false))) 1185
          ((4077, .pred false) :: factsFrom ((Flow.live 1184).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next_sv hat hd hsub false
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 2
          (PTX.next (setReg t 4077 (.pred false))) = some t' ∧
          At t' 1184 (factsFrom ((Flow.live 1184).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := by
        seg_fp hstart using skip
      have hstep' : next P L g d e = some (some d) := by
        rw [hok] at hstep
        simpa using hstep
      rw [hstep']
      refine Or.inl (Or.inr ⟨d, t', rfl, ?_, ⟨?_, hinv⟩⟩)
      · rw [hu']
        exact run_rtg hr
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show t'.pc = d.site.pc
          rw [hpc]
          exact hat'.1
        · change t'.sub = d.sub
          rw [hsub]
          exact hat'.2.1
        · exact hat'.2.2.1.trans (siteAcc_nil d hsub).symm
        · exact hat'.2.2.2.1
        · simpa [code, facts_svDone hd] using hat'.2.2.2.2
    · have hu' : u = PTX.next (setReg t 4077 (.pred true)) := by rw [hu, hok]
      have hstart : At (PTX.next (setReg t 4077 (.pred true))) 1185
          ((4077, .pred true) :: factsFrom ((Flow.live 1184).filter (fun r => tracked.contains r))
            (valueOf P L g d)) := at_wait_next_sv hat hd hsub true
      obtain ⟨t', hr, hat'⟩ : ∃ t', run kernel asms L g 1
          (PTX.next (setReg t 4077 (.pred true))) = some t' ∧
          At t' 1187 (facts P L g { d with site := .fenceEpilogue }) := by
        seg_fp hstart using skip
      set d' : D := { d with site := .fenceEpilogue } with hd'def
      have hstep' : next P L g d e = some (some d') := by
        rw [hok] at hstep
        simpa [hd'def] using hstep
      rw [hstep']
      have hgood : (code P L g).Good (some d') t' := by
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show t'.pc = 1187
            exact hat'.1
          · change t'.sub = d.sub
            rw [hsub]
            exact hat'.2.1
          · exact hat'.2.2.1
          · exact hat'.2.2.2.1
          · simpa [code, facts_svDone hd, hsub, hd'def] using hat'.2.2.2.2
        · have h := inv_setSite hinv .fenceEpilogue
            (by intro _; exact hinv.epilogueLast (by rw [hd]; rfl))
            (by intro h; exact absurd h (by decide))
            (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
            (by intro h; exact absurd h (by decide))
            (by rintro (h | h) <;> exact absurd h (by simp))
            (fun _ => hinv.rowTotal (by rw [hd]; rfl))
          simpa [code, hsub, hd'def] using h
      exact Or.inl (Or.inr ⟨d', t', rfl, run_rtg (by rw [hu']; exact hr), hgood⟩)

/-! ## The valid-mask ring's free arrival

pc 571 arrives on `bar_valid_coord_free[vslot]`, telling the index warp that the block's
`is_token_valid` word is no longer needed. The address is `sb + 222872 + 8 * vslot`
(`validFreeOff`) in `%r1000`, formed at pc 570; the arrival takes no data register, and its
continuation is the partner's row maximum at pc 572. -/

/-- `%r1000`, the address of the mask ring's free word, at the free-arrival site. -/
theorem reg1000 {d : D} {t : TState} (hat : (code P L g).AtD d t) (hd : d.site = .validFree) :
    t.regs 1000 = some (b32 (L.sharedBase + (222872 + 8 * (d.block % 4)))) := by
  have h := reg_value (P := P) (L := L) (g := g) (d := d) hat (r := 1000) (by
    rw [hd]; decide +kernel)
  simpa [valueOf, table, sb, PTX.Flow.lookupLit, Option.getD_some] using h

/-- The free-arrival site's facts, with the site's program counter evaluated. -/
theorem facts_validFree {d : D} (hd : d.site = .validFree) :
    facts P L g d = factsFrom ((Flow.live 571).filter (fun r => tracked.contains r))
      (valueOf P L g d) := by
  simp only [facts, hd]
  rfl
end

/-- **The free arrival's step**: the arrival continues at the partner's row maximum, whose facts
are the arrival state's without the address register. -/
theorem step_validFree {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}
    (hpre : Pre P L mem0) (d : D) (hd : d.site = .validFree) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 571 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      show d.sub = 0
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_571)
    have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 1000)
      (a := L.sharedBase + (222872 + 8 * (d.block % 4))) (reg1000 hat hd)
      (ringAddr_lt hpre (buf := d.block % 4) (by omega))
      (ringAddr_mod8 hpre (off := 222872) (by decide))
    have hb : readBits L g t 32 (.imm 0) = .ok (BitVec.ofNat 64 0) := by
      simp only [readBits, truncBits]; rfl
    have hn : readBits L g t 32 (.imm 1) = .ok (BitVec.ofNat 64 1) := by
      simp only [readBits, truncBits]; rfl
    obtain ⟨rrel, rsc, he, hu⟩ := fires_arrive_next (A := asms) (L := L) (g := g) (t := t)
      (base := 1000) (off := 0) (tx := .imm 0) (count := .imm 1) (cluster := false)
      (rel := true) (sc := .cta) (pc := 571) hm hb hn hf
    have hu' : u = PTX.next t := Option.some.inj hu
    set d' : D := { d with site := .maxRead } with hd'def
    have hstep : next P L g d e = some (some d') := by
      rw [he]
      simp [next, nextSite, hd, hd'def]
    rw [hstep]
    have hF : Holds t.regs (factsFrom ((Flow.live 571).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
      simpa [code, facts_validFree hd] using hat.2.2.2.2
    have hsub' : ∀ r ∈ (Flow.live 572).filter (fun r => tracked.contains r),
        r ∈ (Flow.live 571).filter (fun r => tracked.contains r) := by decide +kernel
    refine Or.inl (Or.inr ⟨d', u, rfl, ?_, ⟨?_, ?_⟩⟩)
    · exact .refl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show u.pc = 572
        rw [hu']
        have h1 : t.pc = d.site.pc := hat.1
        show t.pc + 1 = 572
        omega
      · change u.sub = d.sub
        rw [hu']
        exact hat.2.1
      · change u.acc = siteAcc d'
        rw [hu']
        simpa [code, siteAcc, hd, hd'def, PTX.next] using hat.2.2.1
      · change u.fault = none
        rw [hu']
        exact hat.2.2.2.1
      · have h := holds_factsFrom_mono hF hsub'
        rw [hu', hd'def]
        exact h
    · have h := inv_setSite hinv .maxRead (by intro h; exact absurd h (by decide))
        (by intro h; exact absurd h (by decide))
        (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
        (by intro h; exact absurd h (by decide))
        (by rintro (h | h) <;> exact absurd h (by simp))
      simpa [code, hsub, hd'def] using h

/-! ## The run from the entry to the first site

The role's first event is one of the three `.nc` reads or the bulk wait; the thread reaches it
from pc 104 through the staging address arithmetic (`cvta.shared.u64`, the pointer moves and the
SW128 swizzle), the parameter loads of the sink and the length pointers, and the four tests that
decide which of them is read. The parameter loads, the pointer moves and the `cvta`s are
one-instruction steps (`Core`'s rules read launch data that a segment's evaluation cannot see);
the rest runs as segments. The register facts are the live registers, valued by the role's
table (`startFacts`). -/

variable {P : Params} {L : Launch} {g : Nat} {mem0 : Mem0}

/-- The table's values, as `simp` reduces them after a segment's evaluation. -/
macro "wg0_values" : tactic =>
  `(tactic| simp only [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
    Option.getD_none, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT, true_and, false_and,
    and_true, and_false, ite_false, ite_true])

/-- The thread index is one of the CTA's 384. -/
theorem tid384 (hpre : Pre P L mem0) : tidOf L g < 384 := by
  rw [tidOf_eq hpre]; omega

/-- `%tid = 32 * warp + lane` (`warpOf` and `laneOf` are the division and remainder by 32). -/
theorem tid_eq (L : Launch) (g : Nat) : tidOf L g = 32 * warpOf L g + laneOf L g := by
  unfold warpOf laneOf
  have := Nat.div_add_mod (tidOf L g) 32
  omega

/-- A 32-lane warp's index divided by 64 is the warp's half. -/
theorem tid_div64_of (c r l : Nat) (hr : r < 2) (hl : l < 32) :
    (32 * (2 * c + r) + l) / 64 = c := by omega

/-- `%tid / 64` is the warp's half: the lane is below 32. -/
theorem tid_div64 (L : Launch) (g : Nat) : tidOf L g / 64 = warpOf L g / 2 := by
  rw [tid_eq L g]
  conv_lhs =>
    rw [show warpOf L g = 2 * (warpOf L g / 2) + warpOf L g % 2 from
      (Nat.div_add_mod (warpOf L g) 2).symm]
  exact tid_div64_of _ _ _ (Nat.mod_lt _ (by decide)) (laneLt L g)

/-- The entry state is a state of the run's first segment: the prologue's facts at pc 104 are the
run's table there (the two parameter pointers and the launch reads are the prologue's own
values). -/
theorem entry_at {t : TState} (hentry : Entry P L g t) :
    At t 104 (startFacts P L g 104) := by
  have hlive : startLive 104 = [459, 460, 461, 463, 465, 466, 2880, 2990, 2991] := by
    decide +kernel
  refine ⟨hentry.pc, hentry.sub, hentry.acc, hentry.fault, ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  rw [hlive] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    exact holds_mem hentry.regs
      (mem_factsFrom (val := _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g)
        (by decide +kernel))

/-- The first segment: the head and warp-half words, the shared base word and the `cvta.shared`
source. -/
theorem run_104_110 (hpre : Pre P L mem0) (hwg : wgOf L g = 0) {t : TState}
    (h : At t 104 (startFacts P L g 104)) :
    ∃ t', run kernel asms L g 6 t = some t' ∧ At t' 110 (startFacts P L g 110) := by
  have ht : tidOf L g < 384 := tid384 hpre
  have h1 : tidOf L g % 4294967296 = tidOf L g := Nat.mod_eq_of_lt (by omega)
  have h2 : tidOf L g * 64 % 4294967296 = tidOf L g * 64 := Nat.mod_eq_of_lt (by omega)
  have h2' : tidOf L g * 128 % 4294967296 = tidOf L g * 128 :=
    Nat.mod_eq_of_lt (by omega)
  have h3 : tidOf L g * 64 / 64 = tidOf L g := Nat.mul_div_cancel _ (by decide)
  have h3' : tidOf L g * 128 / 8192 = tidOf L g / 64 := by
    rw [show (8192 : Nat) = 128 * 64 from by norm_num, ← Nat.div_div_eq_div_mul]
    rw [show tidOf L g * 128 / 128 = tidOf L g from by omega]
  have h5 : (tidOf L g / 64) % 2 = half L g := by
    have hw4 : warpOf L g < 4 := warpLt hpre hwg
    rw [tid_div64 L g]
    unfold half
    omega
  have hb32 : L.sharedBase < 2 ^ 32 := by
    have := sharedBase_lt hpre
    omega
  seg_fp h using
    (try wg0_values)
    (try nf_simp)
    (try simp only [h1, h2, h3, h2', h3', h5, land_4032, land_8192, head, half])
    (try omega)

/-- A register live at a state of the entry run holds the run's table value. -/
theorem start_fact {t : TState} {pc : Nat} {r : Nat}
    (h : At t pc (startFacts P L g pc)) (hr : r ∈ startLive pc) :
    t.regs r = some (startValue P L g r) :=
  holds_mem h.2.2.2.2 (mem_factsFrom hr)

section
variable {t : TState}

/-- A local step that writes one register with the table's value, from the entry run's facts at
`pc` to the table's facts at `pc + 1`: every register live at `pc + 1` was live at `pc` or is the
written one, and the written value is the table's. -/
theorem at_next_set {pc : Nat} {r : Nat} (h : At t pc (startFacts P L g pc)) (hr : r ∉ startLive pc)
    (hl : ∀ x ∈ startLive (pc + 1), x ∈ r :: startLive pc) :
    At (PTX.next (setReg t r (startValue P L g r))) (pc + 1)
      (startFacts P L g (pc + 1)) := by
  have hset : At (PTX.next (setReg t r (startValue P L g r))) (pc + 1)
      ((r, startValue P L g r) :: startFacts P L g pc) :=
    At.set h (not_mem_factsFrom hr)
  have h' : At (PTX.next (setReg t r (startValue P L g r))) (pc + 1)
      (factsFrom (r :: startLive pc) (startValue P L g)) := by
    simpa [startFacts, factsFrom] using hset
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, holds_factsFrom_mono h'.2.2.2.2 hl⟩

theorem ctaLt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) (hg : g < L.threads) :
    g / L.block < L.grid := by
  rw [Nat.div_lt_iff_lt_mul (by rw [hpre.block]; decide)]
  exact hg

/-! ## The parameter words and the predicates of the skips before the loop

Pcs 146-198 read the scale and the three optional pointers out of the scalar parameter object,
test them, and form the padded block count `%r473` (`64 * blocksOf`) on the way. The loads'
words, the tests' predicates and the block count are functions of the launch and the state's
block, so they are stated by the role's table (`startValue`); these lemmas evaluate the
tests and the count. -/

theorem paramWord_8 (hpre : Pre P L mem0) : paramWord L 8 4 = 64 := by
  have h := Thread.paramWord_four (L := L) (off := 8) (x := 64) fun k hk => by
    simpa using hpre.paramHq k hk
  rwa [Nat.mod_eq_of_lt (by norm_num : 64 < 2 ^ 32)] at h

theorem paramWord_40 (hpre : Pre P L mem0) : paramWord L 40 4 = P.topk := by
  have h := Thread.paramWord_four (L := L) (off := 40) (x := P.topk) fun k hk => by
    simpa using hpre.paramTopk k hk
  show Thread.paramWord L 40 4 = P.topk
  rw [h]
  have hle := hpre.topkAdd63Lt
  exact Nat.mod_eq_of_lt (by omega)

theorem paramWord_120 (hpre : Pre P L mem0) : paramWord L 120 4 = P.extra_topk := by
  have h := Thread.paramWord_four (L := L) (off := 120) (x := P.extra_topk) fun k hk => by
    simpa using hpre.paramExtraTopk k hk
  show Thread.paramWord L 120 4 = P.extra_topk
  rw [h]
  have hle := hpre.extraTopkAdd63Lt
  exact Nat.mod_eq_of_lt (by omega)

theorem paramWord_88_zero (hpre : Pre P L mem0) (h : P.sinkBase = none) :
    paramWord L 88 8 = 0 := by
  have hb := hpre.paramSink
  rw [h] at hb
  obtain ⟨hbytes, -⟩ := hb
  have e := Thread.paramWord_eight (x := 0) fun k hk => by simpa [leByte] using hbytes k hk
  show Thread.paramWord L 88 8 = 0
  rw [e]
  exact Nat.zero_mod _

theorem paramWord_88_some (hpre : Pre P L mem0) {x : Nat} (h : P.sinkBase = some x) :
    paramWord L 88 8 = x % 2 ^ 64 := by
  have hb := hpre.paramSink
  rw [h] at hb
  obtain ⟨hptr, -, -⟩ := hb
  exact Thread.paramWord_eight fun k hk => by simpa using hptr k hk

theorem supplied_int {off x n : Nat} (h : intBytes x off (param "0") L) (hn : n ≤ 4) :
    ParamSupplied L (param "0") off n :=
  fun k hk => ⟨leByte x k, by simpa using h k (by omega)⟩

theorem supplied_ptr {off x n : Nat} (h : ptrBytes x off (param "0") L) (hn : n ≤ 8) :
    ParamSupplied L (param "0") off n :=
  fun k hk => ⟨leByte x k, by simpa using h k (by omega)⟩

theorem supplied_80 (hpre : Pre P L mem0) : ParamSupplied L (param "0") 80 8 := by
  cases h : P.topkLenBase with
  | none =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    obtain ⟨hbytes, -⟩ := hb
    exact fun k hk => ⟨0, hbytes k hk⟩
  | some x =>
    have hb := hpre.paramTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

theorem supplied_144 (hpre : Pre P L mem0) : ParamSupplied L (param "0") 144 8 := by
  cases h : P.extraTopkLenBase with
  | none =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    obtain ⟨hbytes, -⟩ := hb
    exact fun k hk => ⟨0, hbytes k hk⟩
  | some x =>
    have hb := hpre.paramExtraTopkLen
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

theorem supplied_88 (hpre : Pre P L mem0) : ParamSupplied L (param "0") 88 8 := by
  cases h : P.sinkBase with
  | none =>
    have hb := hpre.paramSink
    rw [h] at hb
    obtain ⟨hbytes, -⟩ := hb
    exact fun k hk => ⟨0, hbytes k hk⟩
  | some x =>
    have hb := hpre.paramSink
    rw [h] at hb
    exact fun k hk => ⟨_, hb.1 k hk⟩

theorem truncBits_int_zero : truncBits 64 (BitVec.ofInt 64 0) = 0 := by decide

theorem truncBits_nat (x : Nat) :
    truncBits 64 (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x % 2 ^ 64) := by
  simp [truncBits, BitVec.toNat_ofNat]

theorem compare_eq_b64_zero_false {x : Nat} (hpos : 0 < x) (hlt : x < 2 ^ 64) :
    compare .eq .b 64 (BitVec.ofNat 64 x) (truncBits 64 (BitVec.ofInt 64 0)) = false := by
  rw [truncBits_int_zero]
  simp only [compare, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hlt]
  have : (x : Int) ≠ 0 := by omega
  simpa using this

theorem compare_eq_b64_zero_true :
    compare .eq .b 64 (BitVec.ofNat 64 0) (truncBits 64 (BitVec.ofInt 64 0)) = true := by
  rw [truncBits_int_zero]; rfl

theorem compare_ge_s32_false {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h : a < b) :
    compare .ge .s 32 (truncBits 32 (BitVec.ofNat 64 a))
      (truncBits 32 (BitVec.ofNat 64 b)) = false := by
  norm_signed

theorem ptrIsNull_none {off : Nat} (hw : Thread.paramWord L off 8 = 0) :
    Thread.ptrIsNull L off = true := by
  unfold Thread.ptrIsNull
  rw [hw]
  exact compare_eq_b64_zero_true

theorem ptrIsNull_some {off : Nat} {x : Nat} (hw : Thread.paramWord L off 8 = x % 2 ^ 64)
    (hpos : 0 < x) (hlt : x < 2 ^ 64) : Thread.ptrIsNull L off = false := by
  unfold Thread.ptrIsNull
  rw [hw, truncBits_nat]
  rw [show x % 2 ^ 64 % 2 ^ 64 = x % 2 ^ 64 from Nat.mod_mod_of_dvd x (by decide)]
  rw [Nat.mod_eq_of_lt hlt]
  exact compare_eq_b64_zero_false hpos hlt

theorem ptrIsNull_88_none (hpre : Pre P L mem0) (h : P.sinkBase = none) :
    Thread.ptrIsNull L 88 = true :=
  ptrIsNull_none (paramWord_88_zero hpre h)

theorem ptrIsNull_88_some (hpre : Pre P L mem0) {x : Nat} (h : P.sinkBase = some x) :
    Thread.ptrIsNull L 88 = false :=
  ptrIsNull_some (paramWord_88_some hpre h) (hpre.sinkNonNull x h) (hpre.sinkBaseLt x h)

theorem ptrIsNull_80_none (hpre : Pre P L mem0) (h : P.topkLenBase = none) :
    Thread.ptrIsNull L 80 = true :=
  ptrIsNull_none (Thread.paramWord_80_zero hpre h)

theorem ptrIsNull_80_some (hpre : Pre P L mem0) {x : Nat} (h : P.topkLenBase = some x) :
    Thread.ptrIsNull L 80 = false :=
  ptrIsNull_some (Thread.paramWord_80_some hpre h) (hpre.topkLenNonNull x h)
    (hpre.topkLenBaseLt x h)

theorem ptrIsNull_144_none (hpre : Pre P L mem0) (h : P.extraTopkLenBase = none) :
    Thread.ptrIsNull L 144 = true :=
  ptrIsNull_none (Thread.paramWord_144_zero hpre h)

theorem ptrIsNull_144_some (hpre : Pre P L mem0) {x : Nat} (h : P.extraTopkLenBase = some x) :
    Thread.ptrIsNull L 144 = false :=
  ptrIsNull_some (Thread.paramWord_144_some hpre h) (hpre.extraTopkLenNonNull x h)
    (hpre.extraTopkLenBaseLt x h)

theorem geBatch_false (hpre : Pre P L mem0) (hbatch : ctaidY L g < P.b) :
    Thread.geBatch L g = false := by
  have hb32 : P.b % 2 ^ 32 = P.b := Nat.mod_eq_of_lt (by have := hpre.bLt; omega)
  have hparam : Thread.paramWord L 0 4 = P.b := by
    rw [Thread.paramWord_b hpre, hb32]
  have ha : ctaidY L g < 2 ^ 31 := lt_trans hbatch hpre.bLt
  unfold Thread.geBatch
  rw [show Thread.ctaidY L g = ctaidY L g from rfl, hparam]
  exact compare_ge_s32_false ha hpre.bLt hbatch

theorem headGe_false (hpre : Pre P L mem0) : headGe L g = false := by
  have hh : head L g < 64 := head_lt L g
  have hp : Thread.paramWord L 8 4 = 64 := paramWord_8 hpre
  unfold headGe
  rw [hp]
  exact compare_ge_s32_false (by omega) (by norm_num) hh

theorem ceilToMultiple_eq_self {n d : Nat} (hd : 0 < d) (h : d ∣ n) :
    Result.ceilToMultiple n d = n := by
  obtain ⟨k, rfl⟩ := h
  unfold Result.ceilToMultiple
  have hdiv : (d * k + d - 1) / d = k := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm k d]; omega
    · rw [Nat.add_mul, one_mul, Nat.mul_comm k d]; omega
  rw [hdiv, Nat.mul_comm]

theorem blocksOf_mul (hpre : Pre P L mem0) (hbatch : ctaidY L g < P.b)
    (h0 : P.topkLenBase = none) (h1 : P.extraTopkLenBase = none) :
    64 * blocksOf P L g = P.topk + P.extra_topk := by
  have ht : P.topkLen (eOf L g) = P.topk := by
    have hb := hpre.paramTopkLen
    rw [h0] at hb
    exact hb.2 (eOf L g) hbatch
  have he : P.extraTopkLen (eOf L g) = P.extra_topk := by
    have hb := hpre.paramExtraTopkLen
    rw [h1] at hb
    exact hb.2 (eOf L g) hbatch
  have hdvd : 64 ∣ P.topk + P.extra_topk := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpre.topkDiv64, hpre.extraDiv64]
  unfold blocksOf Result.blocks Result.totalBlocks Result.origPadded Result.topkBlock
  rw [ht, he,
    ceilToMultiple_eq_self (by decide) (Nat.dvd_of_mod_eq_zero hpre.topkDiv64),
    ceilToMultiple_eq_self (by decide) (Nat.dvd_of_mod_eq_zero hpre.extraDiv64),
    max_eq_left (Nat.le_of_dvd hpre.topkPos (Nat.dvd_of_mod_eq_zero hpre.topkDiv64))]
  rw [Nat.mul_comm]
  exact Nat.div_mul_cancel hdvd

/-- Xor of two 64-bit patterns in the `Nat` normal form. -/
theorem nf_xor (a b : Nat) : BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 ^^^ b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 18446744073709551616 ^^^ b % 18446744073709551616 < 18446744073709551616 :=
    Nat.xor_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt h1]

theorem land63 (a : Nat) : a &&& 63 = a % 64 := Nat.and_two_pow_sub_one_eq_mod a 6

theorem truncBits_int_63 : truncBits 32 (BitVec.ofInt 64 63) = BitVec.ofNat 64 63 := by decide

theorem truncBits_int_1 : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := by decide

theorem truncBits_int_2 : truncBits 32 (BitVec.ofInt 64 2) = BitVec.ofNat 64 2 := by decide

theorem truncBits_int_256 : truncBits 32 (BitVec.ofInt 64 256) = BitVec.ofNat 64 256 := by decide

theorem truncBits_int_26 : truncBits 32 (BitVec.ofInt 64 26) = BitVec.ofNat 64 26 := by decide

theorem truncBits_int_31 : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := by decide

theorem truncBits_int_neg64 : truncBits 32 (BitVec.ofInt 64 (-64)) =
    BitVec.ofNat 64 (2 ^ 32 - 64) := by decide

/-! ## The two parameter loads and the four tests, to the first site -/

theorem ld_start (hpre : Pre P L mem0) {t : TState} {pc w off d : Nat} {ty : DType}
    (hc : kernel.code[pc]? = some ⟨none, .mem (Thread.paramLoad ty off 2991 d)⟩)
    (hsup : ParamSupplied L (param "0") off (w / 8))
    (hsze : off + w / 8 ≤ 304)
    (hal : 0 < w / 8 ∧ off % (w / 8) = 0 ∧ (8 : Nat) % (w / 8) = 0)
    (h : At t pc (startFacts P L g pc))
    (hv : paramElem w w (paramNat L (param "0") off (w / 8)) = startValue P L g d)
    (hr0 : d ∉ startLive pc)
    (hl : ∀ x ∈ startLive (pc + 1), x ∈ d :: startLive pc)
    (h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0))
    (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (hsf : Assumption.SegFreePc asms pc := by seg_free_pc)
    (hw : ty.width = w := by rfl)
    (hr : (Thread.paramLoad ty off 2991 d).rule = some .threadMove := by rfl) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' (pc + 1) (startFacts P L g (pc + 1)) := by
  have hL : ∀ b ∈ asms, b.localRule L g t (.mem (Thread.paramLoad ty off 2991 d)) = none := by
    intro b hb
    exact Thread.asms_localRule_mem (t := t) (by rw [h.1]; exact h1)
      (by rw [h.1]; exact h2) b hb
  refine ⟨PTX.next (setReg t d (startValue P L g d)), ?_, ?_⟩
  · rw [← hv]
    exact run_local hc rfl h (Thread.exec_ldParamReg (A := asms) (L := L) (g := g)
      (w := w) (off := off) (r := 2991) (d := d) (t := t) (p := param "0") (ty := ty)
      (decl := scalarsParam) (base := P.param0Base) h2991 hpre.param0Object
      ⟨by omega, hsze⟩ hal hsup (Assumption.SegFreePc.of_eq h.1 hsf) hL hw hr)
  · exact at_next_set (P := P) (L := L) (g := g) (pc := pc) (r := d) h hr0 hl

theorem bra_to {pc target p b : Nat} {pick : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, false), .bra target false⟩)
    (h : At t pc (startFacts P L g pc)) (hp : p ∈ startLive pc)
    (hv : startValue P L g p = .pred pick) (hb : b = if pick then target else pc + 1)
    (hl : ∀ r ∈ startLive b, r ∈ startLive pc) (h1 : pc ∉ paramAdds)
    (h2 : pc ∉ prefetchTensorMapSites) (hsf : Assumption.SegFreePc asms pc := by seg_free_pc) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' b (startFacts P L g b) := by
  have hL : ∀ a ∈ asms, a.localRule L g t (.bra target false) = none := by
    intro a ha
    exact Thread.asms_localRule_bra (t := t) (by rw [h.1]; exact h1) (by rw [h.1]; exact h2) a ha
  obtain ⟨t', hr, ht⟩ :=
    run_bra (K := kernel) (A := asms) (L := L) (g := g) hc pick h
      (hv ▸ holds_mem h.2.2.2.2 (mem_factsFrom hp)) hL hsf
  rw [← hb] at ht
  exact ⟨t', hr, At.mono ht (holds_factsFrom_mono ht.2.2.2.2 hl)⟩

theorem run_146_147 (hpre : Pre P L mem0) {t : TState}
    (h : At t 146 (startFacts P L g 146)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 147 (startFacts P L g 147) := by
  obtain ⟨bits, hbits, hb, hdec⟩ := hpre.paramScale
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 146) (w := 32)
    (off := 28) (d := 467) (ty := .int .b 32)
    Flow.code_146 (supplied_int (off := 28) (x := bits) hb (by decide)) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

theorem run_147_148 (hpre : Pre P L mem0) {t : TState}
    (h : At t 147 (startFacts P L g 147)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 148 (startFacts P L g 148) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 147) (w := 64)
    (off := 88) (d := 3000) (ty := .int .b 64)
    Flow.code_147 (supplied_88 hpre) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

theorem run_148_149 (h : At t 148 (startFacts P L g 148)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 149 (startFacts P L g 149) := by
  seg_fp h using
    (try wg0_values)

theorem run_149_150 (hpre : Pre P L mem0) {x : Nat} {t : TState}
    (h : At t 149 (startFacts P L g 149)) (hs : P.sinkBase = some x) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 150 (startFacts P L g 150) := by
  have hp := ptrIsNull_88_some (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 149) (target := 158) (p := 69)
    (pick := false) (b := 150) Flow.code_149 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_150_151 (h : At t 150 (startFacts P L g 150)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 151 (startFacts P L g 151) := by
  seg_fp h using
    (try wg0_values)
    (try (rw [truncBits_int_63]))
    (try (norm_bits [land63, head]))

theorem run_151_152 (hpre : Pre P L mem0) {t : TState}
    (h : At t 151 (startFacts P L g 151)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 152 (startFacts P L g 152) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 151) (w := 32)
    (off := 8) (d := 931) (ty := .int .b 32)
    Flow.code_151 (supplied_int (off := 8) (x := 64) hpre.paramHq (by decide)) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

theorem run_152_153 (h : At t 152 (startFacts P L g 152)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 153 (startFacts P L g 153) := by
  seg_fp h using
    (try wg0_values)
    (try (simp only [headGe]))

theorem run_153_154 (hpre : Pre P L mem0) {t : TState}
    (h : At t 153 (startFacts P L g 153)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 154 (startFacts P L g 154) := by
  have hg := headGe_false (P := P) (L := L) (g := g) (mem0 := mem0) hpre
  refine bra_to (P := P) (L := L) (g := g) (pc := 153) (target := 158) (p := 70)
    (pick := false) (b := 154) Flow.code_153 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hg]

theorem run_154_156 (h : At t 154 (startFacts P L g 154)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 156 (startFacts P L g 156) := by
  have hhh : head L g < 64 := head_lt L g
  seg_fp h using
    (try wg0_values)
    (try nf_simp)
    (try omega)
end

section
variable (hpre : Pre P L mem0)
include hpre

theorem run_149_158 {t : TState} (h : At t 149 (startFacts P L g 149)) (hs : P.sinkBase = none) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 158 (startFacts P L g 158) := by
  have hp := ptrIsNull_88_none (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 149) (target := 158) (p := 69)
    (pick := true) (b := 158) Flow.code_149 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_158_159 {t : TState} (h : At t 158 (startFacts P L g 158)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 159 (startFacts P L g 159) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 158) (w := 32)
    (off := 0) (d := 933) (ty := .int .b 32)
    Flow.code_158 (supplied_int (off := 0) (x := P.b) hpre.paramB (by decide)) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

omit hpre in
theorem run_159_160 {t : TState}
    (h : At t 159 (startFacts P L g 159)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 160 (startFacts P L g 160) := by
  seg_fp h using
    (try wg0_values)
    (try (simp only [Thread.geBatch, Thread.ctaidY, eOf, ctaidY, Thread.ctaOf, ctaOf]))

theorem run_160_161 {t : TState} (h : At t 160 (startFacts P L g 160)) (hbatch : ctaidY L g < P.b) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 161 (startFacts P L g 161) := by
  have hg := geBatch_false (P := P) (L := L) (g := g) (mem0 := mem0) hpre hbatch
  refine bra_to (P := P) (L := L) (g := g) (pc := 160) (target := 1836) (p := 71)
    (pick := false) (b := 161) Flow.code_160 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hg]

theorem run_161_163 {t : TState} (h : At t 161 (startFacts P L g 161)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 163 (startFacts P L g 163) := by
  have hw := warpOf_lt (g := g) hpre
  seg_fp h using
    (try wg0_values)
    (try (rw [truncBits_int_1]))
    (try norm_bits)
    (try rfl)

theorem run_163_164 {t : TState} (h : At t 163 (startFacts P L g 163)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 164 (startFacts P L g 164) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 163) (w := 64)
    (off := 80) (d := 3002) (ty := .int .b 64)
    Flow.code_163 (supplied_80 hpre) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

omit hpre in
theorem run_164_165 {t : TState}
    (h : At t 164 (startFacts P L g 164)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 165 (startFacts P L g 165) := by
  seg_fp h using
    (try wg0_values)

theorem run_165_166 {x : Nat} {t : TState} (h : At t 165 (startFacts P L g 165))
    (hs : P.topkLenBase = some x) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 166 (startFacts P L g 166) := by
  have hp := ptrIsNull_80_some (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 165) (target := 170) (p := 72)
    (pick := false) (b := 166) Flow.code_165 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_165_170 {t : TState} (h : At t 165 (startFacts P L g 165)) (hs : P.topkLenBase = none) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 170 (startFacts P L g 170) := by
  have hp := ptrIsNull_80_none (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 165) (target := 170) (p := 72)
    (pick := true) (b := 170) Flow.code_165 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_166_168 {t : TState} (h : At t 166 (startFacts P L g 166)) (hbatch : ctaidY L g < P.b) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 168 (startFacts P L g 168) := by
  have he : eOf L g < 2 ^ 31 := lt_trans (by rw [show eOf L g = ctaidY L g from rfl]; exact hbatch)
    hpre.bLt
  seg_fp h using
    (try wg0_values)
    (try nf_simp)
    (try omega)

theorem run_170_171 {t : TState} (h : At t 170 (startFacts P L g 170)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 171 (startFacts P L g 171) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 170) (w := 32)
    (off := 40) (d := 2881) (ty := .int .b 32)
    Flow.code_170 (supplied_int (off := 40) (x := P.topk) hpre.paramTopk (by decide)) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

theorem run_171_176 {t : TState} (h : At t 171 (startFacts P L g 171)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧ At t' 176 (startFacts P L g 176) := by
  have hread : (init P L g).origLenRead = false := rfl
  have hp : Thread.paramWord L 40 4 = P.topk := paramWord_40 hpre
  have hle := hpre.topkAdd63Lt
  seg_fp h using
    (try wg0_values)
    (try simp only [hread, Bool.false_eq_true, ite_false])
    (try (simp only [truncBits_int_63, truncBits_int_26, truncBits_int_31,
      truncBits_int_neg64, hp]))
    (try norm_signed)

theorem run_176_177 {t : TState} (h : At t 176 (startFacts P L g 176)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 177 (startFacts P L g 177) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 176) (w := 64)
    (off := 144) (d := 3003) (ty := .int .b 64)
    Flow.code_176 (supplied_144 hpre) (by decide)
    ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

omit hpre in
theorem run_177_178 {t : TState}
    (h : At t 177 (startFacts P L g 177)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 178 (startFacts P L g 178) := by
  seg_fp h using
    (try wg0_values)

theorem run_178_179 {x : Nat} {t : TState} (h : At t 178 (startFacts P L g 178))
    (hs : P.extraTopkLenBase = some x) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 179 (startFacts P L g 179) := by
  have hp := ptrIsNull_144_some (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 178) (target := 183) (p := 73)
    (pick := false) (b := 179) Flow.code_178 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_178_183 {t : TState} (h : At t 178 (startFacts P L g 178))
    (hs : P.extraTopkLenBase = none) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 183 (startFacts P L g 183) := by
  have hp := ptrIsNull_144_none (P := P) (L := L) (mem0 := mem0) hpre hs
  refine bra_to (P := P) (L := L) (g := g) (pc := 178) (target := 183) (p := 73)
    (pick := true) (b := 183) Flow.code_178 h (by decide +kernel) ?_ (by decide)
    (by decide +kernel) (by decide) (by decide)
  simp [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, hp]

theorem run_179_181 {t : TState} (h : At t 179 (startFacts P L g 179)) (hbatch : ctaidY L g < P.b) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 181 (startFacts P L g 181) := by
  have he : eOf L g < 2 ^ 31 := lt_trans (by rw [show eOf L g = ctaidY L g from rfl]; exact hbatch)
    hpre.bLt
  seg_fp h using
    (try wg0_values)
    (try nf_simp)
    (try omega)

theorem run_183_184 {t : TState} (h : At t 183 (startFacts P L g 183)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 184 (startFacts P L g 184) := by
  have h2991 : t.regs 2991 = some (.ptr 64 false (.param (param "0")) 0) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 2991) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  refine ld_start (P := P) (L := L) (g := g) (mem0 := mem0) hpre (pc := 183) (w := 32)
    (off := 120) (d := 2882) (ty := .int .b 32)
    Flow.code_183 (supplied_int (off := 120) (x := P.extra_topk) hpre.paramExtraTopk (by decide))
    (by decide) ⟨by decide, by decide, by decide⟩ h ?_ (by decide +kernel)
    (by decide +kernel) h2991 (by decide) (by decide)
  rw [paramElem_of_ne (by decide)]
  rfl

theorem run_184_189 {t : TState} (h : At t 184 (startFacts P L g 184)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧ At t' 189 (startFacts P L g 189) := by
  have hs := sharedBase_lt hpre
  have htid : tidOf L g < 384 := tid384 hpre
  have h4 : tidOf L g % 128 % 4294967296 * 4 % 4294967296 = 4 * (tidOf L g % 128) := by
    have := Nat.mod_lt (tidOf L g) (by decide : 0 < 128); omega
  have hy : 4 * (tidOf L g % 128) ^^^ 256 < 512 :=
    Nat.xor_lt_two_pow (n := 9) (by have := Nat.mod_lt (tidOf L g) (by decide : 0 < 128); omega)
      (by norm_num)
  seg_fp h using
    (try wg0_values)
    (try (simp only [truncBits_int_1, truncBits_int_2, truncBits_int_63, truncBits_int_26,
      truncBits_int_31, truncBits_int_neg64, truncBits_int_256, sb]))
    (try (simp only [Nat.add_zero]))
    (try (nf_simp [nf_xor]))
    (try (rw [h4]))
    (try (norm_bits [nf_xor]))
    (try norm_bits)
    (try norm_signed [nf_xor])
    (try omega)

theorem run_189_194 {t : TState} (h : At t 189 (startFacts P L g 189)) :
    ∃ t', run kernel asms L g 5 t = some t' ∧ At t' 194 (startFacts P L g 194) := by
  have hp120 : Thread.paramWord L 120 4 = P.extra_topk := paramWord_120 hpre
  have hlee := hpre.extraTopkAdd63Lt
  seg_fp h using
    (try wg0_values)
    (try (simp only [truncBits_int_63, truncBits_int_26, truncBits_int_31,
      truncBits_int_neg64, hp120]))
    (try norm_signed)
    (try (all_goals nf_simp))
    (try (all_goals omega))

theorem run_194_198 {t : TState} (h : At t 194 (startFacts P L g 194)) (hbatch : ctaidY L g < P.b)
    (h0 : P.topkLenBase = none) (h1 : P.extraTopkLenBase = none) :
    ∃ t', run kernel asms L g 4 t = some t' ∧ At t' 198 (startFacts P L g 198) := by
  have hp40 : Thread.paramWord L 40 4 = P.topk := paramWord_40 hpre
  have hp120 : Thread.paramWord L 120 4 = P.extra_topk := paramWord_120 hpre
  have hb : 64 * blocksOf P L g = P.topk + P.extra_topk := blocksOf_mul hpre hbatch h0 h1
  have hle := hpre.topkAdd63Lt
  have hlee := hpre.extraTopkAdd63Lt
  have hge : 64 ≤ P.topk := Nat.le_of_dvd hpre.topkPos (Nat.dvd_of_mod_eq_zero hpre.topkDiv64)
  have hceil : (P.topk + 63) / 64 * 64 = P.topk := by
    have := ceilToMultiple_eq_self (d := 64) (by decide)
      (Nat.dvd_of_mod_eq_zero hpre.topkDiv64)
    simpa [Result.ceilToMultiple] using this
  have hceile : (P.extra_topk + 63) / 64 * 64 = P.extra_topk := by
    have := ceilToMultiple_eq_self (d := 64) (by decide)
      (Nat.dvd_of_mod_eq_zero hpre.extraDiv64)
    simpa [Result.ceilToMultiple] using this
  have hpad := hpre.paddedRange (eOf L g) hbatch
  have ht := hpre.paramTopkLen
  have he := hpre.paramExtraTopkLen
  rw [h0] at ht
  rw [h1] at he
  change Result.origPadded (P.topkLen (eOf L g)) +
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 at hpad
  rw [ht.2 (eOf L g) hbatch, he.2 (eOf L g) hbatch] at hpad
  change max ((P.topk + 64 - 1) / 64 * 64) 64 +
    (P.extra_topk + 64 - 1) / 64 * 64 < 2 ^ 31 at hpad
  simp only [show ∀ n : Nat, n + 64 - 1 = n + 63 from fun _ => by omega,
    hceil, hceile, max_eq_left hge] at hpad
  have hdm : P.topk / 64 * 64 = P.topk :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpre.topkDiv64)
  have hdme : P.extra_topk / 64 * 64 = P.extra_topk :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpre.extraDiv64)
  have hdiv : (P.topk + 63) / 64 = P.topk / 64 := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [hdm]; omega
    · rw [Nat.add_mul, one_mul, hdm]; omega
  have hdive : (P.extra_topk + 63) / 64 = P.extra_topk / 64 := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [hdme]; omega
    · rw [Nat.add_mul, one_mul, hdme]; omega
  have hsmall : P.topk / 4294967296 = 0 := Nat.div_eq_of_lt (by omega)
  have hsmalle : P.extra_topk / 4294967296 = 0 := Nat.div_eq_of_lt (by omega)
  have hmod0 : (P.topk + 63) % 4294967296 = P.topk + 63 := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (P.extra_topk + 63) % 4294967296 = P.extra_topk + 63 := Nat.mod_eq_of_lt (by omega)
  have hmod2 : P.topk % 4294967296 = P.topk := Nat.mod_eq_of_lt (by omega)
  have hmod3 : P.extra_topk % 4294967296 = P.extra_topk := Nat.mod_eq_of_lt (by omega)
  seg_fp h using
    (try wg0_values)
    (try (simp only [truncBits_int_1, truncBits_int_2, truncBits_int_63, truncBits_int_26,
      truncBits_int_31, truncBits_int_neg64, truncBits_int_256, hp40, hp120, sb]))
    (try (rw [hb]))
    (try (simp only [show (IntOp.max false == IntOp.max false) = true from rfl, ite_true]))
    (try (nf_simp [toSigned, PTX.compare, Nat.min_def, reduceLandMask, ← Bool.decide_and,
      ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not, ne_eq,
      hceil, hceile, hdiv, hdive, hsmall, hsmalle, hdm, hdme, hmod0, hmod1, hmod2, hmod3]))
    (try (all_goals (try split_ifs)))
    (try (all_goals nf_simp))
    (try (all_goals omega))

/-- The `cvta.shared.u64` of the staging region's base word: the generic shared pointer the
swizzle's arithmetic works on. -/
theorem run_110_111 (hg : g < L.threads) {t : TState} (h : At t 110 (startFacts P L g 110)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 111 (startFacts P L g 111) := by
  have h3110 : t.regs 3110 = some (b64 L.sharedBase) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3110) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  have hcta : g / L.block < L.grid := ctaLt hpre hg
  have hx : L.sharedBase < 2 ^ 32 := by
    have := sharedBase_lt hpre
    omega
  have hl := readSharedAddress_bits (L := L) (g := g) (t := t) (r := 3110) (cl := false)
    (x := L.sharedBase) h3110 (Or.inr rfl) hg hcta hx
  have hexec : execLocalA asms L g t (.addr (.cvta false (.shared .cta) 64 3111 (.reg 3110))) =
      .ok (PTX.next (setReg t 3111 (shPtr L g L.sharedBase))) := by
    refine (exec_cvtaShared (A := asms) (L := L) (g := g) (w := 64) (toShared := false)
      (cl := false) (t := t) (d := 3111) (a := .reg 3110)
      (loc := ⟨.shared, g / L.block, L.sharedBase⟩) hl (by decide) ?_ (by seg_free_pc)).trans ?_
    · intro b hb
      exact localRule_none_addr t _ b hb
    · rfl
  have hwv : shPtr L g L.sharedBase = startValue P L g 3111 := rfl
  refine ⟨PTX.next (setReg t 3111 (startValue P L g 3111)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_110 rfl h hexec
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 110) (r := 3111) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 111, x ∈ 3111 :: startLive 110)

omit hpre in
/-- The pointer's quadrant offset: the head and warp-half words of the staging row. -/
theorem lor_head (L : Launch) (g : Nat) :
    64 * head L g ||| 8192 * half L g = 64 * head L g + 8192 * half L g := by
  have hh : head L g < 64 := head_lt L g
  rw [Nat.or_comm, show (8192 : Nat) = 2 ^ 13 from by norm_num,
    show 64 * head L g + 2 ^ 13 * half L g = 2 ^ 13 * half L g + 64 * head L g from
      Nat.add_comm _ _]
  exact (Nat.two_pow_add_eq_or_of_lt (show 64 * head L g < 2 ^ 13 by omega)
    (half L g)).symm

/-- The quadrant word `%rd3112`: the two mask words joined and doubled. -/
theorem word3112 (hwg : wgOf L g = 0) :
    (64 * (tidOf L g % 64) % 4294967296 ||| 8192 * (warpOf L g / 2) % 4294967296) %
        4294967296 * 2 % 18446744073709551616 =
      2 * (64 * (tidOf L g % 64) + 8192 * (warpOf L g / 2)) % 18446744073709551616 := by
  have hw4 : warpOf L g < 4 := warpLt hpre hwg
  have hh : tidOf L g % 64 < 64 := Nat.mod_lt _ (by decide)
  have ha : 64 * (tidOf L g % 64) < 4294967296 := by omega
  have hb : 8192 * (warpOf L g / 2) < 4294967296 := by omega
  have hab : 64 * (tidOf L g % 64) + 8192 * (warpOf L g / 2) < 4294967296 := by omega
  have hor : 64 * (tidOf L g % 64) ||| 8192 * (warpOf L g / 2)
      = 64 * (tidOf L g % 64) + 8192 * (warpOf L g / 2) := by
    have h := lor_head L g
    simpa [head, half] using h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hor, Nat.mod_eq_of_lt hab]
  omega

/-- The second segment: the head and warp-half words joined into the quadrant's byte offset,
doubled (`mul.wide.u32`). -/
theorem run_111_113 (hwg : wgOf L g = 0) {t : TState} (h : At t 111 (startFacts P L g 111)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ At t' 113 (startFacts P L g 113) := by
  have ht : tidOf L g < 384 := tid384 hpre
  have h1 : tidOf L g % 4294967296 = tidOf L g := Nat.mod_eq_of_lt (by omega)
  have h2 : tidOf L g * 64 % 4294967296 = tidOf L g * 64 := Nat.mod_eq_of_lt (by omega)
  have h2' : tidOf L g * 128 % 4294967296 = tidOf L g * 128 := Nat.mod_eq_of_lt (by omega)
  have h3 : tidOf L g * 64 / 64 = tidOf L g := Nat.mul_div_cancel _ (by decide)
  have h3' : tidOf L g * 128 / 8192 = tidOf L g / 64 := by
    rw [show (8192 : Nat) = 128 * 64 from by norm_num, ← Nat.div_div_eq_div_mul]
    rw [show tidOf L g * 128 / 128 = tidOf L g from by omega]
  have h5 : (tidOf L g / 64) % 2 = half L g := by
    have hw4 : warpOf L g < 4 := warpLt hpre hwg
    rw [tid_div64 L g]
    unfold half
    omega
  have h3112 := word3112 (P := P) (L := L) (g := g) hpre hwg
  seg_fp h using
    (try wg0_values)
    (try nf_simp)
    (try exact h3112)

omit hpre in
/-- An `Int.ofNat` reduced modulo `2 ^ 64` read back as a `Nat`. -/
theorem intEmod_toNat (x : Nat) :
    (Int.ofNat x % (18446744073709551616 : Int)).toNat = x % 18446744073709551616 := by
  rw [Int.toNat_emod (by simp) (by norm_num)]
  simp

omit hpre in
/-- **The swizzle's last instruction**: the `and`ed row mask xored with the chunk's byte is the
chunk's staged word. -/
theorem stageWord_bits {A : Nat} (hA : A < 2 ^ 32) :
    BitVec.ofNat 64 ((A % 18446744073709551616 / 8 % 18446744073709551616 &&& 112) %
        18446744073709551616) ^^^
      BitVec.ofNat 64 (A % 18446744073709551616)
      = BitVec.ofNat 64 ((A / 8 &&& 112) ^^^ A) := by
  have h1 : A % 18446744073709551616 = A := Nat.mod_eq_of_lt (by omega)
  have h2 : A / 8 % 18446744073709551616 = A / 8 := Nat.mod_eq_of_lt (by omega)
  have h3 : (A / 8 &&& 112) % 18446744073709551616 = A / 8 &&& 112 :=
    Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (n := 64) (by decide))
  rw [h1, h2, h3, nf_xor, h1, h3]

/-- The pointer `%rd3114`: the staging region's base plus the thread's quadrant. -/
theorem run_111_114 {t : TState} (h : At t 113 (startFacts P L g 113)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 114 (startFacts P L g 114) := by
  have h3111 : t.regs 3111 = some (shPtr L g L.sharedBase) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3111) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have h3112 : t.regs 3112 = some (b64 (quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3112) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some] using this
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g < 2 ^ 32 := by
    have hs := sharedBase_lt hpre
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3113], [.reg 3111, .reg 3112]⟩) =
      .ok (PTX.next (setReg t 3113 (shPtr L g (L.sharedBase + quadOff L g)))) := by
    have he := exec_add_sharedPtr_reg (A := asms) (L := L) (g := g) (w := 64) (wq := 64)
      (t := t) (d := 3113) (r := 3111) (q := 3112) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase) (k := quadOff L g) (b := L.sharedBase + quadOff L g) (ik := .s)
      h3111 h3112 (Or.inr rfl) hb hq rfl (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3113], [.reg 3111, .reg 3112]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g)) = shPtr L g (L.sharedBase + quadOff L g) :=
      rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g) = startValue P L g 3113 := rfl
  refine ⟨PTX.next (setReg t 3113 (startValue P L g 3113)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_113 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 113) (r := 3113) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 114, x ∈ 3113 :: startLive 113)

/-- The second pointer move: `%rd3114` is the staging base plus the region's base `65536`. -/
theorem run_114_115 {t : TState} (h : At t 114 (startFacts P L g 114)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 115 (startFacts P L g 115) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65536 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3114], [.reg 3113, .imm 65536]⟩) =
      .ok (PTX.next (setReg t 3114 (shPtr L g (L.sharedBase + quadOff L g + 65536)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3114) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65536) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3114], [.reg 3113, .imm 65536]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65536)) =
        shPtr L g (L.sharedBase + quadOff L g + 65536) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65536) = startValue P L g 3114 := rfl
  refine ⟨PTX.next (setReg t 3114 (startValue P L g 3114)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_114 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 114) (r := 3114) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 115, x ∈ 3114 :: startLive 114)

omit hpre in
/-- **The swizzle's last instruction without the pointer's own modulo**: the second operand's
number is the offset itself. -/
theorem stageWord_bits' {A : Nat} (hA : A < 2 ^ 32) :
    BitVec.ofNat 64 ((A / 8 % 18446744073709551616 &&& 112) % 18446744073709551616) ^^^
      BitVec.ofNat 64 A
      = BitVec.ofNat 64 ((A / 8 &&& 112) ^^^ A) := by
  have h2 : A / 8 % 18446744073709551616 = A / 8 := Nat.mod_eq_of_lt (by omega)
  have h3 : (A / 8 &&& 112) % 18446744073709551616 = A / 8 &&& 112 :=
    Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ (n := 64) (by decide))
  rw [h2, h3, nf_xor]
  rw [show A % 18446744073709551616 = A from Nat.mod_eq_of_lt (by omega), h3]

/-- The pointer `%rd3117`: the staging base plus the chunk `1` offset `65552`. -/
theorem run_add3117 {t : TState} (h : At t 118 (startFacts P L g 118)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 119 (startFacts P L g 119) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65552 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3117], [.reg 3113, .imm 65552]⟩) =
      .ok (PTX.next (setReg t 3117 (shPtr L g (L.sharedBase + quadOff L g + 65552)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3117) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65552) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3117], [.reg 3113, .imm 65552]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65552)) =
        shPtr L g (L.sharedBase + quadOff L g + 65552) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65552) = startValue P L g 3117 := rfl
  refine ⟨PTX.next (setReg t 3117 (startValue P L g 3117)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_118 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 118) (r := 3117) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 119, x ∈ 3117 :: startLive 118)

/-- The pointer `%rd3120`: the staging base plus the chunk `2` offset `65568`. -/
theorem run_add3120 {t : TState} (h : At t 122 (startFacts P L g 122)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 123 (startFacts P L g 123) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65568 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3120], [.reg 3113, .imm 65568]⟩) =
      .ok (PTX.next (setReg t 3120 (shPtr L g (L.sharedBase + quadOff L g + 65568)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3120) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65568) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3120], [.reg 3113, .imm 65568]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65568)) =
        shPtr L g (L.sharedBase + quadOff L g + 65568) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65568) = startValue P L g 3120 := rfl
  refine ⟨PTX.next (setReg t 3120 (startValue P L g 3120)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_122 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 122) (r := 3120) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 123, x ∈ 3120 :: startLive 122)

/-- The pointer `%rd3123`: the staging base plus the chunk `3` offset `65584`. -/
theorem run_add3123 {t : TState} (h : At t 126 (startFacts P L g 126)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 127 (startFacts P L g 127) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65584 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3123], [.reg 3113, .imm 65584]⟩) =
      .ok (PTX.next (setReg t 3123 (shPtr L g (L.sharedBase + quadOff L g + 65584)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3123) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65584) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3123], [.reg 3113, .imm 65584]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65584)) =
        shPtr L g (L.sharedBase + quadOff L g + 65584) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65584) = startValue P L g 3123 := rfl
  refine ⟨PTX.next (setReg t 3123 (startValue P L g 3123)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_126 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 126) (r := 3123) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 127, x ∈ 3123 :: startLive 126)

/-- The pointer `%rd3126`: the staging base plus the chunk `4` offset `65600`. -/
theorem run_add3126 {t : TState} (h : At t 130 (startFacts P L g 130)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 131 (startFacts P L g 131) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65600 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3126], [.reg 3113, .imm 65600]⟩) =
      .ok (PTX.next (setReg t 3126 (shPtr L g (L.sharedBase + quadOff L g + 65600)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3126) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65600) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3126], [.reg 3113, .imm 65600]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65600)) =
        shPtr L g (L.sharedBase + quadOff L g + 65600) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65600) = startValue P L g 3126 := rfl
  refine ⟨PTX.next (setReg t 3126 (startValue P L g 3126)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_130 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 130) (r := 3126) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 131, x ∈ 3126 :: startLive 130)

/-- The pointer `%rd3129`: the staging base plus the chunk `5` offset `65616`. -/
theorem run_add3129 {t : TState} (h : At t 134 (startFacts P L g 134)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 135 (startFacts P L g 135) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65616 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3129], [.reg 3113, .imm 65616]⟩) =
      .ok (PTX.next (setReg t 3129 (shPtr L g (L.sharedBase + quadOff L g + 65616)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3129) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65616) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3129], [.reg 3113, .imm 65616]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65616)) =
        shPtr L g (L.sharedBase + quadOff L g + 65616) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65616) = startValue P L g 3129 := rfl
  refine ⟨PTX.next (setReg t 3129 (startValue P L g 3129)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_134 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 134) (r := 3129) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 135, x ∈ 3129 :: startLive 134)

/-- The pointer `%rd3132`: the staging base plus the chunk `6` offset `65632`. -/
theorem run_add3132 {t : TState} (h : At t 138 (startFacts P L g 138)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 139 (startFacts P L g 139) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65632 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3132], [.reg 3113, .imm 65632]⟩) =
      .ok (PTX.next (setReg t 3132 (shPtr L g (L.sharedBase + quadOff L g + 65632)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3132) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65632) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3132], [.reg 3113, .imm 65632]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65632)) =
        shPtr L g (L.sharedBase + quadOff L g + 65632) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65632) = startValue P L g 3132 := rfl
  refine ⟨PTX.next (setReg t 3132 (startValue P L g 3132)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_138 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 138) (r := 3132) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 139, x ∈ 3132 :: startLive 138)

/-- The pointer `%rd3135`: the staging base plus the chunk `7` offset `65648`. -/
theorem run_add3135 {t : TState} (h : At t 142 (startFacts P L g 142)) :
    ∃ t', run kernel asms L g 1 t = some t' ∧ At t' 143 (startFacts P L g 143) := by
  have h3113 : t.regs 3113 = some (shPtr L g (L.sharedBase + quadOff L g)) := by
    have := start_fact (P := P) (L := L) (g := g) h (r := 3113) (by decide +kernel)
    simpa [startValue, valueOf, table, PTX.Flow.lookupLit, Option.getD_some, shPtr] using this
  have hs := sharedBase_lt hpre
  have hh : head L g < 64 := head_lt L g
  have hw6 : half L g < 6 := by
    unfold half
    have := warpOf_lt (g := g) hpre
    omega
  have hq : quadOff L g < 2 ^ 31 := by
    unfold quadOff
    omega
  have hb : L.sharedBase + quadOff L g + 65648 < 2 ^ 32 := by
    unfold quadOff
    omega
  have hstep : execLocalA asms L g t
      (.int ⟨.add, .int .s 64, false, [some 3135], [.reg 3113, .imm 65648]⟩) =
      .ok (PTX.next (setReg t 3135 (shPtr L g (L.sharedBase + quadOff L g + 65648)))) := by
    have he := exec_add_sharedPtr (A := asms) (L := L) (g := g) (w := 64) (gen := true)
      (t := t) (d := 3135) (r := 3113) (i := g / L.block) (c := g / L.block)
      (a := L.sharedBase + quadOff L g) (k := 65648) (ik := .s)
      h3113 (Or.inr rfl) hb (by omega) (by decide)
      (fun a ha => by
        refine Thread.asms_localRule_int (t := t)
          (i := ⟨.add, .int .s 64, false, [some 3135], [.reg 3113, .imm 65648]⟩)
          (by rw [h.1]; decide) (by rw [h.1]; decide) (by rw [h.1]; decide) rfl a ha)
      (by seg_free_pc)
    have hv : Value.ptr 64 true (PtrTarget.shared (g / L.block) (g / L.block))
        (BitVec.ofNat 64 (L.sharedBase + quadOff L g + 65648)) =
        shPtr L g (L.sharedBase + quadOff L g + 65648) := rfl
    simpa [hv] using he
  have hwv : shPtr L g (L.sharedBase + quadOff L g + 65648) = startValue P L g 3135 := rfl
  refine ⟨PTX.next (setReg t 3135 (startValue P L g 3135)), ?_, ?_⟩
  · rw [← hwv]
    exact run_local (K := kernel) Flow.code_142 rfl h hstep
  · exact at_next_set (P := P) (L := L) (g := g) (pc := 142) (r := 3135) h
      (by decide +kernel)
      (by decide +kernel : ∀ x ∈ startLive 143, x ∈ 3135 :: startLive 142)

/-- The swizzle chunk `0` (pcs 115-118): the row mask and the xor. -/
theorem run_swz0 {t : TState} (h : At t 115 (startFacts P L g 115)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 118 (startFacts P L g 118) := by
  have hsp : stagePtr L g 0 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))

/-- The swizzle chunk `1` (pcs 119-122): the row mask and the xor. -/
theorem run_swz1 {t : TState} (h : At t 119 (startFacts P L g 119)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 122 (startFacts P L g 122) := by
  have hsp : stagePtr L g 1 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Int.toNat_natCast, Value.ptr.injEq,
      true_and]; norm_bits))

/-- The swizzle chunk `2` (pcs 123-126): the row mask and the xor. -/
theorem run_swz2 {t : TState} (h : At t 123 (startFacts P L g 123)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 126 (startFacts P L g 126) := by
  have hsp : stagePtr L g 2 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Int.toNat_natCast, Value.ptr.injEq,
      true_and]; norm_bits))

/-- The swizzle chunk `3` (pcs 127-130): the row mask and the xor. -/
theorem run_swz3 {t : TState} (h : At t 127 (startFacts P L g 127)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 130 (startFacts P L g 130) := by
  have hsp : stagePtr L g 3 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Int.toNat_natCast, Value.ptr.injEq,
      true_and]; norm_bits))

/-- The swizzle chunk `4` (pcs 131-134): the row mask and the xor. -/
theorem run_swz4 {t : TState} (h : At t 131 (startFacts P L g 131)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 134 (startFacts P L g 134) := by
  have hsp : stagePtr L g 4 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Int.toNat_natCast, Value.ptr.injEq,
      true_and]; norm_bits))

/-- The swizzle chunk `5` (pcs 135-138): the row mask and the xor. -/
theorem run_swz5 {t : TState} (h : At t 135 (startFacts P L g 135)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 138 (startFacts P L g 138) := by
  have hsp : stagePtr L g 5 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Int.toNat_natCast, Value.ptr.injEq,
      true_and]; norm_bits))

/-- The swizzle chunk `6` (pcs 139-142): the row mask and the xor. -/
theorem run_swz6 {t : TState} (h : At t 139 (startFacts P L g 139)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 142 (startFacts P L g 142) := by
  have hsp : stagePtr L g 6 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  have hword : Value.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 ((stagePtr L g 6 % 18446744073709551616 / 8 %
        18446744073709551616 &&& 112) % 18446744073709551616) ^^^
      BitVec.ofNat 64 (stagePtr L g 6 % 18446744073709551616)) = stageWord L g 6 := by
    simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
    exact stageWord_bits hsp
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try exact hword)

/-- The swizzle chunk `7` (pcs 143-146): the row mask and the xor. -/
theorem run_swz7 {t : TState} (h : At t 143 (startFacts P L g 143)) :
    ∃ t', run kernel asms L g 3 t = some t' ∧ At t' 146 (startFacts P L g 146) := by
  have hsp : stagePtr L g 7 < 2 ^ 32 := stagePtr_lt hpre g (by omega)
  have hword : Value.ptr 64 true (.shared (g / L.block) (g / L.block))
      (BitVec.ofNat 64 ((stagePtr L g 7 % 18446744073709551616 / 8 %
        18446744073709551616 &&& 112) % 18446744073709551616) ^^^
      BitVec.ofNat 64 (stagePtr L g 7 % 18446744073709551616)) = stageWord L g 7 := by
    simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
    exact stageWord_bits hsp
  seg_fp h using
    (try simp only [Assumptions.keepSwizzleTag, Function.update_apply, Nat.reduceEqDiff,
      ite_false, ite_true, override, List.lookup, Nat.reduceBEq, startValue, shPtr])
    (try wg0_values)
    (try dsimp only [shPtr])
    (try nf_simp [intEmod_toNat])
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits hsp))
    (try (simp only [stageWord, stageMask, stagePtr, Value.ptr.injEq, true_and]
          exact stageWord_bits' hsp))
    (try exact hword)
end

theorem valueOf_init_2880 (P : Params) (L : Launch) (g : Nat) :
    valueOf P L g (init P L g) 2880 = sinkReg P L g := by
  simp [valueOf, table, PTX.Flow.lookupLit, Option.getD_some]

theorem sinkReg_eq_negInf (hpre : Pre P L mem0) (h : P.sinkBase = none) :
    sinkReg P L g = negInf := by
  have hb := hpre.paramSink
  rw [h] at hb
  exact sinkReg_none (hb.2 (head L g) (head_lt L g))

theorem AtD_init {t : TState} {pc : Nat}
    (hpc : (init P L g).site.pc = pc) (h : At t pc (startFacts P L g pc))
    (hsink : 2880 ∈ (Flow.live pc).filter (fun r => tracked.contains r) →
      valueOf P L g (init P L g) 2880 = negInf)
    (hsub : ∀ r ∈ (Flow.live pc).filter (fun r => tracked.contains r), r ∈ startLive pc) :
    (code P L g).AtD (init P L g) t := by
  have hfacts : facts P L g (init P L g) =
      factsFrom ((Flow.live pc).filter (fun r => tracked.contains r))
        (valueOf P L g (init P L g)) := by
    simp [facts, hpc]
  refine ⟨h.1.trans hpc.symm, h.2.1, ?_, h.2.2.2.1, ?_⟩
  · exact h.2.2.1.trans (siteAcc_nil (init P L g) rfl).symm
  change Holds t.regs (facts P L g (init P L g))
  rw [hfacts]
  refine holds_of_pointwise fun r hr => ?_
  have hv := holds_mem h.2.2.2.2 (mem_factsFrom (hsub r hr))
  show t.regs r = some (valueOf P L g (init P L g) r)
  rw [hv]
  by_cases h2880 : r = 2880
  · subst h2880
    rw [startValue_2880, hsink hr]
  · rw [startValue_of_ne P L g h2880]

theorem start_of_entry (hpre : Pre P L mem0) {t : TState} (hentry : Entry P L g t) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      (code P L g).AtD (init P L g) t' ∧ Inv P L g (init P L g) := by
  have h0 : At t 104 (startFacts P L g 104) := entry_at hentry
  obtain ⟨t1, hr1, h1⟩ := run_104_110 hpre hentry.wg h0
  obtain ⟨t2, hr2, h2⟩ := run_110_111 hpre hentry.threads h1
  obtain ⟨t3, hr3, h3⟩ := run_111_113 hpre hentry.wg h2
  obtain ⟨t4, hr4, h4⟩ := run_111_114 hpre h3
  obtain ⟨t5, hr5, h5⟩ := run_114_115 hpre h4
  obtain ⟨t6, hr6, h6⟩ := run_swz0 hpre h5
  obtain ⟨t7, hr7, h7⟩ := run_add3117 hpre h6
  obtain ⟨t8, hr8, h8⟩ := run_swz1 hpre h7
  obtain ⟨t9, hr9, h9⟩ := run_add3120 hpre h8
  obtain ⟨t10, hr10, h10⟩ := run_swz2 hpre h9
  obtain ⟨t11, hr11, h11⟩ := run_add3123 hpre h10
  obtain ⟨t12, hr12, h12⟩ := run_swz3 hpre h11
  obtain ⟨t13, hr13, h13⟩ := run_add3126 hpre h12
  obtain ⟨t14, hr14, h14⟩ := run_swz4 hpre h13
  obtain ⟨t15, hr15, h15⟩ := run_add3129 hpre h14
  obtain ⟨t16, hr16, h16⟩ := run_swz5 hpre h15
  obtain ⟨t17, hr17, h17⟩ := run_add3132 hpre h16
  obtain ⟨t18, hr18, h18⟩ := run_swz6 hpre h17
  obtain ⟨t19, hr19, h19⟩ := run_add3135 hpre h18
  obtain ⟨t20, hr20, h20⟩ := run_swz7 hpre h19
  obtain ⟨t21, hr21, h21⟩ := run_146_147 hpre h20
  obtain ⟨t22, hr22, h22⟩ := run_147_148 hpre h21
  obtain ⟨t23, hr23, h23⟩ := run_148_149 h22
  have hc0 := run_comp hr1 hr2
  have hc0 := run_comp hc0 hr3
  have hc0 := run_comp hc0 hr4
  have hc0 := run_comp hc0 hr5
  have hc0 := run_comp hc0 hr6
  have hc0 := run_comp hc0 hr7
  have hc0 := run_comp hc0 hr8
  have hc0 := run_comp hc0 hr9
  have hc0 := run_comp hc0 hr10
  have hc0 := run_comp hc0 hr11
  have hc0 := run_comp hc0 hr12
  have hc0 := run_comp hc0 hr13
  have hc0 := run_comp hc0 hr14
  have hc0 := run_comp hc0 hr15
  have hc0 := run_comp hc0 hr16
  have hc0 := run_comp hc0 hr17
  have hc0 := run_comp hc0 hr18
  have hc0 := run_comp hc0 hr19
  have hc0 := run_comp hc0 hr20
  have hc0 := run_comp hc0 hr21
  have hc0 := run_comp hc0 hr22
  have hc0 := run_comp hc0 hr23
  cases hs : P.sinkBase with
  | some x =>
    obtain ⟨u1, hu1, hu1'⟩ := run_149_150 hpre h23 hs
    obtain ⟨u2, hu2, hu2'⟩ := run_150_151 hu1'
    obtain ⟨u3, hu3, hu3'⟩ := run_151_152 hpre hu2'
    obtain ⟨u4, hu4, hu4'⟩ := run_152_153 hu3'
    obtain ⟨u5, hu5, hu5'⟩ := run_153_154 hpre hu4'
    obtain ⟨u6, hu6, hu6'⟩ := run_154_156 hu5'
    have hc := run_comp hc0 hu1
    have hc := run_comp hc hu2
    have hc := run_comp hc hu3
    have hc := run_comp hc hu4
    have hc := run_comp hc hu5
    have hc := run_comp hc hu6
    refine ⟨u6, run_rtg hc, ?_, init_inv g hpre hentry.wg⟩
    refine AtD_init ?_ hu6' ?_ ?_
    · simp [init, firstSite, Site.pc, hs]
    · intro hmem
      exact absurd hmem (by decide +kernel)
    · decide +kernel
  | none =>
    obtain ⟨u1, hu1, hu1'⟩ := run_149_158 hpre h23 hs
    obtain ⟨u2, hu2, hu2'⟩ := run_158_159 hpre hu1'
    obtain ⟨u3, hu3, hu3'⟩ := run_159_160 hu2'
    obtain ⟨u4, hu4, hu4'⟩ := run_160_161 hpre hu3' hentry.batch
    obtain ⟨u5, hu5, hu5'⟩ := run_161_163 hpre hu4'
    obtain ⟨u6, hu6, hu6'⟩ := run_163_164 hpre hu5'
    obtain ⟨u7, hu7, hu7'⟩ := run_164_165 hu6'
    have hc1 := run_comp hc0 hu1
    have hc1 := run_comp hc1 hu2
    have hc1 := run_comp hc1 hu3
    have hc1 := run_comp hc1 hu4
    have hc1 := run_comp hc1 hu5
    have hc1 := run_comp hc1 hu6
    have hc1 := run_comp hc1 hu7
    cases ht : P.topkLenBase with
    | some y =>
      obtain ⟨v1, hv1, hv1'⟩ := run_165_166 hpre hu7' ht
      obtain ⟨v2, hv2, hv2'⟩ := run_166_168 hpre hv1' hentry.batch
      have hc := run_comp hc1 hv1
      have hc := run_comp hc hv2
      refine ⟨v2, run_rtg hc, ?_, init_inv g hpre hentry.wg⟩
      refine AtD_init ?_ hv2' ?_ ?_
      · simp [init, firstSite, afterSink, Site.pc, hs, ht]
      · intro _
        rw [valueOf_init_2880]
        exact sinkReg_eq_negInf hpre hs
      · decide +kernel
    | none =>
      obtain ⟨v1, hv1, hv1'⟩ := run_165_170 hpre hu7' ht
      obtain ⟨v2, hv2, hv2'⟩ := run_170_171 hpre hv1'
      obtain ⟨v3, hv3, hv3'⟩ := run_171_176 hpre hv2'
      obtain ⟨v4, hv4, hv4'⟩ := run_176_177 hpre hv3'
      obtain ⟨v5, hv5, hv5'⟩ := run_177_178 hv4'
      have hc2 := run_comp hc1 hv1
      have hc2 := run_comp hc2 hv2
      have hc2 := run_comp hc2 hv3
      have hc2 := run_comp hc2 hv4
      have hc2 := run_comp hc2 hv5
      cases he : P.extraTopkLenBase with
      | some z =>
        obtain ⟨w1, hw1, hw1'⟩ := run_178_179 hpre hv5' he
        obtain ⟨w2, hw2, hw2'⟩ := run_179_181 hpre hw1' hentry.batch
        have hc := run_comp hc2 hw1
        have hc := run_comp hc hw2
        refine ⟨w2, run_rtg hc, ?_, init_inv g hpre hentry.wg⟩
        refine AtD_init ?_ hw2' ?_ ?_
        · simp [init, firstSite, afterSink, afterLen, Site.pc, hs, ht, he]
        · intro _
          rw [valueOf_init_2880]
          exact sinkReg_eq_negInf hpre hs
        · decide +kernel
      | none =>
        obtain ⟨w1, hw1, hw1'⟩ := run_178_183 hpre hv5' he
        obtain ⟨w2, hw2, hw2'⟩ := run_183_184 hpre hw1'
        obtain ⟨w3, hw3, hw3'⟩ := run_184_189 hpre hw2'
        obtain ⟨w4, hw4, hw4'⟩ := run_189_194 hpre hw3'
        obtain ⟨w5, hw5, hw5'⟩ := run_194_198 hpre hw4' hentry.batch ht he
        have hc := run_comp hc2 hw1
        have hc := run_comp hc hw2
        have hc := run_comp hc hw3
        have hc := run_comp hc hw4
        have hc := run_comp hc hw5
        refine ⟨w5, run_rtg hc, ?_, init_inv g hpre hentry.wg⟩
        refine AtD_init ?_ hw5' ?_ ?_
        · simp [init, firstSite, afterSink, afterLen, Site.pc, hs, ht, he]
        · intro _
          rw [valueOf_init_2880]
          exact sinkReg_eq_negInf hpre hs
        · decide +kernel

theorem truncBits_int_222768 : truncBits 32 (BitVec.ofInt 64 222768) = BitVec.ofNat 64 222768 := by
  decide

theorem run_199_200 (hpre : Pre P L mem0) {d : D} {t : TState}
    (h : At t 199 (factsFrom ((Flow.live 199).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ t', run kernel asms L g 1 t = some t' ∧
      At t' 200 (factsFrom ((Flow.live 200).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
  have hs := sharedBase_lt hpre
  seg_fp h using
    (try wg0_values)
    (try (simp only [truncBits_int_222768]))
    (try (simp only [sb]))
    (try norm_bits)
    (try omega)

/-- **The bulk wait fires and the thread reaches the last-store arrival's object.** -/
theorem step_bulkWait (hpre : Pre P L mem0) (d : D) (hd : d.site = .bulkWait) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hpc : d.site.pc = 198 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      rw [hd] at h
      show d.sub = 0
      simpa [Site.elems] using h
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_198)
    have hev : eventTmpl asms L g t (.bulkWait (.read) 0) = .bulkWait .read 0 (PTX.next t) :=
      rfl
    rw [hev] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' : u = PTX.next t := Option.some.inj hu
    subst hu'
    set d' : D := { d with site := .lastStore } with hd'def
    have hstep : next P L g d e = some (some d') := by
      rw [he]
      simp [next, nextSite, hd, hd'def]
    rw [hstep]
    have hF : Holds t.regs (factsFrom ((Flow.live 198).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
      simpa [code, facts, hd, Site.pc] using hat.2.2.2.2
    have h199 : At (PTX.next t) 199
        (factsFrom ((Flow.live 199).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show t.pc + 1 = 199
        have h1 : t.pc = d.site.pc := hat.1
        rw [h1, hpc]
      · show t.sub = 0
        rw [show t.sub = d.sub from hat.2.1, hsub]
      · show t.acc = []
        exact hat.2.2.1.trans (siteAcc_nil d hsub)
      · show t.fault = none
        exact hat.2.2.2.1
      · exact holds_factsFrom_mono hF (by decide +kernel)
    obtain ⟨t', hr, ht⟩ := run_199_200 hpre h199
    refine Or.inl (Or.inr ⟨d', t', rfl, run_rtg hr, ⟨?_, ?_⟩⟩)
    · refine ⟨ht.1, ?_, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
      show t'.sub = d'.sub
      rw [show d'.sub = 0 from hsub]
      exact ht.2.1
    · have h := inv_setSite hinv .lastStore (by intro h; exact absurd h (by decide))
        (by intro h; exact absurd h (by decide))
        (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
        (by intro h; exact absurd h (by decide))
        (by intro _; exact hinv.preloop (Or.inl hd))
      simpa [code, hsub, hd'def] using h

/-- The padded token count is positive and fits the signed comparison at softmax entry. -/
theorem blocksOf_word_bounds (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) :
    64 ≤ 64 * blocksOf P L g ∧ 64 * blocksOf P L g < 2 ^ 31 := by
  have hpad := hpre.paddedRange (eOf L g) hbatch
  have hpos := blocksOf_pos P L g
  refine ⟨by omega, ?_⟩
  change Result.origPadded (P.topkLen (eOf L g)) +
    Result.ceilToMultiple (P.extraTopkLen (eOf L g)) 64 < 2 ^ 31 at hpad
  unfold blocksOf Result.blocks Result.totalBlocks Result.topkBlock
  rw [Nat.mul_comm]
  exact (Nat.div_mul_le_self _ _).trans_lt hpad

/-- The last-store arrival starts the first block's initialization. The short-row branch is
unreachable since the main sparse list always contributes at least one padded block. -/
theorem lastStore_prefix (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (d : D) (hd : d.site = .lastStore) {t u : TState} {e : Event} {ins : Instr}
    (hat : (code P L g).AtD d t) (hinv : Inv P L g d) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ m bytes count rel scope, e.kind = .arrive m bytes count rel scope ∧
      ∃ t', run kernel asms L g 7 u = some t' ∧
        At t' 208 (factsFrom ((Flow.live 208).filter (fun r => tracked.contains r))
          (valueOf P L g d)) := by
  have hpc : d.site.pc = 200 := by rw [hd]; rfl
  have hsub : d.sub = 0 := by
    have h := hinv.subLt
    rw [hd] at h
    simpa [Site.elems] using h
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_200)
  have hreg : t.regs 938 = some (b32 (L.sharedBase + 222768)) :=
    reg_value hat (by rw [hd]; decide +kernel)
  have hlt := sharedBase_lt hpre
  have hsb := hpre.sharedAlignment
  rw [← hpre.sharedBase] at hsb
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 938) hreg
    (by omega) (by omega)
  have hb : readBits L g t 32 (.imm 0) = .ok (BitVec.ofNat 64 0) := by rfl
  have hn : readBits L g t 32 (.imm 1) = .ok (BitVec.ofNat 64 1) := by rfl
  obtain ⟨rel, scope, he, hu⟩ := fires_arrive_next (A := asms) (L := L) (g := g) (t := t)
    (base := 938) (off := 0) (tx := .imm 0) (count := .imm 1) (cluster := false)
    (rel := true) (sc := .cta) (pc := 200) hm hb hn hf
  have hstart : At u 201
      (factsFrom ((Flow.live 200).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
    rw [Option.some.inj hu]
    refine ⟨?_, hat.2.1.trans hsub, hat.2.2.1.trans (siteAcc_nil d hsub), hat.2.2.2.1, ?_⟩
    · change t.pc + 1 = 201
      rw [show t.pc = d.site.pc from hat.1, hpc]
    · simpa only [code, facts, hd, Site.pc, PTX.next] using hat.2.2.2.2
  obtain ⟨hb0, hb31⟩ := blocksOf_word_bounds hpre hbatch
  obtain ⟨v, hv, hvat⟩ : ∃ v, run kernel asms L g 1 u = some v ∧ At v 202
      ((74, .pred false) :: factsFrom ((Flow.live 200).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp hstart using
      (try wg0_values)
      (try norm_signed)
      (try omega)
  obtain ⟨v', hv', hv'at⟩ : ∃ v', run kernel asms L g 6 v = some v' ∧
      At v' 208 (factsFrom ((Flow.live 208).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp hvat using
      (try wg0_values)
      (try rfl)
  exact ⟨_, _, _, rel, scope, congrArg Event.kind he, v', run_comp hv hv', hv'at⟩

/-- The low half of the packed scale word survives and feeds the following duplicated pack. -/
theorem run_208_211 {t : TState} (d : D)
    (h : At t 208 (factsFrom ((Flow.live 208).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u 211
      (factsFrom ((Flow.live 211).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hr := holds_mem h.2.2.2.2
    (mem_factsFrom (r := 467) (by decide +kernel))
  change t.regs 467 = some (b32 (paramWord L 28 4)) at hr
  let v := b32 (paramWord L 28 4)
  let packed := joinValue v (.bits 32 0)
  have he := Audit.deadPack_uses_low (L := L) (g := g)
    (by rw [h.1]; rfl : Assumptions.deadPackWords t.pc = some (3144, 467, 950)) hr rfl
  have hx : execLocalA asms L g t
      (.move ⟨.pack, .int .b 64, [some 3144], [.reg 467, .reg 950]⟩) =
      .ok (PTX.next (setReg t 3144 packed)) := by
    rw [Assumption.SegFreePc.exec (by seg_free_pc) h.1]
    simp [execLocalRule, List.findSome?_cons, asms, Assumptions.all,
      Assumptions.idealArith, Assumptions.approx, Assumptions.ncReadOnly, Assumptions.storeDrain,
      Assumption.idealReal, Assumption.approxExact, Assumption.ncReadOnly,
      Assumptions.mulBf16x2, Assumptions.cvtBf16x2, Assumptions.cvtUe8m0, Assumptions.lg2Exact,
      Assumptions.paramPointers, paramAdds, prefetchTensorMapSites, Assumptions.sharedBits,
      Assumptions.sharedBitsSites, h.1,
      Assumption.FloatForm.ofOp, Assumption.ApproxForm.ofOp, he, packed, v]
  have hs := run_local (K := kernel) Flow.code_208 rfl h hx
  have hat := h.set (r := 3144) (v := packed) (by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
    exact fun hr' => (by decide +kernel : 3144 ∉ (Flow.live 208).filter
      (fun r => tracked.contains r)) (hr' ▸ hr))
  have hv : paramWord L 28 4 < 2 ^ 32 := Thread.paramNat_lt L (param "0") 28 4
  let t₁ := PTX.next (setReg t 3144 packed)
  have hpc₁ : t₁.pc = 209 := hat.1
  have hu₁ : execLocalA asms L g t₁
      (.move ⟨.unpack, .int .b 64, [some 951, none], [.reg 3144]⟩) =
      .ok (PTX.next (setReg t₁ 951 v)) := by
    rw [Assumption.SegFreePc.exec (by seg_free_pc) hpc₁, execLocalRule_of_none
      (Thread.asms_localRule_move (by rw [hpc₁]; decide) (by rw [hpc₁]; decide)
        (by rw [hpc₁]; decide))]
    rw [execLocal_move (by rfl)]
    simp [execMove, readValue, readReg, t₁, PTX.next, setReg, setDst, packed, v, b32, joinValue,
      splitValue, Value.bytes, DType.width, truncBits_ofNat hv (by decide), bind, Except.bind,
      pure, Except.pure]
  have hm := run_local (K := kernel) Flow.code_209 rfl hat hu₁
  have hat₂ := hat.set (r := 951) (v := v) (by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (by decide : 3144 ≠ 951)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      exact fun hr' => (by decide +kernel : 951 ∉ (Flow.live 208).filter
        (fun r => tracked.contains r)) (hr' ▸ hr))
  obtain ⟨u, hu, hau⟩ : ∃ u, run kernel asms L g 1 (PTX.next (setReg t₁ 951 v)) = some u ∧
      At u 211 (factsFrom ((Flow.live 211).filter (fun r => tracked.contains r))
        (valueOf P L g d)) := by
    seg_fp hat₂ using rfl
  exact ⟨u, run_comp (run_comp hs hm) hu, hau⟩

/-- Compute the first block's shared P destination from the warp half and lane. -/
theorem run_211_222 (hpre : Pre P L mem0) (hwg : wgOf L g = 0) {t : TState} (d : D)
    (h : At t 211 (factsFrom ((Flow.live 211).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 11 t = some u ∧ At u 222
      ((956, b32 (16 * laneOf L g)) ::
        factsFrom ((Flow.live 222).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hw := warpLt hpre hwg
  have hl := laneLt L g
  have hs := sharedBase_lt hpre
  have hlo : 16 * laneOf L g < 512 := by omega
  have hl32 : laneOf L g < 4294967296 := by omega
  have hlo32 : 16 * laneOf L g < 4294967296 := by omega
  have hlo1024 : 16 * laneOf L g + 512 < 4294967296 := by omega
  have hlo64 : 16 * laneOf L g < 18446744073709551616 := by omega
  have hlo1024wide : 16 * laneOf L g + 512 < 18446744073709551616 := by omega
  have hor512 : (16 * laneOf L g) ||| 512 = 16 * laneOf L g + 512 :=
    Nat.or_two_pow_eq_add_of_lt (n := 9) hlo
  have hor4096 : (4096 : Nat) ||| (16 * laneOf L g) = 4096 + 16 * laneOf L g :=
    lor_4096 (by decide) (by omega)
  have hor4608 : (4096 : Nat) ||| (16 * laneOf L g + 512) = 4096 + (16 * laneOf L g + 512) :=
    lor_4096 (by decide) (by omega)
  seg_fp h using
    (try wg0_values)
    (first
      | rfl
      | norm_bits [sb]
      | (interval_cases hwarp : warpOf L g <;>
          norm_bits [sb, half, hwarp, hor512, hor4096, hor4608, Nat.or_zero, Nat.zero_or,
            Nat.reduceAnd, Nat.mul_comm (laneOf L g) 16, Nat.mod_eq_of_lt hl32,
            Nat.mod_eq_of_lt hlo32, Nat.mod_eq_of_lt hlo1024, Nat.mod_eq_of_lt hlo64,
            Nat.mod_eq_of_lt hlo1024wide]))

/-- Compute the peer exchange and own output addresses for the first block. -/
theorem run_222_236 (hpre : Pre P L mem0) (hwg : wgOf L g = 0) {t : TState} (d : D)
    (h : At t 222 ((956, b32 (16 * laneOf L g)) ::
      factsFrom ((Flow.live 222).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 14 t = some u ∧ At u 236
      (factsFrom ((Flow.live 236).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hw := warpLt hpre hwg
  have hl := laneLt L g
  have hs := sharedBase_lt hpre
  have hxor : (warpOf L g * 4096) ^^^ 8192 = 4096 * (warpOf L g ^^^ 2) := by
    interval_cases hwarp : warpOf L g <;> decide
  have hx32 : warpOf L g * 4096 < 4294967296 := by omega
  have hx64 : warpOf L g * 4096 < 18446744073709551616 := by omega
  have hw32 : warpOf L g < 4294967296 := by omega
  have hp : warpOf L g ^^^ 2 < 4 := Nat.xor_lt_two_pow (n := 2) hw (by decide)
  obtain ⟨v, hv, hat⟩ : ∃ v, run kernel asms L g 4 t = some v ∧ At v 226
      ((965, sb L (exchangeQuad * (warpOf L g ^^^ 2) + 16 * laneOf L g)) ::
        (962, b32 (4096 * warpOf L g)) :: (956, b32 (16 * laneOf L g)) ::
        factsFrom ((Flow.live 226).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
    seg_fp h using
      (try wg0_values)
      (norm_bits [sb, exchangeQuad, nf_xor, Nat.mod_eq_of_lt hw32,
        Nat.mod_eq_of_lt hx32, Nat.mod_eq_of_lt hx64, hxor])
  obtain ⟨u, hu, hau⟩ : ∃ u, run kernel asms L g 10 v = some u ∧ At u 236
      (factsFrom ((Flow.live 236).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
    seg_fp hat using
      (try wg0_values)
      (norm_bits [sb, exchangeBase, exchangeQuad, exchangeChunk])
  exact ⟨u, run_comp hv hu, hau⟩

/-- Set the 32-bit remaining-block counter before entering the loop. -/
theorem run_236_241 (hpre : Pre P L mem0) (hbatch : eOf L g < P.b) {t : TState} (d : D)
    (hblock : d.block = 0)
    (h : At t 236 (factsFrom ((Flow.live 236).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 5 t = some u ∧ At u 241
      (factsFrom ((Flow.live 241).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  obtain ⟨hpos, hlim⟩ := blocksOf_word_bounds hpre hbatch
  have hp : 0 < blocksOf P L g := by omega
  have hb31 : blocksOf P L g < 2 ^ 31 := by omega
  seg_fp h using
    (wg0_values)
    (simp only [hblock, Nat.zero_add, truncBits_int_1, truncBits_int_26, truncBits_int_31])
    (norm_signed)

/-- Form the pair-barrier id and the mask-half selector before the opening group barrier. -/
theorem run_241_244 (hpre : Pre P L mem0) (hwg : wgOf L g = 0) {t : TState} (d : D)
    (h : At t 241 (factsFrom ((Flow.live 241).filter (fun r => tracked.contains r))
      (valueOf P L g d))) :
    ∃ u, run kernel asms L g 3 t = some u ∧ At u 244
      ((75, .pred (decide (2 ≤ warpOf L g))) ::
        factsFrom ((Flow.live 244).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have hw := warpLt hpre hwg
  seg_fp h using
    (try wg0_values)
    (interval_cases hw' : warpOf L g <;> decide)

/-- Set the first block's ring positions, accumulator words and barrier operands. -/
theorem run_244_256 {t : TState} (d : D) (hw : warpOf L g < 4)
    (hblock : d.block = 0) (hpeak : d.peak = ⊥) (hmi : d.miUpd = false)
    (hsum : d.sumUpd = false)
    (h : At t 244 ((75, .pred (decide (2 ≤ warpOf L g))) ::
      factsFrom ((Flow.live 244).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 12 t = some u ∧ At u 256
      (factsFrom ((Flow.live 256).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  by_cases har : 2 ≤ warpOf L g <;>
    simp only [har, decide_true, decide_false] at h <;>
    seg_fp h using
      (try wg0_values)
      (first
        | rfl
        | (simp only [hblock, hpeak, hmi, hsum, halfSumVal, peakVal, miVal, negInf, negMax,
            Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.zero_div, Nat.zero_mod] <;> rfl)
        | (interval_cases hw' : warpOf L g <;> decide)
        | norm_signed [half, har])

/-- The preceding row's store arrival leads to the first softmax barrier. -/
theorem step_lastStore (hpre : Pre P L mem0) (hbatch : eOf L g < P.b)
    (d : D) (hd : d.site = .lastStore) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    obtain ⟨m, tx, count, rel, scope, he, t₁, hr₁, hat₁⟩ :=
      lastStore_prefix hpre hbatch d hd hat hinv hc hf
    obtain ⟨t₂, hr₂, hat₂⟩ := run_208_211 d hat₁
    obtain ⟨t₃, hr₃, hat₃⟩ := run_211_222 hpre hinv.wg d hat₂
    obtain ⟨t₄, hr₄, hat₄⟩ := run_222_236 hpre hinv.wg d hat₃
    obtain ⟨hblock, hpeak, _, hmi, hsum⟩ := hinv.preloop (Or.inr hd)
    obtain ⟨t₅, hr₅, hat₅⟩ := run_236_241 hpre hbatch d hblock hat₄
    obtain ⟨t₆, hr₆, hat₆⟩ := run_241_244 hpre hinv.wg d hat₅
    obtain ⟨t₇, hr₇, hat₇⟩ := run_244_256 d hinv.warpLt hblock hpeak hmi hsum hat₆
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      simpa [hd, Site.elems] using h
    let d' : D := { d with site := .wg0Sync }
    have hn : next P L g d e = some (some d') := by
      simp [next, nextSite, hd, he, d']
    refine Or.inl (Or.inr ⟨d', t₇, hn, ?_, ?_, ?_⟩)
    · exact (run_rtg (run_comp (run_comp (run_comp (run_comp (run_comp
        (run_comp hr₁ hr₂) hr₃) hr₄) hr₅) hr₆) hr₇))
    · exact ⟨hat₇.1, hat₇.2.1.trans hsub.symm, hat₇.2.2.1, hat₇.2.2.2.1, hat₇.2.2.2.2⟩
    · have hi := inv_setSite hinv .wg0Sync (by intro h; exact absurd h (by decide))
        (by intro h; exact absurd h (by decide))
        (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
        (by intro h; exact absurd h (by decide))
        (by rintro (h | h) <;> exact absurd h (by decide))
      simpa [code, d', hsub] using hi

theorem run_276_278 {t : TState} (d : D)
    (h : At t 276 ((76, .pred false) ::
      factsFrom ((Flow.live 275).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 2 t = some u ∧ At u 278
      (factsFrom ((Flow.live 278).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  seg_fp h using rfl

theorem run_276_283 {t : TState} (d : D)
    (h : At t 276 ((76, .pred true) ::
      factsFrom ((Flow.live 275).filter (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 2 t = some u ∧ At u 283
      (factsFrom ((Flow.live 283).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  seg_fp h using rfl

/-- The emitted score loads have defined Tensor Memory read templates. -/
theorem scoreLoad_template {base addr : Nat} {ds : List Nat} {t : TState}
    {mem0 : Mem0} (hpre : Pre P L mem0)
    (haddr : addr = 400 ∨ addr = 432) (hcount : ds.length = 32)
    (hr : t.regs base = some (b32 addr)) :
    eventTmpl asms L g t (.tcLd ds base .s32x32b none) =
      .tcLd addr ds.length .s32x32b (fun words => setRegs (PTX.next t) ds words) := by
  have hblock : L.block % 32 = 0 := by rw [hpre.block]
  have hsize : TcShape.countOk .s32x32b ds.length := by rw [hcount]; decide
  have hread := readBits_b32 (L := L) (g := g) (t := t) (r := base) (a := addr) hr (by omega)
  have hdata : tcDataAddressOk L g .s32x32b addr = true := by
    rcases haddr with rfl | rfl <;> rfl
  have hnat : (BitVec.ofNat 64 addr).toNat = addr := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]; omega
  have hplain : ∀ s, TcShape.s32x32b ≠ .packed16 s := by
    intro s hs
    cases hs
  have hwait : asms.any (·.tcLdWait t.pc) = false := rfl
  simp only [eventTmpl, tcLdTmpl, hwait, tcTmpl_tcLd_none hplain, hblock, hsize, ↓reduceIte,
    hread, bind, Except.bind, hnat, hdata, Bool.false_eq_true, pure, Except.pure, ofExec]

/-- Decode the two fixed-width score loads as Tensor Memory reads with their returned words. -/
theorem fires_scoreLoad {base addr : Nat} {ds : List Nat} {t u : TState} {e : Event}
    {site : Nat} {mem0 : Mem0} (hpre : Pre P L mem0)
    (haddr : addr = 400 ∨ addr = 432) (hcount : ds.length = 32)
    (hr : t.regs base = some (b32 addr))
    (hf : Fires site (eventTmpl asms L g t (.tcLd ds base .s32x32b none)) e (some u)) :
    ∃ words : List Value, words.length = ds.length ∧ e = ⟨site, .tc (.ld addr words .s32x32b)⟩ ∧
      u = setRegs (PTX.next t) ds words := by
  rw [scoreLoad_template (g := g) hpre haddr hcount hr] at hf
  obtain ⟨words, hwords, he, hu⟩ := hf
  exact ⟨words, hwords, he, Option.some.inj hu⟩

theorem get_scoreDst {own : Bool} {r : Nat} {words : List Value} {t : TState}
    (hlen : words.length = 32) (hr : r ∈ scoreDsts own) :
    (setRegs t (scoreDsts own) words).regs r =
      some (words.getD (r - scoreFirst own) (b32 0)) := by
  obtain ⟨hlo, hhi⟩ := (scoreDst_mem own r).mp hr
  have hi : r - scoreFirst own < words.length := by omega
  apply setRegs_get (p := r - scoreFirst own)
  · exact List.nodup_range'
  · have hindex : r - scoreFirst own < 32 := hi.trans_le hlen.le
    simpa only [scoreDsts, Nat.one_mul, Nat.add_sub_of_le hlo] using
      (List.getElem?_range' (s := scoreFirst own) (step := 1) hindex)
  · rw [List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]

/-- Deliver the 32 returned words, and retain the live registers outside their destination. -/
theorem at_loadScores {d : D} {own : Bool} {words : List Value} {t : TState}
    {p : Nat} {src dst : List Nat} (h : At t p (factsFrom src (valueOf P L g d)))
    (hlen : words.length = 32)
    (hframe : ∀ r ∈ dst, r ∉ scoreDsts own → r ∈ src)
    (hdisj : ∀ r ∈ dst, ¬ (1009 ≤ r ∧ r ≤ 1043) ∧
      ¬ (3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0) ∧ ¬ (4031 ≤ r ∧ r < 4039)) :
    At (setRegs (PTX.next t) (scoreDsts own) words) (p + 1)
      (factsFrom dst (valueOf P L g (loadScores d own words))) := by
  have hs := setRegs_skel (PTX.next t) (scoreDsts own) words
  refine ⟨hs.1.trans (At.next h).1, hs.2.1.trans h.2.1, hs.2.2.1.trans h.2.2.1,
    hs.2.2.2.trans h.2.2.2.1, ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  by_cases hdst : r ∈ scoreDsts own
  · rw [get_scoreDst hlen hdst]
    rw [scoreDst_mem] at hdst
    cases own
    · have hpeer : 2886 ≤ r ∧ r < 2918 := hdst
      have hown : ¬ (2918 ≤ r ∧ r < 2950) := by omega
      simp [valueOf, loadScores, scoreFirst, hpeer, hown]
    · have hown : 2918 ≤ r ∧ r < 2950 := hdst
      simp [valueOf, loadScores, scoreFirst, hown]
  · rw [setRegs_other _ _ _ _ hdst]
    have hbefore := holds_mem h.2.2.2.2 (mem_factsFrom (hframe r hr hdst))
    change t.regs r = _
    rw [hbefore]
    rw [scoreDst_mem] at hdst
    obtain ⟨hm, hp, he⟩ := hdisj r hr
    cases own
    · have hpeer : ¬ (2886 ≤ r ∧ r < 2918) := hdst
      simp only [valueOf, loadScores, Bool.false_eq_true, ↓reduceIte, hpeer, hm, hp, he]
      rfl
    · have hown : ¬ (2918 ≤ r ∧ r < 2950) := hdst
      simp only [valueOf, loadScores, ↓reduceIte, hown, hm, hp, he]
      rfl

/-- A plain Tensor Memory fence keeps the role's facts and advances one instruction. -/
theorem at_next_of {d : D} {t : TState} {site : Nat}
    (hat : (code P L g).AtD d t) (hsite : d.site.pc = site) (hsub : d.sub = 0) :
    At (PTX.next t) (site + 1)
      (factsFrom ((Flow.live site).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
  have h : At t site
      (factsFrom ((Flow.live site).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
    refine ⟨hat.1.trans hsite, hat.2.1.trans hsub, hat.2.2.1.trans (siteAcc_nil d hsub),
      hat.2.2.2.1, ?_⟩
    simpa only [code, facts, hsite] using hat.2.2.2.2
  exact At.next h

/-- Each warp takes the score-load arm matching its position within the warpgroup. -/
theorem step_fenceLoad (d : D) (hd : d.site = .fenceLoad) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 275 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      simpa [hd, Site.elems] using h
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_275)
    change e = ⟨275, .tc .fenceAfter⟩ ∧ some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := { d with site := .scoreLoad ⟨arm L g, armLt L g⟩ 0, sub := 0 }
    have hvSame : valueOf P L g d' = valueOf P L g d := by funext r; rfl
    have hn : next P L g d e = some (some d') := by
      simp [he, next, nextSite, hd, hsub, d']
    have hat' := at_next_of hat hsite hsub
    have hp := holds_mem hat'.2.2.2.2 (mem_factsFrom (r := 76) (by decide +kernel))
    change (PTX.next t).regs 76 = some (.pred (decide (2 ≤ warpOf L g))) at hp
    obtain ⟨v, hr, hv⟩ : ∃ v, run kernel asms L g 2 (PTX.next t) = some v ∧
        (code P L g).AtD d' v := by
      by_cases harm : 2 ≤ warpOf L g
      · have hAt := hat'.mono (show Holds (PTX.next t).regs ((76, .pred true) ::
            factsFrom ((Flow.live 275).filter (fun r => tracked.contains r))
              (valueOf P L g d)) from ⟨by simpa [harm] using hp, hat'.2.2.2.2⟩)
        obtain ⟨v, hr, hv⟩ := run_276_283 d hAt
        have ha : (⟨arm L g, armLt L g⟩ : Fin 2) = 1 := Fin.ext (by simp [arm, harm])
        refine ⟨v, hr, ?_⟩
        refine ⟨?_, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
        · simpa [code, d', ha, Site.pc] using hv.1
        · have hpc' : d'.site.pc = 283 := by
            simp only [d', ha]
            rfl
          simpa only [code, facts, hpc', hvSame] using hv.2.2.2.2
      · have hAt := hat'.mono (show Holds (PTX.next t).regs ((76, .pred false) ::
            factsFrom ((Flow.live 275).filter (fun r => tracked.contains r))
              (valueOf P L g d)) from ⟨by simpa [harm] using hp, hat'.2.2.2.2⟩)
        obtain ⟨v, hr, hv⟩ := run_276_278 d hAt
        have ha : (⟨arm L g, armLt L g⟩ : Fin 2) = 0 := Fin.ext (by simp [arm, harm])
        refine ⟨v, hr, ?_⟩
        refine ⟨?_, hv.2.1, hv.2.2.1, hv.2.2.2.1, ?_⟩
        · simpa [code, d', ha, Site.pc] using hv.1
        · have hpc' : d'.site.pc = 278 := by
            simp only [d', ha]
            rfl
          simpa only [code, facts, hpc', hvSame] using hv.2.2.2.2
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr, hv, ?_⟩)
    exact inv_setSite hinv (.scoreLoad ⟨arm L g, armLt L g⟩ 0)
      (by simp [Site.inEpilogue]) (by simp [Site.inRescale]) (fun _ => ⟨0, rfl⟩)
      (by simp) (by simp)

/-- A finished score wait advances to the fence that orders use of its two loads. -/
theorem step_scoreWait {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .scoreWait) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 286 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      simpa [hd, Site.elems] using h
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_286)
    have hm : eventTmpl asms L g t .tcWaitLd = .tc .waitLd (PTX.next t) := by
      simp [eventTmpl, tcTmpl, hpre.block, ofExec, pure, Except.pure]
    rw [hm] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := { d with site := .fenceBefore }
    have hn : next P L g d e = some (some d') := by
      simp [he, next, nextSite, hd, d']
    have hat' := at_next_of hat hsite hsub
    have hkeep := holds_factsFrom_mono hat'.2.2.2.2
      (by decide +kernel : ∀ r ∈ (Flow.live 287).filter (fun r => tracked.contains r),
        r ∈ (Flow.live 286).filter (fun r => tracked.contains r))
    refine Or.inl (Or.inr ⟨d', PTX.next t, hn, .refl, ?_, ?_⟩)
    · exact ⟨hat'.1, hat'.2.1.trans hsub.symm, hat'.2.2.1, hat'.2.2.2.1, hkeep⟩
    · have hi := inv_setSite hinv .fenceBefore (by intro h; exact absurd h (by decide))
        (by intro h; exact absurd h (by decide))
        (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
        (by intro h; exact absurd h (by decide))
        (by rintro (h | h) <;> exact absurd h (by decide))
      simpa [code, d', hsub] using hi

/-- The score fence precedes the shared mask-word read of this warp half. -/
theorem step_fenceBefore {mem0 : Mem0} (hpre : Pre P L mem0)
    (d : D) (hd : d.site = .fenceBefore) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 287 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      simpa [hd, Site.elems] using h
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_287)
    change e = ⟨287, .tc .fenceBefore⟩ ∧ some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := { d with site := .maskRead }
    have hn : next P L g d e = some (some d') := by
      simp [he, next, nextSite, hd, d']
    have hat' := at_next_of hat hsite hsub
    have hB := sharedBase_lt hpre
    have hhalf := halfLt hinv.warpLt
    have hslot := vslotOf_lt d
    obtain ⟨v, hr, hv⟩ : ∃ v, run kernel asms L g 1 (PTX.next t) = some v ∧ At v 289
        (factsFrom ((Flow.live 289).filter (fun r => tracked.contains r)) (valueOf P L g d)) := by
      seg_fp hat' using
        (try wg0_values)
        (norm_bits [sb, maskStride])
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr, ?_, ?_⟩)
    · exact ⟨hv.1, hv.2.1.trans hsub.symm, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩
    · have hi := inv_setSite hinv .maskRead (by intro h; exact absurd h (by decide))
        (by intro h; exact absurd h (by decide))
        (by rintro ⟨a, k, hk⟩; exact absurd hk (by simp))
        (by intro h; exact absurd h (by decide))
        (by rintro (h | h) <;> exact absurd h (by decide))
      simpa [code, d', hsub] using hi

private def scoreAddressReg (a k : Fin 2) : Nat :=
  ([[986, 987], [984, 985]].getD a.val []).getD k.val 0

private def scoreAddress (k : Fin 2) : Nat := if k.val = 0 then 400 else 432

private theorem after_score_locals (d : D) (a k : Fin 2) {t : TState}
    (h : At t ((Site.scoreLoad a k).pc + 1)
      (factsFrom ((Flow.live ((Site.scoreLoad a k).pc + 1)).filter
        (fun r => tracked.contains r)) (valueOf P L g d))) :
    ∃ n u, run kernel asms L g n t = some u ∧ At u (afterScoreSite a k).pc
      (factsFrom ((Flow.live (afterScoreSite a k).pc).filter
        (fun r => tracked.contains r)) (valueOf P L g d)) := by
  fin_cases a <;> fin_cases k
  · refine ⟨1, ?_⟩
    seg_fp h using rfl
  · refine ⟨1, ?_⟩
    seg_fp h using rfl
  · refine ⟨1, ?_⟩
    seg_fp h using rfl
  · exact ⟨0, t, rfl, h⟩

private theorem inv_loadScores {d : D} (h : Inv P L g d) {a k : Fin 2}
    (hd : d.site = .scoreLoad a k) (own : Bool) (words : List Value) :
    Inv P L g (loadScores d own words) := by
  cases own <;>
    exact ⟨h.wg, h.warpLt, h.laneLt, h.headEq, h.ring, h.blockLt, h.epilogueLast, h.rescaleArm,
      h.subLt, h.armSite, h.exitWarp, h.preloop, h.rowTotal, by simp [loadScores, hd]⟩

/-- Each score-load event writes the 32 returned values into its selected score half. -/
theorem step_scoreLoad (hpre : Pre P L mem0) (d : D) (a k : Fin 2)
    (hd : d.site = .scoreLoad a k) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    obtain ⟨j, hj⟩ := hinv.armSite ⟨a, k, hd⟩
    have ha : a.val = arm L g :=
      congrArg Fin.val (Site.scoreLoad.inj (hd.symm.trans hj)).1
    have hsub : d.sub = 0 := by
      have h := hinv.subLt
      simpa [hd, Site.elems] using h
    let own := a.val == k.val
    have hcode : kernel.code[(Site.scoreLoad a k).pc]? =
        some ⟨none, .tcLd (scoreDsts own) (scoreAddressReg a k) .s32x32b none⟩ := by
      fin_cases a <;> fin_cases k
      · exact Flow.code_278
      · exact Flow.code_280
      · exact Flow.code_283
      · exact Flow.code_285
    have hr : t.regs (scoreAddressReg a k) = some (b32 (scoreAddress k)) := by
      have h := reg_value hat (r := scoreAddressReg a k) (by
        rw [hd]
        fin_cases a <;> fin_cases k <;> decide +kernel)
      rw [h]
      fin_cases a <;> fin_cases k <;> rfl
    rw [hd] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hcode)
    have haddr : scoreAddress k = 400 ∨ scoreAddress k = 432 := by
      fin_cases k <;> decide
    have hlen : (scoreDsts own).length = 32 := by simp [scoreDsts]
    obtain ⟨words, hw, he, hu⟩ := fires_scoreLoad hpre haddr hlen hr hf
    subst u
    let d' : D := { loadScores d own words with site := afterScoreSite a k }
    have hn : next P L g d e = some (some d') := by
      simp [he, next, nextSite, hd, ha, own, d']
    have hat' : At t (Site.scoreLoad a k).pc
        (factsFrom ((Flow.live (Site.scoreLoad a k).pc).filter
          (fun r => tracked.contains r)) (valueOf P L g d)) :=
      ⟨hat.1.trans (congrArg Site.pc hd), hat.2.1.trans hsub,
        hat.2.2.1.trans (siteAcc_nil d hsub), hat.2.2.2.1,
        by simpa only [code, facts, hd] using hat.2.2.2.2⟩
    have hframe : ∀ r ∈ (Flow.live ((Site.scoreLoad a k).pc + 1)).filter
        (fun r => tracked.contains r), r ∉ scoreDsts own →
        r ∈ (Flow.live (Site.scoreLoad a k).pc).filter (fun r => tracked.contains r) := by
      fin_cases a <;> fin_cases k <;> decide +kernel
    have hdisj : ∀ r ∈ (Flow.live ((Site.scoreLoad a k).pc + 1)).filter
        (fun r => tracked.contains r), ¬ (1009 ≤ r ∧ r ≤ 1043) ∧
        ¬ (3145 ≤ r ∧ r ≤ 3173 ∧ (r - 3145) % 4 = 0) ∧ ¬ (4031 ≤ r ∧ r < 4039) := by
      fin_cases a <;> fin_cases k <;> decide +kernel
    have hload := at_loadScores hat' (hw.trans hlen) hframe hdisj
    obtain ⟨n, v, hv, hatv⟩ := after_score_locals (loadScores d own words) a k hload
    have hregval : valueOf P L g d' = valueOf P L g (loadScores d own words) := by
      funext r
      rfl
    have hsub' : (loadScores d own words).sub = 0 := by cases own <;> exact hsub
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hv, ?_, ?_⟩)
    · exact ⟨hatv.1, hatv.2.1.trans hsub'.symm, hatv.2.2.1.trans (siteAcc_nil d' hsub').symm,
        hatv.2.2.2.1, by
        simpa only [code, facts, hregval] using hatv.2.2.2.2⟩
    · have hInv := inv_loadScores hinv hd own words
      have hp : ∀ s, afterScoreSite a k = s →
          Inv P L g { loadScores d own words with site := s, sub := 0 } := by
        intro s hs
        unfold afterScoreSite at hs
        split at hs
        · obtain rfl := hs
          exact inv_setSite hInv _ (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
            (fun _ => ⟨_, by rw [show a = ⟨arm L g, armLt L g⟩ from Fin.ext ha]⟩)
            (by simp) (by simp)
        · obtain rfl := hs
          exact inv_setSite hInv .scoreWait (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
            (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
      simpa [code, d', hsub'] using hp _ rfl

/-- The aligned mask load can only emit a shared read. -/
theorem fired_maskRead (hpre : Pre P L mem0)
    {d : D} {t : TState} {o : Option TState} {e : Event} {ins : Instr}
    (hd : d.site = .maskRead) (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e o) :
    ∃ ac bytes, e.kind = .rd ac bytes ∧
      siteLoc L g d.site d.block d.sub = some ac.loc ∧ ac.size = 4 ∧
      o = some (afterLoad t [1002] bytes) := by
  have hpc : d.site.pc = 289 := by rw [hd]; rfl
  have hsub : t.sub = 0 := by
    have h := hinv.subLt
    rw [show t.sub = d.sub from hat.2.1]
    simpa [hd, Site.elems] using h
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_289)
  let addr := L.sharedBase + (maskStride * (d.block % 4) + 4 * half L g)
  have hr : t.regs 1001 = some (b32 addr) := reg_value hat (by rw [hd]; decide +kernel)
  have hB := sharedBase_lt hpre
  have hhalf := halfLt hinv.warpLt
  have hslot := vslotOf_lt d
  have hlt : addr + 221696 < 2 ^ 32 := by
    simp only [addr, maskStride]
    omega
  have hb : L.sharedBase % 1024 = 0 := by
    rw [hpre.sharedBase]
    exact hpre.sharedAlignment
  have hal : (addr + 221696) % 4 = 0 := by
    simp only [addr, maskStride]
    omega
  have haddr : effAddr L g t .shared 1001 221696 =
      .ok ⟨.shared, g / L.block, addr + 221696⟩ :=
    effAddr_b32_off (off := 221696) hr hlt
  rw [eventTmpl, memTmpl_load (sp := .shared) (base := 1001) (w := 32)
    rfl rfl rfl rfl rfl] at hf
  simp only [MemAccess.regs, DType.width, loadTmpl, haddr, bind, Except.bind,
    Bool.false_eq_true, ↓reduceIte, hsub] at hf
  rw [elemAcc_ok (by decide) (by simpa using hal)] at hf
  obtain ⟨bs, -, he, hu⟩ := hf
  refine ⟨_, bs, congrArg Event.kind he, ?_, rfl, hu⟩
  rw [hd]
  simp only [siteLoc, Loc.at, shLoc, ctaOf, addr, maskBase, Option.some.injEq, Loc.mk.injEq,
    true_and]
  omega

/-- The mask event reads the four-byte word for this ring slot and warp half. -/
theorem fires_maskRead (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .maskRead) (hat : (code P L g).AtD d t) (hinv : Inv P L g d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ ac bytes, e.kind = .rd ac bytes ∧
      siteLoc L g d.site d.block d.sub = some ac.loc ∧ ac.size = 4 ∧
      u = afterLoad t [1002] bytes := by
  obtain ⟨a, bs, he, hl, hs, hu⟩ := fired_maskRead hpre hd hat hinv hc hf
  exact ⟨a, bs, he, hl, hs, Option.some.inj hu⟩

/-- The shared P fence leads to the arrival on the current slot's softmax-ready barrier. -/
theorem step_soFence (hpre : Pre P L mem0) (d : D) (hd : d.site = .soFence) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 1120 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by
      have hs := hinv.subLt
      simpa [hd, Site.elems] using hs
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1120)
    change e = ⟨1120, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      some u = some (PTX.next t) at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst hu'
    let d' : D := { d with site := .soReady }
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, he, hd, d']
    have hat' := at_next_of hat hsite hsub
    have hbase := sharedBase_lt hpre
    have hslot := slotOf_lt d
    obtain ⟨v, hr, hav⟩ : ∃ v, run kernel asms L g 1 (PTX.next t) = some v ∧
        At v 1122 (facts P L g d') := by
      seg_fp hat' using
        (try simp only [d'])
        (try wg0_values)
        (norm_bits [sb])
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr, ?_, ?_⟩)
    · exact ⟨hav.1, hav.2.1.trans hsub.symm, hav.2.2.1, hav.2.2.2.1, hav.2.2.2.2⟩
    · have hi := inv_setSite hinv .soReady (by simp [Site.inEpilogue]) (by simp [Site.inRescale])
        (by rintro ⟨_, _, h⟩; cases h) (by simp) (by simp)
      simpa [code, d', hsub] using hi

/-- The second warpgroup sync precedes the current index slot's free arrival. -/
theorem step_wg0Sync2 (hpre : Pre P L mem0) (d : D) (hd : d.site = .wg0Sync2) :
    (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hinv hc hf => by
    have hsite : d.site.pc = 569 := by rw [hd]; rfl
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hinv.subLt
    rw [hsite] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_569)
    have hr998 : t.regs 998 = some (b32 9) := reg_value hat (by rw [hd]; decide +kernel)
    have hr999 : t.regs 999 = some (b32 128) := reg_value hat (by rw [hd]; decide +kernel)
    have h9 := readBits_b32 (L := L) (g := g) hr998 (by decide : 9 < 2 ^ 32)
    have h128 := readBits_b32 (L := L) (g := g) hr999 (by decide : 128 < 2 ^ 32)
    have hbar : eventTmpl asms L g t (.barSyncN (.reg 998) (.reg 999) true) =
        .bar 9 (PTX.next t) (some 128) .sync := by
      simp [eventTmpl, barTmpl, h9, h128, hpre.block]
    rw [hbar] at hf
    obtain ⟨he, hu⟩ := hf
    have hu' := Option.some.inj hu
    subst u
    let d' : D := { d with site := .validFree, sub := 0 }
    have hn : next P L g d e = some (some d') := by simp [next, nextSite, he, hd, hsub, d']
    have hat' := at_next_of hat hsite hsub
    have hbase := sharedBase_lt hpre
    have hslot : d.block % 4 < 4 := Nat.mod_lt _ (by decide)
    obtain ⟨v, hr, hav⟩ : ∃ v, run kernel asms L g 1 (PTX.next t) = some v ∧
        At v 571 (facts P L g d') := by
      seg_fp hat' using
        (try simp only [d'])
        (try wg0_values)
        (norm_bits [sb, maskStride])
    refine Or.inl (Or.inr ⟨d', v, hn, run_rtg hr, ?_, ?_⟩)
    · exact ⟨hav.1, hav.2.1, hav.2.2.1, hav.2.2.2.1, hav.2.2.2.2⟩
    · apply inv_setSite hinv .validFree <;> simp [Site.inEpilogue, Site.inRescale]

/-- A softmax-ready arrival names the two-slot P barrier, with one arrival and no bytes. -/
theorem fires_soReady (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hd : d.site = .soReady) (hat : (code P L g).AtD d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ rel scope, e.kind = .arrive (shLoc L g (soReadyOff d.slotOf)) 0 1 rel scope ∧
      u = PTX.next t := by
  have hsite : d.site.pc = 1122 := by rw [hd]; rfl
  rw [hsite] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1122)
  have hreg : t.regs 1717 = some (b32 (L.sharedBase + (222920 + 8 * (d.block % 2)))) :=
    reg_value hat (by rw [hd]; decide +kernel)
  have hslot := slotOf_lt d
  have hm := mbarLoc_b32 (L := L) (g := g) (t := t) (base := 1717) hreg
    (ringAddr_lt hpre (off := 222920) (buf := d.slotOf) (by omega))
    (ringAddr_mod8 hpre (off := 222920) (by decide))
  obtain ⟨rel, scope, he, hu⟩ := fires_arrive_next (base := 1717) (tx := .imm 0) (count := .imm 1)
    (A := asms) (L := L) (g := g) (t := t) (cluster := false) (rel := true) (sc := .cta)
    (off := 0) hm (by rfl) (by rfl) hf
  exact ⟨rel, scope, congrArg Event.kind he, Option.some.inj hu⟩

end Wg0

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
