-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.RingExec
public import Kernels.InklingRelDecode.Proof.Protocol.RingSched

@[expose] public section

/-!
# The KV ring protocol of the Inkling decode kernel (obligations 2 and 3 of S6)

This is the first file of the protocol layer. It speaks only about the abstract states of the
site machines (`WComp.code`: `Loader.D`, `Mma.D`) and the shapes of their events (`LdShape`,
`MmShape`, the `EvD` shapes of the prologue); no pc and no register number occurs.

## The ring

Block `i` of a split (`i < num_iters`) stages its K tile and its V tile in slot `i % 3` of the
ring: `kv_ready (i % 3)` and `kv_empty (i % 3)` are mbarriers of arrival count 1, and the block is
the `i / 3`-th use of the slot (`RingSched.slot`, `use`). One use completes one phase of each:

* `kv_ready s`, phase `u`: the producer's `mbarrier.arrive.expect_tx` of **65536 bytes** (one
  arrival; the loader's lane 0 at `LdShape.arrive`, the prologue's `arr j`) and the completion of
  **8 tensor copies of 8192 bytes** (`8 · 8192 = 65536`): the block's K tile (slabs 0 and 1,
  64 columns per box, two boxes per slab) and V tile, `32768 + 32768 B` (`Mma.kLo`, `Mma.vLo`: K at
  `sharedBase + 32768 s`, V at `sharedBase + 98304 + 32768 s`). The loader's elected lane issues
  the eight (`el0 … el3`, two copies each); the prologue issues them as four sites executed by the
  elected lanes of warps 0 and 1 (`ProA.shape_ptc`, `ptcSite (4 j + c)`, warp `% 2` in the
  destination and the origin), also eight per block.
* `kv_empty s`, phase `u`: the MMA warp's PV commit for block `3 u + s` (`MmShape.pvCommit1`,
  `commitSpec cta (kvEmpty ((i - 1) % 3))` in iteration `i`, i.e. block `i - 1`), which follows the
  QK MMAs of block `i - 1` and the PV MMAs of block `i - 1` in program order, so one phase of
  `kv_empty s` retires all reads of the slot's K and V tiles by that use.

**The unified schedule** (`RingSched.issuer`): the first `np = num_pre ≤ 3` blocks are issued by
the default partition's prologue, one per slot `s < np` and without any wait (the barriers are
fresh); every other block is issued by the loader, which waits for the slot first. So slot `s`
has the loader's uses `loaderBlock np s n = 3 (n + [s < np]) + s`, `n = 0, 1, …`.

## What is proved here (all in `Proof/Protocol`, default heartbeats, standard axioms)

* `RingSched`: slot/use/block arithmetic, the unified schedule (`loader_block_iff`), the parity
  of the polls (`readyParity i = (i / 3) % 2`, `emptyParity i = 1 - (i / 3) % 2`), and the phase
  they wait for (`Open`, `ready_open`, `empty_open`, `*_open_iff`, `loader_parity`, `mma_parity`,
  `loader_needs`, `reuse_gate`).
* `RingCount`: `count_trace` (count of events along a machine run = change of a measure of the
  abstract state), `trace_drop`, `trace_take`.
* `RingLoader`: `ld_next`, `ld_okPoll`, `loader_polls`, **`loader_wait`**: at the `wait` site of the
  loader, with `np = polled d₀ ≤ 3`, the event polls `kv_empty (i % 3)` with parity
  `emptyParity i`, block `i` is the loader's `n`-th block of its slot (`n` = the loader's earlier
  successful polls of that barrier) and the parity is `(n + δ) % 2` (`δ = 0` if `s < np`, else 1).
* `RingMma`: the same for the MMA warp's `kv_ready` polls (`mm_next`, `mm_okPoll`, `mma_polls`,
  **`mma_wait`**: block `i` is the `n`-th block of its slot and the parity is `n % 2`).
* `RingExec`: both read on an execution through `wAt` (`= Frame.stateAt (fun g => WComp.code L g
  Q)`): **`loader_poll_exec`**, **`mma_poll_exec`** (the parity field of FA4's `RingFacts.poll`).
* `RingCommit`: the MMA warp's PV commits to `kv_empty` along its run (`Mm.done`, `mma_commits`)
  and **`mma_commit_exec`**: for a thread whose elections all return its lane (`ElectLead`), the
  commit to `kv_empty s` at event `k` is the commit for block `i - 1` of iteration `i` and the
  thread's `n`-th commit to that barrier, `i - 1 = blockOf s n`: the PV commit for block
  `3 n + s` is the `n`-th notification of `kv_empty s`.
* `Ring` (this file): `loader_poll_phase`, `mma_poll_phase`: the same polls as `Open` at the number
  of completed phases of the barrier their block needs.

## Premises of the execution-level statements

* `hin` (the role is one run from the anchor to the event): the worker enters the loader (the
  MMA role) once and does not leave it before the event. It is the role-table protocol
  (obligation 6): one byte per warp, written `0x01000202` by the default partition before
  `bar.sync 1`, read at the dispatch; after the role the worker returns to the dispatch and reads
  the exit byte `3` written at the end. The machine follows the dispatch only when the byte is the
  warp's own (`WCompMachine`), so it is a premise there as well.
* `hfresh` (no earlier successful poll of the barrier before the anchor): follows from `hin` and
  the shapes of the worker's own events (none polls a ring barrier); `EvW` has no shape for
  `.worker`/`.idle`/`.exit` states yet (gap table, the development notes).
* `np ≤ 3` and `np = Spec.numPre`: the loader reads `np` from `sharedBase + 212992`, where the
  prologue wrote `numPre` (`EvD.st9_values`); the equality is a reads-from fact (obligation 6).
* The MMA warp's `Mma.Inv` along the run (given by `Frame.fired_site` for every followed state).

## The one-CTA slot hypotheses and the phase and order theorems (`RingKv*`)

`PairTmaRing.Hyp` is specialised to a CTA pair with two producers, so the KV ring has its own
structure, `Kv.Slot` and `Kv.Hyp` (`RingKvSlot`): the slot's barriers `kvReady c s`/`kvEmpty c s`
(count 1), three threads (`ap` = lane 0 of the loader warp, which arrives; `cp` = the lane the
loader's elections elect, which issues the eight copies; `cm` = the MMA warp's elected lane, which
polls `full` and commits), `δ = 1` when the prologue preloads use 0 of the slot (events `pArr`,
`pCp`), and the record sources of both barriers, the polls' parity, acquire scope and spins, the
issue budget of the copies, and the identity of the prologue's threads. Under `Kv.Hyp`:

* `Lib.KvSingle`: the slot as a slot of the library's single-CTA TMA ring (`Slot.toS`: eight
  copies of 8192 bytes; `Hyp.toS`; `Slot.fits`), and the library's results
  (`Lemmas/Protocol/SingleTmaRing`: `Items`, `Attribution`, `Poll`, `Order`, `RingFacts`,
  `Faults`) stated for the KV definitions: the slot is a `MbarRing.Items.Ring` with nine kinds of
  items per use (one arrival, eight copies; `ring`), each of use `u` an event of the loader (use
  `u - δ` of its thread) or of the prologue (`u = 0`, `δ = 1`); **`F_found`**: the MMA lane's
  successful poll of `kv_ready` with `j` earlier ones found phase `j + 1` and observed phase `j`;
  `consumer_observes`, `producer_observes`: the poll observed every item of the use / the
  consumer's notification of the previous use; **`lane_poll_full`**: any lane's poll found a phase
  at least the schedule's, with `Open p phase` (lower bound only); **`fault_free`**: no record of
  the slot's barriers faults.
* `Lib.KvSingle` (`SingleTmaRing/Order`): `copy_observed`, `copy_before_read`,
  `read_observed`, `read_before_copy`; **`copy_read_order`**: a copy of use `copyUse` (0 for the
  prologue's, else the loader thread's earlier copies over eight plus `δ`) and a read of the MMA
  lane of use `readUse` (its earlier commits to `kv_empty`) that has polled `kv_ready` more times
  than `readUse`, covering one byte, are ordered `AsyncBefore` by their uses: **RAW**
  `copyUse ≤ readUse → write before read`, **WAR** `readUse < copyUse → read before write`.
* `RingLoaderCount`, `RingLoaderExec`: the loader's per-block counts on `kv_ready (i % 3)`:
  **`loader_arrive_exec`** (one arrival, lane 0, 65536 bytes, `n`-th arrival = block
  `loaderBlock np s n`, `arrivals + 1 = okPolls kv_empty`), **`loader_copy_exec`** (eight copies per
  block, the `8 n + j`-th is copy `j = cpIn site`, `copies / 8 + 1 = okPolls kv_empty`; for a thread
  with `ElectLead`).
* `RingKvFoot`, `RingKvMma`: the bytes. **`copy_foot`**: a KV copy writes only `[dst, dst + 8192)`;
  **`qk_b_foot`**, **`pv_b_foot`**, **`qk_a_foot`**, **`pv_a_none`**: a QK MMA's B operand reads
  only its half of the K tile, a PV MMA's B operand only the V tile, A only the Q tile resp.
  nothing from shared memory; **`mma_issue_exec`**: at a QK (PV) MMA of block `i` (`i - 1`) of
  the elected lane, in slot `s`: the lane has committed `i / 3` (`(i - 1) / 3`) times to
  `kv_empty s` and polled `kv_ready s` `i / 3 + 1` (at least `(i - 1) / 3 + 1`) times, and every
  byte read lies in the slot's K region (V region; A: Q region, none);
  **`mma_commit_gate_exec`**: the commit to `kv_empty s` has fewer earlier commits than
  successful `kv_ready s` polls (the gate of `EmptySource.notify`).
* `RingKvPreload`: **`PreloadFacts`**, the one structure of what the default partition has to
  supply (the prologue's arrival and eight copies of slot `s` as events, their `ProA` shapes, their
  threads, completeness), `bar_loc_kvReady`, `tx_balance`.

## What is not proved, and what it needs (statements are kept out of the code)

* **`Kv.Hyp` from the thread layer.** The fields are of three kinds. Proved per thread by the
  execution-level theorems above: the loader's arrival and copy gates and counts
  (`FullSource.arrive`, `copy`, `issue`, budget), the polls' parity (`loader_poll_exec`,
  `mma_poll_exec`: `full_parity`, `empty_parity`), the commit's gate (`mma_commit_gate_exec`:
  `EmptySource.notify`), the acquire scope (`.cta` in `LdShape` and `MmShape`: `full_acq`,
  `empty_acq`). Premises with a gap row in
  the development notes: the record sources as a classification of *every* event that touches a ring
  barrier (needs shapes for `.worker`, `.idle`, `.exit` states and the default partition), that the
  loader states are warp 6's (so `ap`, `cp` are single threads), `ElectLead` of the copy thread
  and `pre_ne`/`pre_cta`/`pre_inj` (`PreloadFacts`), `spins` (DEP-CANONICAL-SPIN of the wait
  sites), initialization first (obligation 1, `InitFirst`) and no invalidation.
* **The upper bound of the phase for a non-designated lane.** Needs the warp barrier edges
  (`bar.warp.sync` before the loader's arrival and before each MMA issue) in the dependency order.
* **The first poll of a fresh slot** (`δ = 0`, no earlier poll): the phase is 0 (not only `≥ 0`):
  `Items.Ring.empty_poll_phase` needs `n ≥ 1`; it needs the gating of the first copy on the poll.
* **From `AsyncCovers` to the byte footprint.** `copy_foot`, `qk_b_foot`, ... are about
  `TensorCopy.writeLoc` and `OperandSpec.byteLoc`; `AsyncCovers X (g, k) (.write (.load x y z)) l`
  is `X.AsyncFootprint` (`Core/Data/Events.lean`: a `TensorIssue` of the thread's event and
  `writeLoc ... = some a.loc`), `.mmaRead` is `MmaFootprint`. The wrapper that turns them into the
  region facts FA4's `RingFacts.write`/`read`/`only_copies` state (an access of a ring region is a
  ring copy's or the MMA lane's) is not written; `only_copies` needs the accessor table of the
  whole shared window (`Lemmas/Protocol/Region.lean`: default partition's Q stores, the
  `(num_pre, num_iters)` and role-table words, barrier objects, TMEM word).
* **The QK reads of block `i` before the commit of block `i`, in program order.** `copy_read_order`
  takes a read as an `X.TcAsync` event with `readUse + 1 ≤ polls`; that each QK MMA of block `i` is
  covered by the lane's commit for block `i` (issued in iteration `i + 1`, after `PV(i)` is
  issued: the commit covers all earlier MMAs of the thread) is `read_before_copy`'s premise
  `hcnt` read with `readUse` of the MMA (`mma_issue_exec` gives `readUse = i / 3`), so nothing more
  is missing there.
* **`np ≤ 3`, `np = Spec.numPre`, `hin`, `hfresh`** as before (role table, obligation 6).

## How the other protocol obligations are structured (not started)

All are of the shape of this file: a role pair, a barrier with an index, per-thread
alternation from the machines' run counts, then the generic barrier lemmas.

* **s_ready / p_ready** (obligation 4; `sReady b`, `pReady b`, `b = i % 2`): producer is the MMA
  warp's `qkCommit` (count 1, elected lane) resp. the softmax's `mbarrier.arrive` (`arrive`
  after the P store, count 1, one lane); consumers poll with parities `(i / 2) % 2`
  (`MmShape.pWait`) and in the softmax region (`Sm`, not yet a machine). Needs: an
  `Sm`-style `wait`/`arrive` count along the softmax loop; the `i % 2` ring has two uses in flight,
  so the unit-ring lemma of `Lemmas/Protocol/UnitRing` (two unit objects) is the model.
* **o_done / o_final** (obligation 5): `pvCommit2`/`finCommit` produce; the softmax's `waitO` and
  the epilogue's poll of `o_final` (`Epi.shape`) consume, with parity 0 for the one use of
  `o_final`; `tcgen05.wait::ld` then `dealloc`.
* **TMEM lifetime** (obligation 7): `tcgen05.alloc` (prologue, warp 0 lane), the base word through
  shared memory, S double buffer `[tm + 128 (i % 2)]`, P aliased on S, O at `tm + 256`; every
  `tcgen05.ld/st/mma` of a thread inside the allocation, `dealloc` after the last `tcgen05.ld`
  of the epilogue (`wait::ld`) and the MMA commit `o_final`. Uses `Lemmas/Tmem`, FA4's
  `Tmem*.lean` as the model; the MMA events' TMEM columns are in `QkIssue`/`PvIssue`.
* **named barrier 1 and the role table** (obligation 6): `bar.sync 1` of 256 threads before the
  dispatch (`Worker.bar1`) and at each role's start/end (`Loader.bar0/bar1`, `Mma.bar0/bar1`),
  the writes of `0x01000202` and `0x03030303`, the reads by the dispatch and by the loader/MMA of
  `(num_pre, num_iters)`; `Lemmas/Protocol/NamedBar*` and `Lemmas/CtaBarrier`. It supplies the
  premises `hin`, `hfresh`, `np = numPre` and the byte values of this file.

## Local generic lemmas for promotion to `Lemmas/`

`RingCount.trace_drop`, `trace_take`, `count_trace` (with an event predicate `E`);
`RingExec.after_split`, `fired_some`, `run_states` (specific to `WComp.code`, but the proofs only
use `Machine.after_append` and `Trace.fired_at`); `RingCommit.not_ends_take`;
`RingLoaderExec.countP_take_split`. **The one-CTA TMA ring** is `Lemmas/Protocol/SingleTmaRing`
(`n` copies of `bytes` bytes per use, an optional preloaded use `δ` with items `pArr`, `pCp`);
`RingKvSlot` is its KV slot with the constants `9 = 1 + 8`, `65536`, `8192`, and `Lib.KvSingle`
the conversion. `scopesMeet`, `commits_tcAsync_succ`, `tcAsync_lt` are the library's.
`RingKvFoot.byteAddress_k`, `byteAddress_mn` (the 128-byte row of a 128-byte-swizzled K-major /
MN-major address), `sdesc_decode`, `decode_k`, `decode_v` (decoding of the `0x40004040` descriptor
family; FA4 has `sdesc_decode`), `box_writeLoc2` (`box_writeLoc` for any
2-byte format). Everything else is kernel-specific.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Ring
open PTX PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvEmpty kvReady)

noncomputable section

variable {Q : Params} {L : Launch} {g : Nat} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre Q L mem0) (hw : 4 ≤ WComp.warpOf L g) (hg : g < L.threads)
include hpre hw hg

end
end PTX.Kernels.InklingRelDecode.Proof.Ring
