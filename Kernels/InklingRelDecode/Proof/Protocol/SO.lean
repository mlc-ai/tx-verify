-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.SOEpi
public import Kernels.InklingRelDecode.Proof.Protocol.SOHandoff
public import Kernels.InklingRelDecode.Proof.Protocol.SOHyp
public import Kernels.InklingRelDecode.Proof.Protocol.SOMmaExec
public import Kernels.InklingRelDecode.Proof.Protocol.SOParity
public import Kernels.InklingRelDecode.Proof.Protocol.SOSched
public import Kernels.InklingRelDecode.Proof.Protocol.SOSmExec
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemLife
public import Kernels.InklingRelDecode.Proof.Protocol.SOTmemOrder

@[expose] public section

/-!
# The S/P/O handshake and the Tensor Memory lifetime (obligations 4, 5 and 7 of S6)

Design note and umbrella of the `SO*` files. Like `Ring.lean` for the KV ring it speaks only about
the abstract states of the site machines and the shapes of their events; the only program counters
are behind `Site.pc` (`SOSites` states its audits through the sites' own accessors).

## The protocol

Block `i` of a split (`i < num_iters`) has its scores in Tensor Memory buffer `b = i % 2` and is the
`i / 2`-th use of it (`SOSched`: `buf`, `useB`, `blockB`, `below2`). The MMA warp's loop (`Mma.D`)
runs `i = 0, …, n`; iteration `i` is the QK half of block `i` (`i < n`) and then the PV half of
block `i - 1` (`i ≥ 1`):

* `tcgen05.mma` ×8 QK into `S b`, then **commit to `s_ready b`** (the elected lane);
* the default partition (`Sm.D`, 128 threads) polls `s_ready b` (parity `(i/2) % 2`), reads its row
  of `S b` (`tcgen05.ld` + `wait::ld`), polls `o_done` (every iteration `i ≥ 1`,
  parity `(i + 1) % 2`) and rescales `O` **only if the rescale is not lazy**, stores `P` over the
  first half of `S b` (`tcgen05.st` + `wait::st`), meets the other threads at `bar.sync 0, 128`,
  and **thread 0 arrives on `p_ready b`**;
* the MMA warp, in iteration `i + 1`, polls `p_ready b` (parity `(i/2) % 2`, every lane), issues the
  PV MMAs of block `i` (A = `P` from Tensor Memory at `tm + 128 b + 8 j`, D = `O`), and commits to
  `kv_empty` and then to **`o_done`**;
* after the loop, one commit to **`o_final`**; the epilogue polls it once (parity 0) and reads `O`.

Tensor Memory columns (`SOTmemCols`): `S b = [tm + 128 b, +128)`, `P b = [tm + 128 b, +64)` (the
alias), `O = [tm + 256, +128)`; the 512-column allocation is `[tm, tm + 512)`, `tm = 0`.

## What is proved (default heartbeats, standard axioms; `SO*` files)

* **Schedule arithmetic** (`SOSched`): buffers, uses, parities (`fullParity i = (i / 2) % 2`), the
  phase at which each poll succeeds (`full_open_iff`, `oDone_open_iff`, `oFinal_open_iff`), and
  the aliasing of the `o_done` poll (`oDone_open_alias`: the poll's parity also passes two phases
  behind). `qk_after_pv`: the QK of block `i + 2` is issued after the PV of block `i`.
* **Audits** (`SOSites`, `decide +kernel`): the program's `mbarrier.try_wait`s are exactly the six
  poll sites of the machines, its `mbarrier.arrive`s the five arrival sites, its `tcgen05.commit`s
  the four of the MMA warp. A fired event at a site that is none of them is not a poll / arrival.
* **The MMA warp** (`SOMmaCount`, `SOMmaEvents`, `SOMmaRun`, `SOMmaExec`): the measures
  `Mm.pPolled`, `Mm.qkDone`, `Mm.oDoneC`, `Mm.finDone` (one-step lemmas `mm_next_*`); the
  classification of the fired event (`mm_okPoll_p`, `mm_commitsTo_s/o/f`); the counts along a run
  (`mma_pPolls`, `mma_sCommits`, `mma_oCommits`, `mma_fCommits`); and on an execution
  **`mma_pwait_exec`** (the `n`-th successful poll of `p_ready b` is for block `2 n + b`, parity
  `n % 2`, every lane), **`mma_qkcommit_exec`** (the `n`-th commit to `s_ready b` is the QK
  commit of block `2 n + b`), **`mma_ocommit_exec`** (the `n`-th commit to `o_done` is for
  block `n`), **`mma_fcommit_exec`** (the commit to `o_final` is the first and only). Premises
  as for the KV ring: the anchored run (`hin`), no earlier event on the barrier (`hfresh`),
  `ElectLead`.
* **The default partition** (`SOSmCount`, `SOSmEvents`, `SOSmRun`, `SOSmExec`, `SOEpi`): the same
  for the softmax region and the epilogue: **`sm_swait_exec`** (a softmax thread's `n`-th poll of
  `s_ready b` is for block `2 n + b`, parity `n % 2`, for each of the 128 threads),
  **`sm_parrive_exec`** (thread 0's `n`-th arrival on `p_ready b` is for block `2 n + b`; no other
  thread arrives: `sm_no_parrive`), `sm_owait_exec` (an `o_done` poll is at `waitO`, parity
  `oDoneParity i`), **`epi_fwait`** (the epilogue's poll of `o_final` is the first, parity 0).
  The thread is taken as an anchored run through one structure, `SmRunAt` (the composed
  default-partition thread, `DComp*`, has to provide it), and `epi_fPolls`'s `hin`.
* **The objects** (`SOHyp`): from the record sources `Facts` (the classification of the events that
  touch the six barriers, the initialization, and the polls' parities) `s_ready b`, `o_final` are
  commit objects of the MMA lane (`sObj`, `fObj`: `MbarRing.Notify.Obj`) and `p_ready b` is a unit
  object of thread 0 (`pObj`: `MbarRing.Unit.Obj`, one producer).
* **The parity fields of `Facts`** (`SOParity`): `s_parity_of_runs`, `p_parity_of_runs`,
  `f_parity_of_runs` discharge `Facts.s_parity`, `p_parity`, `f_parity` from the roles' execution
  theorems, given that every poll of the barrier is an anchored run's (`hanch`; `EpiRunAt` is the
  epilogue's analogue of `SmRunAt`).
* **The handoffs** (`SOHandoff`):
  **S-write before S-read** `s_doneBefore`: a poll of `s_ready b` with `u` earlier successful
  polls observes the commit with `u` earlier commits (`s_observes`), so every MMA issued before it
  is `DoneBefore` every later event of the polling thread (its `tcgen05.ld`).
  **P-write before P-read** `p_store_before_read`: the MMA lane's poll of `p_ready b` with `q`
  earlier polls synchronizes with thread 0's arrival with `q` earlier ones (`p_handoff`,
  `p_before_pv`), so each P store whose `wait::st` is causally before that arrival is
  `StoreDoneBefore` the lane's later events.
  **PV accumulate before the O read and the dealloc** `f_doneBefore`, `f_doneBefore_at`: the
  epilogue's poll of `o_final` observes the only commit to it; every MMA is done before every event
  after the poll.
* **Tensor Memory** (`SOTmemCols`, `SOTmemOrder`, `SOTmemLife`):
  the columns are in the allocation, the buffers and `O` are disjoint, `P b ⊆ S b`
  (`inP_inS`, `inS_disjoint`, `inS_inO_disjoint`, `pv_a_cover`);
  **the result cells of every QK (PV) MMA event lie in `S (i % 2)` (`O`)** and **the A cells of PV
  MMA `j` in the 8 columns `tm + 128 b + 8 j` of `P b`** (`qk_cells`, `pv_cells`, `pv_aCells`:
  from the decoded descriptor, Layout F, `resultCell`/`aCell`); the S load's and the P store's
  columns per thread half (`ldS_col`, `stP_col`) and **the half overlap** that makes the barrier
  `bar20` necessary (`half_overlap`);
  **the PV read of `P b` is before the next QK write to `S b`** with no wait: the PV events of
  iteration `i` precede the QK events of iteration `i + 1` in the MMA warp's program order
  (`pv_before_qk_exec`, from the `o_done` commit counts), and an A read from Tensor Memory is
  pipelined before every later MMA of its thread (`aRead_before_later_mma`: `ReadBefore .a`);
  **the allocation is at column 0** (`alloc_col_zero`, `ld0_tm_zero`, `tm_ok_zero`);
  **every MMA is done before every deallocation** (`mma_done_before_dealloc`).

## Premises (named; the rows are in the development notes, "thread-layer gaps")

* the roles' runs (`hin`, `hfresh`, `SmRunAt`, `ElectLead`, the role table: obligation 6) and the
  facts `hone` (only `cm` issues the MMAs of its CTA), `hbefore` (every MMA of the CTA precedes the
  `o_final` commit);
* `Facts`: the record sources of the six barriers (no other commit, arrival, tensor copy, bulk copy,
  `cp.async.mbarrier.arrive`, cancellation, invalidation names them); the initialization first;
* `WaitOShape`: the event shape of the site `waitO` (thread layer, `Sm.Shape` is `True` there);
* the **dependency paths** of the reuse (`Notify.Reach` for `s_ready`, `Unit.Reach` for
  `p_ready`): the commit of use `t` of `s_ready b` follows the softmax threads' polls for the
  uses before `t` (through `p_ready`), and the arrival of use `t` of `p_ready b` follows the MMA
  lanes' polls for the uses before `t` (through `s_ready`): the FA4 joint induction
  `SFullReach`/`PReadyReach`;
* the **named-barrier orders** (barrier 0 has three arrival counts and the per-thread ordinals of
  the default partition and the workers differ, so the FA4 generation lemmas do not apply as
  they stand): `PAliasSync` (`bar20`: each thread's `wait::ld` before any thread's P store),
  `p_store_before_read`'s `hbar` (`bar21`: each thread's `wait::st` before thread 0's arrival),
  `TmemLife` (every access after the allocation and before the deallocation);
* `BaseWordZero`: the read of `global_smem + 0` returns the zero word (reads-from).

## Findings (not in the task text)

1. **`o_done` is polled in every iteration `i ≥ 1`, so its phase bound is the parity
   alternation** (`SOSmOdone`, `SOOdone`). The fixed kernel waits on `o_done` before the
   lazy-rescale test, so a softmax thread's successful polls are one per iteration from the
   second, with the parity of the thread's earlier polls (`sm_owait_count`: the poll of
   iteration `i` is the thread's `(i - 1)`-th). `o_done` is then a commit object of the MMA lane
   like `s_ready` (`oObj`), its poll with `u` earlier polls observes the notification of the
   commit with `u` earlier commits (`o_observes`), and every MMA of the lane up to that commit is
   done before the poll's later events (`o_doneBefore`): the PV MMAs of block `i - 1` before the
   `tcgen05.ld` of `O` of iteration `i`. The commit-order assumption is not used. As for
   `s_ready`, the premise is the reuse path `Notify.Reach` of the barrier (the commit of use `t`
   follows the thread's polls for the uses before `t`: the joint induction with `p_ready`).
2. **The probabilities alias columns of another thread**: the two halves of a warp share lanes, and
   the P store of half 1 covers columns `[32, 64)` that half 0's S load reads (`half_overlap`). The
   `bar.sync 0, 128` between the loads' waits and the stores is the whole protection (`PAliasSync`).
3. **The epilogue polls `o_final` also when `num_iters < 1`** (`D.startSk`: the second kernel fix
   put the poll in front of the `num_iters` branch), so the MMA warp's commit to it always has a
   poller.
4. **Barrier 0 is used with three arrival counts** (256 threads, 128 threads, 256 threads); see the
   premise above.
5. **`Core` already forbids a column past 512**: `resultCell` and `aCell` give no cell otherwise,
   so `[tm, tm + 512)` is also an acceptance condition of the events.

## Not proved, and what it needs

* the S/P/O handoffs without the dependency-path premises (`Reach`/`Gate`): the joint induction;
* `PAliasSync`, `bar21`'s order and `TmemLife` (named-barrier generation lemma by arrival count);
* `Notify.Reach` of `o_done` (finding 1), with the other reuse paths;
* the exact phase for the lanes other than the designated ones, as for the KV ring;
* the record sources (`Facts`) as a classification over every role's events: the roles' shapes are
  there, the `.worker`/`.idle`/`.exit` states have none (their sites are not in `SOSites`'
  lists, which gives it for polls, arrivals and commits);
* the wrapper from `AsyncCovers` and the region table to byte regions for the S/P/O Tensor Memory
  (the analog of the open KV row): which events access which columns is proved for the MMAs and the
  softmax S load / P store; the O rescale's `tcgen05.ld`/`st` and the epilogue's `tcgen05.ld`
  (`Prm.taddr`) have the shapes (`Epi.Shape.ld`) but no column lemma yet.

## Local generic lemmas for promotion to `Lemmas/`

`SOSmRun.after_none`, `after_some` (a run that reaches a state passes only through states);
`SOSmRun.sm_count` and `SOMmaRun.mma_count` (counting along a code machine's run with an event
class and a state measure: `Ring.count_trace` specialised); `SOSites.site_of_filter` (a program
instruction with a property is at a listed site); `SOSmEvents.arrivesOn_false`;
`SOTmemCols.writeCell_resultCell`, `resultCell_cols`, `aCell_cols` (the columns of a layout-F
result / A cell), `tcDataCell_s16x32bx2_col`; `SOTmemOrder.aRead_before_later_mma`.
-/
