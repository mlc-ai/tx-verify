-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Safety.Protocol
public import Lemmas.Kernel.Goals
public import Kernels.InklingRelDecode.Proof.Interface.InputRead
public import Kernels.InklingRelDecode.Proof2.Safety.Copy

@[expose] public section

/-!
# `SafeGoal` for the Inkling relative decode kernel

`safe_goal` says no consistent execution of the kernel is unsafe, for a launch that satisfies
`Pre`. It takes the thread layer's facts (`Interface.threadFacts`, from `Pre`, the softmax region's
obligations `SmOb` and the machines' `Premises`) and `Protocol`, the one structure of what the
layers below have not proved. The layers above the thread layer speak only of the abstract states
of the machines and of event shapes: no program counter and no register number occurs in this
directory.

## The disjuncts of `Unsafe`, one by one

Status: **done** (proved here from the program text, `Pre` or `ThreadFacts`), **under** (proved
here from the named fields of `Protocol`), **open** (the whole branch is a field).

1. `HasUb`: under `faultFree` (`Interface.no_ub`, with `Premises.tmplOk`: an undefined-behaviour
   event comes only after the machine stopped, and the machine stops only on a value no field
   excludes).
2. `Unalloc`: under `sharedPlaced`, `globalPlaced`, `odoneWait` (`Regions.no_unalloc`: a region
   byte is allocated by `Pre.sharedAllocated`, an input byte by `Interface.reads_mem0`, an output
   byte by `Pre.oAllocated`/`lseAllocated`, a barrier object is inside the window).
3. `Race` and 4. `Mixed`: under `globalReads`, `globalPlaced`, `kvMapOnly`, `sharedPlaced` and
   `order` (`Memory.no_race`, `no_mixed`). Global memory is decided from the thread layer: a
   global write is an epilogue store of an output element (`ThreadFacts.global_wr`), two stores
   that overlap are of one element (`Interface.global_writes_same_element`), and an element has one
   store event (`StoreOnce.storeOnce`: the element determines the thread, and the epilogue's rank
   falls at every store, so a thread does not store a site twice); a write stage of an
   asynchronous operation lands in shared memory (`AsyncWrites.asyncWritesShared`, under
   `kvMapOnly`); a read of a global byte is of an input byte (`globalReads`), which `Pre.
   outputsApart` keeps apart from the outputs. Shared memory is region by region (`order`: the base
   word, the K and V rings by `Ring.Kv.copy_read_order` RAW and WAR, the Q tile, the pair
   `(num_pre, num_iters)` and the role table; the last two are written by every default-partition
   thread with one value, so they are ordered up to `SameValueWrites`).
5. `BarMismatch`: under `barLanes` (`Aligned.no_barMismatch`: the kernel has no `bar.arrive`, so
   only the lane clause remains).
6. `TmaUnsafe`: under `recordsOk`, `objectsPublished`, `sharedPlaced`, `odoneWait`
   (`Objects.no_tmaUnsafe`: the kernel has no `cp.async` and no masked bulk copy, and no generic
   access touches an mbarrier's bytes; every mbarrier operand is one of the twelve barriers,
   `Barriers.mbarPlaced_of`, from the event shapes of initializations, arrivals, commits, copies and
   polls).
7. `TcMma.SourceUnsafe`: open (`tcSource`).
8. A kernel assumption's `ub`: done (`Static.no_assumption_ub`: only `inputReadOnly` declares
   one, and it never holds, `no_inputReadOnly_ub`).
9. `AlignedMismatch`: under `tcAligned`, `barAligned`, `regAligned` (`Aligned.no_alignedMismatch`).
   The cluster and matrix classes are empty (`NoEvents`); the other three need the lanes of a
   warp to run their collectives in lockstep and no participant to exit early.
10. `SharedLifetimeUnsafe`: open (`lifetime`).
11. `ClcUnsafe`: done (`NoEvents.no_clcUnsafe`: no cancellation request).
12. `TensorUnsafe`: under `KvMapOnly`, done on the second tree's role table (`Proof2.kvMapOnly`;
    `Tensor.no_tensorUnsafe`: every copy goes through `mapKv`,
    bf16 with zero fill, so every slot has a byte).
13. `TensorStoreUnsafe`: done (`NoEvents.no_tensorStoreUnsafe`: no tensor store, no linear copy).
14. `TensorAllocationUnsafe`: under `boxInBounds` (`Tensor.no_tensorAllocUnsafe`: no tensor store
    and no prefetch, and no copy selects an out-of-bounds element).
15. `Tmem.Pair.ResourceUnsafe`, 16. `ReleaseUnsafe`: done on the second tree's role table
    (`Proof2.no_resource_unsafe`, `Proof2.no_release_unsafe`, from `Proof2.tmem1Facts`).
18. `AccessUnsafe`: open (`tmemAccess`).
17. `PollShapeUnsafe`: done (`Static.no_pollShapeUnsafe`: the six polls are canonical spins of
    shape B, decided on the code).
19. `TcCommitUnsafe`: done (`TcCommit.no_tcCommitUnsafe`: every commit is the MMA warp's with
    `commitSpec`, the issuing CTA is alone in its cluster).
20. `TcMma.WritesUnsafe`, 21. `InstructionUnsafe`, 22. `ReadsUnsafe`: open (`tcWrites`, `tcInstr`,
    `tcReads`).
23. `SetMaxNReg.Unsafe`: under `regAgree`, `regSync` (`Registers.no_regUnsafe`). Every
    `setmaxnreg` of the program is `inc 256` or `dec 24` (`decide +kernel`, and
    `fires_setMaxReg_op`), so the previous-count clause holds, and the block is 256 threads, two
    whole warpgroups. The open clauses are that the four warps of warpgroup 1 request the same
    direction and count at each ordinal (`EXT-BAR-PARTICIPANTS`) and that a request follows the
    warpgroup's previous requests.
24. `CtaBarFault`: open (`ctaBar`): named barrier 0 is used with counts 256, 128 and 256, barrier 1
    with 256.
25. `ClusterFault`: done (`NoEvents.no_clusterFault`: no cluster barrier instruction).
26. `WarpDivergent`: open (`warpUniform`), and **not provable under `Assumptions.all`**: the six
    guarded `bra.uni` after `mbarrier.try_wait` are executed by all 32 lanes with no order between
    their polls, so two lanes may evaluate the guard differently. FA4 closes the same branch with
    `Assumption.pollAgreeAt` at every poll branch. The kernel needs it too (the development notes,
    `D-ASM-POLLAGREE`, "thread-layer gaps").
27. `MatrixUnsafe`: done (`NoEvents.no_matrixUnsafe`: no warp matrix instruction).
28. `MbarUninit`: open (`mbarInit`).

`TcGroupUniform` is `kernel_groupUniform`.

## What each field needs

The thread-layer fields are classifications of events. `faultFree`: the machines never reject an
event (loaded words, shuffles, role bytes, the `lg2`/`rcp` domains). `sharedPlaced`,
`globalPlaced`, `globalReads`: every read and write of every thread is in one of the regions
(`Regions.lean`) or is an input or output byte; the interface has shapes for the MMA warp's,
the loader's and the epilogue's events, the prologue's initializations, arrivals and counts, and the
global stores, but not for the worker's role-byte read, the base word's allocation store, the
prologue's Q-tile store addresses or the input loads' addresses. `odoneWait`: the `o_done` poll
(`Sm.Site.waitO`) has no event shape. `KvMapOnly` is `Proof2.kvMapOnly` (formerly a field).
`boxInBounds`: the origins of the copies against `Pre.slabInside` and `kvCols`.

The protocol fields need the barrier protocols of `Proof/Protocol` instantiated on the machines,
and the TMEM, named-barrier, warp-lockstep and lifetime protocols that are not written: `order`
(`SharedOrder`), `recordsOk`, `objectsPublished`, `mbarInit`, `barLanes`, `ctaBar`, `tcAligned`,
`barAligned`, `regAligned`, `regAgree`, `regSync`, `warpUniform`, `lifetime`, `tcSource`,
`tmemAccess`, `tcWrites`, `tcInstr`, `tcReads`. Each is a row of
"thread-layer gaps" in the development notes.

Proved and removed from the fields while writing this layer: `storeOnce` (an output element has one
store event), `asyncShared` (asynchronous writes land in shared memory), `mbarPlaced` (down to the
`o_done` poll), the `SetMaxNReg` previous-count and block clauses, the `BarArriveMismatch` clause
and the cluster and matrix aligned classes.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Safety
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0}

/-! ### The read-only input assumption -/

/-- **The read-only input assumption declares no execution undefined.** A write of a global
byte is an output store (`global_intent_write`), and the output arrays of the launch
(`Interface.out_pinned`) hold no input byte of any parameter set of it (`Pre.outputsApart`). -/
theorem no_inputReadOnly_ub {X : Execution} (hpre : Pre Q L mem0)
    (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (has : AsyncWritesShared X) : ¬ Assumptions.inputReadOnly.ub L mem0 X := by
  rintro ⟨P, w, a', l, hP, hw, hc', hsp, -, hrd⟩
  have hsp' : a'.loc.space = .global := hc'.1.symm.trans hsp
  obtain ⟨-, -, -, -, -, -, -, hall⟩ := global_intent_write hpre hX hf has hw hsp'
  obtain ⟨-, -, ho⟩ := hall l hc'
  obtain ⟨h1, h2, h3, h4⟩ := Interface.out_pinned hpre hP
  have hap := hP.outputsApart _ hrd
  rcases ho with h | h
  · exact hap.1 (by rw [h1, h3]; exact h)
  · exact hap.2 (by rw [h2, h4]; exact h)

/-- **No consistent execution of the kernel is unsafe**, given `Pre`, the softmax region's
obligations, the thread machines' premises and the safety layer's protocol facts. -/
theorem safe_goal (hpre : Pre Q L mem0) (hso : SmOb Q L mem0)
    (hP : ∀ X, Consistent L kernel asms mem0 X → Premises Q L X)
    (hR : ∀ X, Consistent L kernel asms mem0 X → Protocol Q L X) :
    SafeGoal kernel Assumptions.all L mem0 := by
  refine ⟨tc_group_uniform, fun X hX hu => ?_⟩
  have hf := threadFacts hpre hso hX (hP X hX)
  have hr := hR X hX
  have hkv : KvMapOnly Q X := Proof2.kvMapOnly hpre hX
  rcases hu with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h
  · exact Interface.no_ub hf.sound (hP X hX) hX hr.faultFree h
  · exact no_unalloc hpre hr.sharedPlaced hr.globalPlaced
      (mbarPlaced_of hpre hX hf hr.odoneWait) h
  · exact no_race hpre hX hf (asyncWritesShared hpre hX hf hkv) hr.globalReads
      hr.globalPlaced (storeOnce hpre hX hf) hr.sharedPlaced hr.order h
  · exact no_mixed hpre hX hf (asyncWritesShared hpre hX hf hkv) hr.globalReads
      hr.globalPlaced (storeOnce hpre hX hf) hr.sharedPlaced hr.order h
  · exact no_barMismatch hX hr.barLanes h
  · exact no_tmaUnsafe hX hr.sharedPlaced (mbarPlaced_of hpre hX hf hr.odoneWait) hr.recordsOk
      hr.objectsPublished h
  · exact hr.tcSource h
  · exact no_assumption_ub (no_inputReadOnly_ub hpre hX hf
      (asyncWritesShared hpre hX hf hkv)) h
  · exact no_alignedMismatch hX hr.tcAligned hr.barAligned hr.regAligned h
  · exact hr.lifetime h
  · exact no_clcUnsafe hX h
  · exact no_tensorUnsafe hpre hX hf hkv h
  · exact no_tensorStoreUnsafe hX h
  · exact no_tensorAllocUnsafe hX hr.boxInBounds h
  · exact Proof2.no_resource_unsafe hpre hX h
  · exact Proof2.no_release_unsafe hpre hX h
  · exact no_pollShapeUnsafe hX h
  · exact hr.tmemAccess h
  · exact no_tcCommitUnsafe hpre hX hf h
  · exact hr.tcWrites h
  · exact hr.tcInstr h
  · exact hr.tcReads h
  · exact no_regUnsafe hpre hX hr.regAgree hr.regSync h
  · exact hr.ctaBar h
  · exact no_clusterFault hX h
  · exact hr.warpUniform h
  · exact no_matrixUnsafe hX h
  · exact hr.mbarInit h

/-- **The conflicts of an execution are ordered, but for the same-value write pairs**, given the
same premises as `safe_goal` (`Memory.conflicts_ordered`). -/
theorem conflicts_ordered_of (hpre : Pre Q L mem0) (hso : SmOb Q L mem0) {X : Execution}
    (hX : Consistent L kernel asms mem0 X) (hP : Premises Q L X) (hr : Protocol Q L X) :
    ConflictsOrderedExcept L X fun _ => True :=
  have hf := threadFacts hpre hso hX hP
  have hkv : KvMapOnly Q X := Proof2.kvMapOnly hpre hX
  conflicts_ordered hpre hX hf (asyncWritesShared hpre hX hf hkv) hr.globalReads
    hr.globalPlaced (storeOnce hpre hX hf) hr.sharedPlaced hr.order

end
end PTX.Kernels.InklingRelDecode.Proof.Safety
