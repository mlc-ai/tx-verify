-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.Assembly

@[expose] public section

/-!
# The progress layer: `progress_goal` (umbrella and design note)

## The statement

`ProgressGoal K A L mem0` (`Lemmas/Kernel/Goals.lean`) is
`∀ X, Maximal L K A mem0 X → Complete L X`: every maximal execution is complete. `Maximal`
(`Core/Assembly/Correctness.lean`) says `X` is consistent and no consistent execution extending it
has more counted events (failed polls do not count); `Complete` says every launched thread has
exited (or its cluster was canceled), the asynchronous work is drained (`AsyncDrained`), and the
paired Tensor Memory requests belong to completed collective operations. `correct_of` takes
`hp : SafeGoal → ProgressGoal`, so the proof may use the safety goal.

`Progress.progress_goal` proves it for the Inkling kernel from `Pre`, the softmax region's
obligations (`SmOb`), the thread machines' premises (`Premises`), `SafeGoal` and one structure of
what the thread and protocol layers have not proved (`Remaining`, `Remaining.lean`).

## The argument

The library's descent (`Descent.progress_of_steps`): an incomplete execution has an open obligation
(`Descent.cover`: a pending thread, an issued tensor copy, MMA or commit not finished, a paired
Tensor Memory request not drained), and every open obligation of a maximal execution steps, to a
counted consistent extension or to an open obligation of strictly smaller rank in a maximal
execution (`Assembly.lean`: `obl_steps`). The rank of a pending thread is twice the virtual time of
its abstract machine state, one more while its last event blocks (`Rank.lean`).

A pending thread at a state of `threadCode L g Q` (`Interface.Select`) is classified by the kind of
its next event, read off the instruction at the state's site and its sub-step (`Kinds.lean`:
`nextKind`; no per-role table). A released thread performs its next event: undefined behaviour,
the exit, a fence, a store, a read, an mbarrier initialization or arrival, a tensor copy, an MMA, a
commit, a Tensor Memory load or store or their waits, a named-barrier arrival, a paired Tensor
Memory operation (`Next.lean`, `NextIssue.lean`; each a counted extension that performs no commit
arrive-on). At an mbarrier poll it polls an object whose blocker is earlier (`Polls.lean`); at a
warp collective the whole warp performs it or a lane of the warp is earlier (`WarpFacts.lean`,
`WarpLanes.lean`, `WarpColl.lean`). A thread whose last event blocks (`Collective.lean`:
`thread_cases`) is at a register request, a `bar.sync`, a paired Tensor
Memory operation or a warp-collective `tcgen05` event (the kernel has no cluster barrier, no
`bar.arrive`, no bulk-group wait, no `cp.async` wait); a register request and a `tcgen05`
collective step because a lane of the warp that has not reached them is pending and earlier.
The asynchronous obligations (`Async.lean`): the kernel issues no linear copy, no
`cp.async.mbarrier.arrive`, no tensor store and no cancellation request; a tensor load completes
once its source bytes are fixed, an MMA once its operands have sources, a commit once the MMAs it
tracks have started (a thread's commits all have `commitSpec`, so they deliver in issue order).
`Alloc.lean` proves the allocation facts: the allocation's address store follows its request and a
recorded allocation is at column 0.

## What `Remaining` still takes

Its fields and what discharges them are in `Remaining.lean` and in the rows "progress layer …" of
the development notes ("thread-layer gaps"). Proved here: `alloc_next`, `alloc_base`,
`commit_prev`, `words`,
`syncGuarded`, every `nextKind` class, `fire`, the poll, warp-collective, register-request and
`tcgen05`-collective steps. Premises: `time` (the schedule), `wait_time`, `reads`,
`async` (tensor and MMA sources), `polls` (the six mbarrier waits), `warpColl`, `regWaits`,
`tcWaits`; and three gaps of the library (`regIssue`, `barSteps`, `tmemSteps`).
-/
