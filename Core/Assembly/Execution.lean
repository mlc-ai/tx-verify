-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.AsyncMBarrier
public import Core.Async.Tensor.TensorExecution
public import Core.Async.BulkExecution
public import Core.Async.Tensor.TensorSafety
public import Core.Async.Tensor.TensorReduce
public import Core.Tmem.TmemPairRelease
public import Core.Tmem.TmemPairCompletion
public import Core.Tmem.TmemPairAccess
public import Core.Tc.TcMmaRead
public import Core.Tc.TcMmaConflicts
public import Core.Tc.TcMmaSafety
public import Core.Tc.TcMmaCompletion
public import Core.Tc.TcCommitSafety
public import Core.Sync.Aligned
public import Core.Thread.Run
public import Core.Memory.Read
public import Core.Assembly.Waiting
public import Core.Assembly.WaitOrder
public import Core.Assembly.Dependency
public import Core.Assembly.Safety
public import Core.Memory.Atomic
public import Core.Sync.WarpUniform
public import Core.Sync.MatrixExec

@[expose] public section

/-!
# Assembly of consistent and unsafe executions

Review the numbered entries below; the review guide is in `Core/README.md`.
-/

namespace PTX

noncomputable section

variable (L : Launch)

/-! ## CORRECT-CONSISTENT — possible executions
Statement: An execution is possible when the trace of every launched thread is one that the thread
  rules produce from the initial state, threads outside the launch have no events, and the execution
  satisfies every execution constraint of the model. These constraints cover reads-from and the
  memory axioms, blocking and collective operations, the order of each synchronization object, the
  origin of asynchronous effects, and what each kernel assumption adds.

Defs: Consistent, Consistent.reduceUnique, Consistent.reduceAcyclic

Source:
- §8 (an execution is possible when it satisfies the axioms); several fields rest on named readings
    (EXT-OBJECT-ORDER, EXT-ASYNC-OBJECT, EXT-ENABLES-OBJECT, EXT-TMEM-ALLOC-ORDER, EXT-STAGE-ORDER,
    EXT-TCACQUIRE, EXT-TC-EXEC-ORDER, EXT-PAIR-ASYNC, EXT-INIT-FENCE-ARRIVE), so the conjunction is
    a reading

Direction: reading

Effect: The conjunction of the rules above. Each field names its rule. Each thread's trace is one
  that its thread rules allow from the initial state, and threads outside the launch have none
  (THREAD-RUN). Blocking and waiting are one field, `Consistent.dependency` (DEP-ORDER); the
  value rules of the collectives keep only what they say about values. `Consistent.reduceUnique` and
  `Consistent.reduceAcyclic` derive the two conclusions of EXT-TMA-REDUCE-ATOMIC from MEM-ATOMICITY.
-/

/-- The possible executions of kernel `K` under assumptions `A`, launch `L` and launch
memory `mem0`. -/
structure Consistent (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution) :
    Prop where
  /-- CORRECT-CONSISTENT: traces (THREAD-RUN) -/
  thr : ∀ g < L.threads, Produces K A L g (X.tr g)
  /-- CORRECT-CONSISTENT: traces (THREAD-RUN) -/
  outside : ∀ g, L.threads ≤ g → X.tr g = []
  /-- MEM-READS-FROM -/
  rf : RfWf mem0 X
  /-- OBJ-CTA-BARRIER-SYNC: the CTA barrier histories -/
  ctaBar : CtaBarHistoryOk L X
  /-- OBJ-CLUSTER-BARRIER-SYNC: the cluster barrier histories -/
  cluster : ClusterHistoryOk L X
  /-- DEP-ORDER: every returned event is ready, and the dependency order with the order of
  any one object has no cycle -/
  dependency : DependencyOk L K X
  /-- DEP-WARP-SHUFFLE -/
  shfl : ShflOk L X
  /-- DEP-WARP-VOTE -/
  vote : VoteOk L X
  /-- DEP-WARP-VOTE (modes), DEP-WARP-REDUX, DEP-WARP-MATCH, DEP-WARP-ACTIVEMASK -/
  warpValue : VoteModeOk L X ∧ ReduxOk L X ∧ MatchOk L X ∧ ActiveMaskOk L X
  /-- DEP-WARP-MATRIX, DEP-WARP-MMA -/
  matrix : MatrixOk L A X
  /-- DEP-WARP-ELECT -/
  elect : ElectOk L X
  /-- DEP-WARP-BARRIER -/
  warpBar : WarpBarOk L X
  /-- MEM-OBJECT-ORDER-CAUSALITY: a synchronizing observation never precedes its source in causality
-/
  observation : ObservationCausal L X
  /-- MEM-OBJECT-ORDER-CAUSALITY (EXT-OBJECT-ORDER): the synchronizing part of each object's order
agrees
    with causality, one object at a time -/
  object : ObjectCoherent L X
  /-- MEM-OBJECT-ORDER-CAUSALITY (EXT-ASYNC-OBJECT): an asynchronous update follows its issue in its
  object's order -/
  asyncObject : AsyncObjectOrdered L X
  /-- OBJ-MBAR-INIT-PUBLICATION (EXT-INIT-FENCE-ARRIVE): an initialization published by
  `fence.mbarrier_init` and a cluster barrier precedes, in its object's order, the operations
  issued after the wait -/
  initFence : InitFenceOrdered L X
  /-- MEM-READ-AXIOMS -/
  noFuture : NoFuture L X
  /-- MEM-READ-AXIOMS -/
  hidden : Hidden L X
  /-- DEP-ASYNC-ORIGIN -/
  tma : TmaOk X
  /-- OBJ-CLC-ORIGIN -/
  clc : ClcOk L X
  /-- DEP-TENSOR-LOAD-ORIGIN -/
  tensor : TensorOk L X
  /-- DEP-BULK-WAIT -/
  store : TensorStoreOk L X
  /-- DEP-REDUCTION-VALUES -/
  reduce : TensorStore.ReduceOk A X
  /-- MEM-ATOMICITY -/
  atomic : AtomicOk L X
  /-- MEM-FENCE-SC -/
  fenceSc : FenceScOk L X (baseCausality L X)
  /-- OBJ-TMEM-ORIGIN -/
  tmemPair : Tmem.Pair.HistoriesOk L X
  /-- OBJ-TMEM-COMPLETION-PREFIX -/
  tmemPairCompletion : Tmem.Pair.CompletionClosed L X
  /-- OBJ-TMEM-ALLOC-RESULT -/
  tmemPairResult : Tmem.Pair.ResultOk L X
  /-- OBJ-MBAR-ORIGIN: per-target commit delivery -/
  tcCommit : AsyncCopy.CommitOk X
  /-- DEP-TC-COMPLETION-CLOSURE: same-source identical-footprint D writes. -/
  mmaCompletion : TcMma.CompletionClosed L X
  /-- DEP-TC-LOAD-VALUE -/
  tcRead : TcMma.ReadOk L A X
  /-- ASM-INTERFACE: what each kernel assumption adds -/
  asm : ∀ a ∈ A, a.wf L mem0 X

/-- In a possible execution, the reductions of one element read their old bytes uniquely
(MEM-ATOMICITY, EXT-TMA-REDUCE-ATOMIC). -/
theorem Consistent.reduceUnique {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) : TensorStore.ReduceUnique X :=
  reduceUnique_of_atomic L hX.atomic.unique hX.store hX.outside

/-- In a possible execution, reads among the reductions of one element have no cycle
(MEM-ATOMICITY, EXT-TMA-REDUCE-ATOMIC). -/
theorem Consistent.reduceAcyclic {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) : TensorStore.ReduceAcyclic X :=
  reduceAcyclic_of_atomic L hX.atomic.acyclic hX.store hX.outside

/-! ## ERR-UNSAFE — undefined behaviour
Statement: An execution is unsafe when it contains an undefined-behaviour event, touches unallocated
  memory, has a data race or a mixed-size conflict, breaks a rule of the barriers, mbarriers, bulk
  copies, CLC, Tensor Memory, shared-memory lifetime or warp-level matrix instructions, breaks the
  `.aligned` qualifier, uses an mbarrier that no published initialization precedes, diverges within
  a warp at an instruction that needs a uniform guard, uses an mbarrier poll result other than in a
  canonical spin, or is declared undefined by a kernel assumption.

Defs: Unsafe

Source:
- §9.7 (the undefined-behaviour sentences of the individual instruction descriptions)
- §8.7 (data races)
- §8.2.6 (allocation, ERR-UNALLOCATED-ACCESS)
- the ERR- entries named in the Effect; the `stricter` ones among them are the checks that are
    stricter than the text (their Direction says so in `Core/README.md`)

Direction: stricter

Effect: The disjunction of the checks of the model, each owned by an ERR- entry, and of the `ub`
  conditions of the kernel assumptions, which have no ERR- entry. In the order of `Unsafe`, an
  execution is unsafe if it has a `ub` event (`HasUb`, ERR-UNDEFINED-INSTRUCTION), touches an
  unallocated byte (`Unalloc`, ERR-UNALLOCATED-ACCESS), has a data race (`Race`, ERR-DATA-RACE) or a
  mixed-size conflict (`Mixed`, ERR-MIXED-SIZE), a CTA barrier mismatch (`BarMismatch`,
  ERR-BARRIER-MISMATCH), an mbarrier fault or an object used outside its lifetime (`TmaUnsafe`,
  ERR-OBJECT-LIFETIME), or a Tensor Memory read without a read source (`TcMma.SourceUnsafe`,
  ERR-TMEM-READ-SOURCE), if a kernel assumption declares it undefined (`a.ub`), or if it has an
  aligned instruction executed differently by the lanes of a warp or skipped by an exited
  participant (`AlignedMismatch`, ERR-ALIGNED-MISMATCH), a use of shared memory outside its
  lifetime (`SharedLifetimeUnsafe`, ERR-SHARED-LIFETIME), a CLC request after an observed failure
  (`ClcUnsafe`, ERR-CLC-REQUEST-AFTER-FAILURE), a tensor load that writes a byte without a scalar
  value (`TensorUnsafe`, ERR-TENSOR-FILL-VALUE), a performed reduction element without an
  arithmetic rule (`TensorStoreUnsafe`, ERR-REDUCTION-NO-RULE), an out-of-bounds element of a
  tensor map of the large allocation class without an accessible backing range
  (`TensorAllocationUnsafe`, ERR-TENSOR-LARGE-OOB), a Tensor Memory allocator fault
  (`Tmem.Pair.ResourceUnsafe`, ERR-TMEM-RESOURCE), a Tensor Memory allocation still live at kernel
  completion (`Tmem.Pair.ReleaseUnsafe`, ERR-TMEM-NOT-RELEASED), a poll whose result is used other
  than in a canonical spin (`PollShapeUnsafe`, ERR-POLL-SHAPE), a Tensor Memory access outside a
  completed allocation or not completed before its release (`Tmem.Pair.AccessUnsafe`,
  ERR-TMEM-ACCESS-LIFETIME), a `tcgen05.commit` whose CTA group does not exist in the cluster
  (`TcCommitUnsafe`, ERR-TC-COMMIT-GROUP), two unordered Tensor Memory writes of a cell
  (`TcMma.WritesUnsafe`, ERR-TMEM-RACE), an invalid MMA or `tcgen05.cp` instance or a completed MMA
  result without a derived value (`TcMma.InstructionUnsafe`, ERR-TC-MMA), an MMA read unordered
  with a write of its cell (`TcMma.ReadsUnsafe`, ERR-TMEM-RACE), an illegal `setmaxnreg` request
  (`SetMaxNReg.UnsafeAt`, ERR-SETMAXNREG), a CTA barrier fault (`CtaBarFault`, ERR-CTA-BARRIER), a
  cluster barrier fault (`ClusterFault`, ERR-CLUSTER-BARRIER), warp-divergent control flow at an
  instruction that requires a uniform guard (`WarpDivergent`, ERR-NONUNIFORM-GUARD), an undefined
  instance of a warp-level matrix instruction (`MatrixUnsafe`, ERR-WARP-MATRIX), or an mbarrier
  operand whose initialization is not published to the instruction (`MbarUninit`,
  ERR-MBAR-UNINITIALIZED).
-/

/-- The execution `X` has undefined behaviour (ERR-UNSAFE): the disjunction of every safety check of
the model and of the kernel assumptions' `ub` conditions. -/
def Unsafe (K : Kernel) (A : List Assumption) (mem0 : Mem0) (X : Execution) : Prop :=
  HasUb X ∨ Unalloc mem0 X ∨ Race L X ∨ Mixed L X ∨ BarMismatch L X ∨ TmaUnsafe L mem0 X ∨
    TcMma.SourceUnsafe L A X ∨ (∃ a ∈ A, a.ub L mem0 X) ∨ AlignedMismatch L K X ∨
    SharedLifetimeUnsafe L K A X ∨ ClcUnsafe L X ∨ TensorUnsafe X ∨
    TensorStoreUnsafe A X ∨ TensorAllocationUnsafe L mem0 X ∨
    Tmem.Pair.ResourceUnsafe L X ∨ Tmem.Pair.ReleaseUnsafe L X ∨ PollShapeUnsafe K X ∨
    Tmem.Pair.AccessUnsafe L X ∨ TcCommitUnsafe L X ∨ TcMma.WritesUnsafe L X ∨
    TcMma.InstructionUnsafe L A X ∨ TcMma.ReadsUnsafe L X ∨ SetMaxNReg.UnsafeAt A L X ∨
    CtaBarFault L X ∨ ClusterFault L X ∨ WarpDivergent L K A X ∨ MatrixUnsafe L A X ∨
    MbarUninit L X

end

end PTX
