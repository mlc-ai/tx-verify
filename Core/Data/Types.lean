-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.CtaBarrierHistory
public import Core.Sync.ClusterBarrierHistory
public import Core.Data.AsyncTypes
public import Core.Clc.ClcEffects
public import Core.Async.Tensor.TensorCopy
public import Core.Async.Tensor.TensorStore
public import Core.Data.TmemPairTypes
public import Core.Tc.TcMmaOperands
public import Core.Tc.TcCommitTargets
public import Core.Tc.TcCopy

@[expose] public section

/-!
# Types of the model

Data only: thread state, events, executions, event templates, and the interface of a
kernel assumption. Which executions are possible is decided by `Core/Assembly/Execution.lean`.
-/

namespace PTX

noncomputable section

/-! ## THREAD-STATE — a thread's local state
Statement: A thread's local state is its position in the source, its registers, the carry flag of
  its condition code register, the progress of the current vector access, and the undefined
  behaviour found since its last event, if any. It says nothing about whether memory operations
  have completed.

Defs: TState

Source:
- §8.9.1 (program order is defined on the source)
- §9.7.2: "Instructions add.cc , addc , sub.cc , subc , mad.cc and madc reference an implicitly
    specified condition code register ( CC ) having a single carry flag bit ( CC.CF ) holding
    carry-in/carry-out or borrow-in/borrow-out."

Direction: representation

Effect: The state holds a source position, the registers (by id, PROG-INSTR-FORMS), the carry flag
  `CC.CF` (`none` until an instruction writes it, THREAD-INT), and the progress of the current
  vector access. The position says where the thread is in its source and nothing about whether
  earlier memory operations have completed or later ones have. `fault` records undefined behaviour
  found by local steps: the thread's next event is `ub`.
-/

/-- The local state of one thread (THREAD-STATE): source position, registers, the progress of the
current vector access, and a pending fault. -/
structure TState where
  pc : Nat := 0
  regs : Nat → Option Value := fun _ => none
  /-- The carry flag `CC.CF` of the condition code register; `none` until an instruction writes
  it. -/
  cf : Option Bool := none
  /-- Elements of the current vector access already performed. -/
  sub : Nat := 0
  /-- Values returned so far by the elements of the current vector load. -/
  acc : List Value := []
  /-- Undefined behaviour found after the last event: the next event is `ub`. -/
  fault : Option Fault := none

/-! ## THREAD-TC-EVENT — Tensor Core operations as events
Statement: Each `tcgen05` instruction is one event of a thread. An event records what the
  instruction names: the access shape of a load or store, the request of an allocation, or the
  destination, descriptors and output-lane mask of an MMA. The values that a load returns and the
  column that an allocation selects are left open, and the execution rules decide which are
  possible.

Defs: TcKind

Source:
- §9.7.18.1 (Tensor Memory)
- §9.7.18.7.1 (tcgen05.alloc, tcgen05.dealloc)
- §9.7.18.8.3 (tcgen05.ld)
- §9.7.18.8.4 (tcgen05.st)
- §9.7.18.8.5 (tcgen05.wait)
- §9.7.18.9.2 (tcgen05.cp)
- §9.7.18.10.10.1 (tcgen05.mma)
- §9.7.18.11.1 (tcgen05.fence)
- §9.7.18.12.1 (tcgen05.commit)

Direction: representation

Effect: A `tcgen05` instruction is one event. A Tensor Memory address is a 32-bit value, lane in the
  high and column in the low 16 bits. What the hardware returns at a load is recorded in that event
  and left open. A load or store records its access shape (`TcShape`, with the `.16x32bx2`
  half-split offset), so every rule that reads its cells uses the same shape. An allocation event
  records the request only: the column is selected when the allocation completes, and is the value
  of the address store that follows it (THREAD-TC, OBJ-TMEM-ALLOC-RESULT). An MMA issue records its
  destination, its decoded descriptors with the CTA identities of its group, accumulation and
  output-lane mask; its operand bytes are recorded separately in the asynchronous snapshot when
  read. The execution rules (DEP-TC-MMA-VALUE, DEP-TC-LOAD-VALUE, OBJ-TMEM-ALLOC-RESULT) and
  reads-from constraints decide which observations are possible.
-/

/-- The `tcgen05` instructions as thread events: allocation management, MMA issue, commit, fence,
load, store, wait and copy (THREAD-TC-EVENT). -/
inductive TcKind where
  /-- Allocation management: `tcgen05.alloc` (with the destination of the returned
  address), `tcgen05.dealloc` or `relinquish_alloc_permit`. -/
  | resource (group : CtaGroup) (dst : Option Loc) (request : Tmem.Request)
  /-- A dense MMA issue with its output-lane mask; actual operand reads belong to the
  async snapshot. -/
  | mma (d : Nat) (operands : TcMma.OperandSpec) (accumulate : Bool)
      (disableOutput : List Nat)
  /-- `tcgen05.commit`: one completion notification per selected cluster rank's mbarrier. -/
  | commit (spec : TcCommit.Spec)
  | fenceBefore
  | fenceAfter
  /-- `tcgen05.ld` of shape `shape` from Tensor Memory address `a`, returning `vals`. -/
  | ld (a : Nat) (vals : List Value) (shape : TcShape)
  /-- `tcgen05.wait::ld`. -/
  | waitLd
  /-- `tcgen05.st` of shape `shape` of `vals` to Tensor Memory address `a`. -/
  | st (a : Nat) (vals : List Value) (shape : TcShape)
  /-- `tcgen05.wait::st`. -/
  | waitSt
  /-- `tcgen05.cp` of the copy `spec` (THREAD-TC-CP-CELLS); its source reads and completion are
  asynchronous effects. -/
  | cp (spec : TcCopy.Spec)
  /-- `tcgen05.shift` of the shift `spec` (THREAD-TC-SHIFT-CELLS); its Tensor Memory reads, writes
and
  completion are asynchronous effects. -/
  | shift (spec : TcShift.Spec)
  deriving DecidableEq

/-! ## THREAD-EVENT — events
Statement: An event is one operation of one thread: a generic-proxy read or write of a footprint, an
  atomic read-modify-write of a footprint, a non-coherent global read, a barrier arrival, a
  completed shuffle, vote, reduction, match or election, an `activemask` query, a read of special
  registers whose values change while the thread runs, a register adjustment request, an mbarrier,
  bulk-copy, tensor or cluster launch control operation, the thread's exit, or undefined behaviour.
  A read records the raw bytes that it returned, and the thread rebuilds the value from them.

Defs: TensorPrefetch.Spec, BarMode, Kind, Event

Source:
- §8.2 (memory operations)
- §8.4 (operation types: `ld` / `st` without qualifiers are weak)
- §8.6 (generic proxy)
- §9.7.15.5 (atom)
- §9.7.15.6 (red)
- §9.7.15.1 (bar.sync, bar.arrive)
- §9.7.15.3 (barrier.cluster)
- §9.7.15.10 (vote.sync)
- §9.7.15.11 (match.sync)
- §9.7.15.12 (activemask)
- §9.7.15.13 (redux.sync)
- §9.7.15.16 (mbarrier)
- §9.7.10.28.3 (cp.async and its groups)
- §9.7.10.28.4.1 (cp.async.bulk)
- §9.7.10.28.4.3 (cp.async.bulk.prefetch)
- §9.7.15.16.18 (cp.async.mbarrier.arrive)
- §9.7.10.28.5.5 (cp.async.bulk.prefetch.tensor)
- §9.7.16.5.14 to §9.7.16.6.3 (mma, ldmatrix, stmatrix, movmatrix, mma.sp)
- §10.4
- §10.8
- §10.23
- §10.24
- §10.28 (special registers that change)

Direction: representation

Effect: An event is one operation of one thread: a generic-proxy read or write of a footprint, an
  atomic read-modify-write of a footprint (`atom`, `red`), which is one event that both reads and
  writes (THREAD-ATOMIC), an `ld.global.nc` read, a CTA barrier arrival (`bar.sync`, or
  `bar.arrive`: `BarMode`), a completed warp shuffle, vote, reduction or match, an `activemask`
  query, a completed warp-level matrix instruction with the bytes the lane contributes and receives
  (DEP-WARP-MATRIX), a read of the special registers that change while the thread runs, with the
  value read from each (THREAD-SREG), the thread's exit, undefined behaviour, an mbarrier or copy
  operation (DEP-ASYNC-ORIGIN), or a `cp.async` group commit, group wait or mbarrier arrive
  (THREAD-CP-ASYNC), or a thread fence or proxy fence (THREAD-FENCE). A read records the raw byte
  contents it returned, so any read can be recorded and a race cannot hide; the value is rebuilt by
  the thread (THREAD-BYTES). A tensor prefetch records the elements it selects
  (`TensorPrefetch.Spec`): the transfer descriptor, origin and four-row coordinates of a tensor
  load, without a shared destination or mbarrier. Its memory read is an asynchronous stage keyed by
  this event (MEM-FOOTPRINT).
-/

/-- The elements a `cp.async.bulk.prefetch.tensor` selects: the descriptor of its transfer
(four-row mode: the map's with four rows, `Descriptor.fourRows`), the signed origin and, in
four-row mode, the tensor row of each box row. -/
structure TensorPrefetch.Spec where
  /-- Rank minus one (`.1d` .. `.5d`). -/
  outer : Nat
  descriptor : TensorDescriptor.Descriptor outer
  origin : Fin (outer + 1) → Int
  rows : Option (Fin 4 → Int) := none

/-- The form of a CTA barrier arrival: `.sync` waits for the barrier to complete
(`barrier{.cta}.sync`), `.arrive` does not (`barrier{.cta}.arrive`). -/
inductive BarMode where
  | sync | arrive
  deriving DecidableEq, Repr

/-- The kind of an event: the effect of the instruction that performed it, together with the
values it returned. The mbarrier kinds are `mbInit`, `mbInval`, `arrive`, `wait` and
`fenceMbarInit`. -/
inductive Kind where
  /-- A register adjustment request (`setmaxnreg`). `inst` is an uninterpreted label;
  matching uses the per-thread request ordinal, source PC and payload. -/
  | setMaxReg (increase : Bool) (count inst : Nat)
  | warpBar (mask inst : Nat)
  /-- Completed election; instance labels pair this dynamic collective across lanes. -/
  | elect (mask inst leader : Nat)
  /-- A generic-proxy read of `a`; its qualifiers are in `a`, with one result per byte. -/
  | rd (a : Acc) (bs : List (Option Byte))
  /-- An `ld.global.nc` read: outside the memory consistency model (§8.1). -/
  | nc (a : Acc) (bs : List (Option Byte))
  /-- A generic-proxy write of `a`, retaining its memory qualifiers. -/
  | wr (a : Acc) (bs : List Byte)
  /-- An atomic read-modify-write of `a` (`atom`, `red`): one operation that read the bytes `old`
  and wrote the bytes `new`; `new` is `none` when the operation has no result for `old`, and the
  thread's next event is then `ub`. -/
  | rmw (a : Acc) (old : List (Option Byte)) (new : Option (List Byte))
  /-- Arrival at CTA barrier `id`; `none` denotes the omitted thread count. `mode` is
  `.sync` for `bar.sync` and `.arrive` for `bar.arrive`. -/
  | bar (id : Nat) (count : Option Nat := none) (mode : BarMode := .sync)
  | cluster (op : ClusterOp)
  /-- Explicit observation so failed responses can constrain later CLC requests. -/
  | clcQuery (query : ClcQuery) (response : ClcResponse)
  | clcIssue (spec : Clc.Spec) (targets : List Nat)
  | tensorIssue (mapAddress : Nat) (spec : TensorCopy.Spec)
  | tensorStore (mapAddress : Nat) (spec : TensorStore.Spec)
  | bulkCommit
  | bulkWait (mode : BulkGroup.WaitMode) (remaining : Nat)
  /-- A completed `shfl.sync`: own operand `a`, lane operands `b`, `c`, the value
  received and the in-range predicate. -/
  | shfl (mode : ShflMode) (a : Value) (b c : Nat) (recv : Value) (ok : Bool)
  /-- A completed `vote.sync.ballot.b32` with member mask `mask`: own predicate `a` and the
  ballot received. -/
  | vote (mask : Nat) (a : Bool) (ballot : BitVec 32)
  /-- A completed `vote.sync` with mode `.all`, `.any` or `.uni` and member mask `mask`: own
  predicate `a` and the predicate received. -/
  | voteMode (mode : VoteMode) (mask : Nat) (a : Bool) (d : Bool)
  /-- A completed integer `redux.sync` with operation `op` (`signed` for `.s32`) and member mask
  `mask`: own source `a` and the result received. -/
  | redux (op : ReduxOp) (signed : Bool) (mask : Nat) (a : BitVec 32) (d : BitVec 32)
  /-- A completed `match.sync` (`all` for `.all`, `wide` for `.b64`) with member mask `mask`: own
  operand `a`, the mask received and whether all the operands of the instance are equal. -/
  | match_ (all wide : Bool) (mask : Nat) (a : BitVec 64) (d : BitVec 32) (p : Bool)
  /-- An `activemask`: the mask returned. -/
  | activemask (d : BitVec 32)
  /-- A completed warp-level matrix instruction (DEP-WARP-MATRIX): its operation, the bytes the lane
  contributes and the bytes it receives. -/
  | matrix (op : MatrixOp) (own recv : List (Option Byte))
  | exit
  | ub (f : Fault)
  /-- `mbarrier.init` of the mbarrier object at `m`, with its expected arrival count. -/
  | mbInit (m : Loc) (count : Nat)
  /-- `mbarrier.inval` of the mbarrier object at `m`. -/
  | mbInval (m : Loc)
  /-- A thread fence (`fence{.sem}.scope`, `membar`) with its semantics and scope (THREAD-FENCE). -/
  | fence (sem : FenceSem) (scope : MbarScope)
  /-- A proxy fence of kind `k` with its scope, `none` for a form without a scope (THREAD-FENCE). -/
  | fenceProxy (k : ProxyFence) (scope : Option MbarScope)
  /-- `fence.mbarrier_init.release.cluster`, which publishes the thread's prior `mbarrier.init`
  operations on `.shared::cta` objects (§9.7.15.4). -/
  | fenceMbarInit
  /-- `mbarrier.arrive{.expect_tx}`: `count` arrivals on `m` after expecting `tx` transaction
  bytes, with release (`release`) or relaxed semantics at `scope`. The defaults are the
  PTX defaults: one arrival, `.release`, `.cta`. -/
  | arrive (m : Loc) (tx : Nat) (count : Nat := 1) (release : Bool := true)
      (scope : MbarScope := .cta)
  /-- Issue of a linear copy (`cp.async`, `cp.async.bulk`); its read, write and notification are
  independent async effects (DEP-LINEAR-COPY-EFFECTS). -/
  | copy (s : AsyncCopy.Spec)
  /-- `cp.async.bulk.prefetch` of the global range `src`: a pending read through the async proxy
  that returns nothing and never completes (EXT-PREFETCH-PENDING). -/
  | bulkPrefetch (src : Acc)
  /-- `cp.async.commit_group`: closes the thread's uncommitted `cp.async` operations into a
  `cp.async`-group. -/
  | asyncCommit
  /-- A completed `cp.async.wait_group` leaving out the `remaining` most recent groups. -/
  | asyncWait (remaining : Nat)
  /-- `cp.async.mbarrier.arrive{.noinc}` on the mbarrier object at `m`: without `.noinc` it
  increments the pending count; its arrive-on is an asynchronous stage (`Part.arriveOn`). -/
  | asyncArrive (m : Loc) (noinc : Bool)
  /-- `mbarrier.try_wait.parity`: whether phase `parity` of `m` was found complete, with
  acquire (`acquire`) or relaxed semantics at `scope`; PTX default `.acquire.cta`. -/
  | wait (m : Loc) (parity : Nat) (ok : Bool) (acquire : Bool := true)
      (scope : MbarScope := .cta)
  /-- A `tcgen05` instruction (THREAD-TC-EVENT). -/
  | tc (k : TcKind)
  /-- `cp.async.bulk.prefetch.tensor` with map address `mapAddress`, selecting `spec`'s
  elements. Its read of their in-bounds bytes is an asynchronous stage (MEM-FOOTPRINT); it
  returns no value to the thread, writes nothing and has no completion. -/
  | tensorPrefetch (mapAddress : Nat) (spec : TensorPrefetch.Spec)
  /-- A read of the special registers `regs` that change while the thread runs, with the value
  read from each (THREAD-SREG). -/
  | sreg (regs : List SReg) (vals : List Nat)

/-- One event of a thread trace: the source position of its instruction and its kind. -/
structure Event where
  /-- Source position of the instruction that performed it. -/
  pc : Nat
  kind : Kind

/-! ## MEM-EXECUTION — executions
Statement: An execution has one finite trace of events per thread, and for every byte of every read
  the write that it read from, or the initial write. It also records the asynchronous effects,
  the histories of the synchronization objects and the Fence-SC order of its `fence.sc` events.
  There is no global memory, global order or global time.

Defs: Execution, Execution.initialByte

Source:
- §8 (an execution is a set of operations with relations between them)
- §8.2.6 (W0)

Direction: representation

Effect: An execution has one finite trace of events per thread, and reads-from: for every byte of
  every read, the write event it read from, or `none` for `W0`. An event is named by its thread and
  its index in that thread's trace. There is no global memory, no global order and no global time.
  Finite traces are enough: `terminates` bounds them, and `progress` speaks about executions that
  cannot grow. `initial` chooses the values of allocated launch bytes not specified in `Mem0`; known
  bytes override it. These choices are universally quantified with the execution and are initial
  contents, not a current shared memory state.
-/

/-- One candidate execution of a kernel (MEM-EXECUTION): the thread traces, reads-from, the
asynchronous effects, and the histories of the synchronization objects. -/
structure Execution where
  /-- The finite event trace of each thread, indexed by the thread's id in the grid. -/
  tr : Nat → List Event
  /-- For read `e` and byte `k` of its footprint: the write it read from, or `none` for
  the initial write `W0`. -/
  rf : AsyncCopy.Ref → Nat → Option AsyncCopy.Ref
  /-- Independent asynchronous accesses and completion notifications. -/
  async : AsyncCopy.Snapshot := {}
  /-- Delivered tcgen05.commit notifications, indexed by destination cluster rank. -/
  tcNotified : EvId → Finset (Fin 16) := fun _ => ∅
  /-- Independent per-target CLC response writes and notifications. -/
  clc : EvId → Clc.Effects := fun _ => {}
  /-- Tensor-copy observations, tied to the spec of the actual issue by TensorOk. -/
  tensor : EvId → Option TensorCopy.Observation := fun _ => none
  /-- Independent shared-to-global tensor reads, writes and completion observations. -/
  tensorStores : EvId → Option TensorStore.Observation := fun _ => none
  /-- Each CTA's Tensor Memory allocator history, indexed by the CTA's grid id. -/
  tmemHistory : Nat → List Tmem.Pair.Requests := fun _ => []
  /-- The completed cta_group::2 operations: the even CTA's and the odd CTA's warp requests. -/
  tmemPairing : List (Tmem.Pair.WarpRequest × Tmem.Pair.WarpRequest) := []
  /-- Nondeterministic peer-wait choice of cta_group::2 dealloc/relinquish instances
  (DEP-TMEM-ALLOC-WAIT); other instances ignore it. Choices on issued requests are preserved
  by extension. -/
  tmemPairBlocks : EvId → Bool := fun _ => false
  /-- One common ownership state for all requests in this grid. -/
  clcState : Clc.State := Clc.initial
  /-- One atomic operation history per mbarrier address, including failed polls. -/
  objects : Loc → List (MBarrier.Record AsyncCopy.Ref) := fun _ => []
  /-- Actual warp arrivals and exits for each CTA's named barrier resources. -/
  barriers : Nat → List (CtaBarrier.Record EvId) := fun _ => []
  /-- Collective cluster barrier arrivals, completed waits and exits, by cluster ID. -/
  clusters : Nat → List (ClusterBarrier.Record EvId) := fun _ => []
  /-- A concrete choice for each unspecified allocated launch byte. Known `Mem0` bytes
  take precedence. This is initial content, not a mutable memory state. -/
  initial : Loc → Byte := fun _ => (.bits 8 0, 0)
  /-- The Fence-SC order (§8.9.3) between `fence.sc` events, determined at runtime
  (MEM-FENCE-SC). -/
  fenceSC : EvId → EvId → Prop := fun _ _ => False

/-- Resolve an allocated launch byte, keeping a known value or the execution's fixed
choice for this address. -/
def Execution.initialByte (X : Execution) (c : Option Byte) (l : Loc) : Option Byte :=
  some (c.getD (X.initial l))

/-! ## THREAD-TEMPLATE — event templates
Statement: A template is the event that an instruction performs with its returned values still open:
  a read is a function of the bytes it returns, a shuffle of the value it receives, and a `try_wait`
  of whether it succeeded. The thread rules instantiate a template with any returned value, and the
  execution rules decide which values are possible.

Defs: Tmpl

Source:
- none (a device of the definition)

Direction: representation

Effect: A template is the event an instruction performs, with what it returns still open: a read is
  a function of the bytes it returns, an atomic read-modify-write a function of the bytes it reads,
  which gives the bytes it writes and the thread's next state, a shuffle a function of the value it
  receives, a `try_wait` a function of whether it succeeded, a read of changing special registers a
  function of the values read; bulk-copy effects live independently in `Execution.async`. Also open
  are the address `tcgen05.alloc` stores, the results of `tcgen05.mma` and `tcgen05.ld`
  (THREAD-TC-EVENT) and the bytes a warp-level matrix instruction receives (DEP-WARP-MATRIX). The
  thread rules (THREAD-RUN) instantiate a template with any returned values; the execution rules
  decide which values are possible.
-/

/-- An event of a thread with the value it returns left open, together with the thread's state
after it (THREAD-TEMPLATE). -/
inductive Tmpl where
  | setMaxReg (increase : Bool) (count : Nat) (t : TState)
  | warpBar (mask : Nat) (t : TState)
  | elect (mask : Nat) (k : Nat → TState)
  | read (a : Acc) (k : List (Option Byte) → TState)
  | readNC (a : Acc) (k : List (Option Byte) → TState)
  | write (a : Acc) (bs : List Byte) (t : TState)
  /-- An atomic read-modify-write of `a`: `f` gives the bytes written from the bytes read, and `k`
  the thread's state after it. -/
  | rmw (a : Acc) (f : List (Option Byte) → Exec (List Byte)) (k : List (Option Byte) → TState)
  | bar (id : Nat) (t : TState) (count : Option Nat := none) (mode : BarMode := .sync)
  | cluster (op : ClusterOp) (t : TState)
  | clcQuery (query : ClcQuery) (response : ClcResponse) (t : TState)
  | clcIssue (spec : Clc.Spec) (targets : List Nat) (t : TState)
  | tensorIssue (mapAddress : Nat) (spec : TensorCopy.Spec) (t : TState)
  | tensorStore (mapAddress : Nat) (spec : TensorStore.Spec) (t : TState)
  | bulkCommit (t : TState)
  | bulkWait (mode : BulkGroup.WaitMode) (remaining : Nat) (t : TState)
  | shfl (mode : ShflMode) (a : Value) (b c : Nat) (k : Value → Bool → TState)
  | vote (mask : Nat) (a : Bool) (k : BitVec 32 → TState)
  | voteMode (mode : VoteMode) (mask : Nat) (a : Bool) (k : Bool → TState)
  | redux (op : ReduxOp) (signed : Bool) (mask : Nat) (a : BitVec 32) (k : BitVec 32 → TState)
  | match_ (all wide : Bool) (mask : Nat) (a : BitVec 64) (k : BitVec 32 → Bool → TState)
  | activemask (k : BitVec 32 → TState)
  /-- A warp-level matrix instruction contributing `own`; the bytes received are open. -/
  | matrix (op : MatrixOp) (own : List (Option Byte)) (k : List (Option Byte) → TState)
  | exit
  | ub (f : Fault)
  | mbInit (m : Loc) (count : Nat) (t : TState)
  | mbInval (m : Loc) (t : TState)
  | fence (sem : FenceSem) (scope : MbarScope) (t : TState)
  | fenceProxy (k : ProxyFence) (scope : Option MbarScope) (t : TState)
  | fenceMbarInit (t : TState)
  | arrive (m : Loc) (tx : Nat) (t : TState) (count : Nat := 1) (release : Bool := true)
      (scope : MbarScope := .cta)
  | copy (s : AsyncCopy.Spec) (t : TState)
  | bulkPrefetch (src : Acc) (t : TState)
  | asyncCommit (t : TState)
  | asyncWait (remaining : Nat) (t : TState)
  | asyncArrive (m : Loc) (noinc : Bool) (t : TState)
  | wait (m : Loc) (parity : Nat) (k : Bool → TState) (acquire : Bool := true)
      (scope : MbarScope := .cta)
  /-- A `tcgen05` event that returns nothing. -/
  | tc (k : TcKind) (t : TState)
  /-- The address store of `tcgen05.alloc` to `dst`: the address of lane 0 and an open column
  (below `2 ^ 16`, the column field of a Tensor Memory address). -/
  | tcAllocStore (dst : Loc) (t : TState)
  /-- `tcgen05.ld` of shape `shape` of `n` registers: the values returned are open. -/
  | tcLd (a n : Nat) (shape : TcShape) (k : List Value → TState)
  | tensorPrefetch (mapAddress : Nat) (spec : TensorPrefetch.Spec) (t : TState)
  /-- A read of the special registers that change while the thread runs, each with the exclusive
  bound of its value, as a function of the values read (THREAD-SREG). -/
  | sreg (reads : List (SReg × Nat)) (k : List Nat → TState)

/-! ## ASM-INTERFACE — the interface of a kernel assumption
Statement: A kernel states its own assumptions, each of which refines what the core leaves undefined
  or adds a condition. An assumption can supply a rule for the instructions it selects in place of
  the core's, allow `ld.global.nc` at chosen sites, supply floating-point arithmetic for MMAs and
  reductions, add undefined behaviour, restrict the executions, or add the synchronization and
  ordering that its hooks select. Each of these is declared in the kernel's theorem.

Defs: Assumption

Source:
- none (per-kernel trust, listed in each theorem)

Direction: interface

Effect: An assumption refines what the core leaves undefined, and each kernel declares its own,
  scoped to what its proof relies on. Its fields differ in risk: `localRule` replaces the core's
  rule for the instructions and states it selects (THREAD-LOCAL), which is the trust class of
  `segmentRule`, and receives the thread state, so it can be limited to instruction forms or sites;
  it returns `none` for every other instruction, which keeps the core's rule; `ncLoads` allows
  `ld.global.nc` at the sites (`pc`) it selects; `mmaRule` supplies only floating MMA arithmetic,
  with no memory ordering or accumulator-provenance guarantee; `matrixMmaRule` supplies only the
  floating arithmetic of one result element of a warp-level `mma` or `mma.sp` (DEP-WARP-MMA);
  `rmwRule` supplies only the floating arithmetic of one element of an `atom`, a `red` or a tensor
  reduction (THREAD-ATOMIC-OP), with no ordering or source; `ub` adds undefined behaviour, which is
  only stricter; `wf` removes executions, which can make a theorem vacuous, so every use of `wf`
  must be justified in the assumption's own contract. `clusterScopeMbar` adds synchronization: at
  the sites (`pc`) it selects, `.cta`-scoped mbarrier release arrivals and acquire waits are treated
  as `.cluster`-scoped (THREAD-RUN), which adds `baseCausality` edges the ISA does not guarantee and
  so can make a theorem unsound for hardware that does not provide them. Further hooks are off
  unless an assumption selects a site, and each is consulted through one definition only.
  `segmentRule` replaces instruction semantics: at a local instruction it may take the straight-line
  code from there as one local step with its own outcome (THREAD-LOCAL), also over forms the core
  defines (trust). `tcLdWait` adds ordering: a `tcgen05.ld` at a selected site is followed by an
  implicit `tcgen05.wait::ld` at the same site (THREAD-RUN, trust). `tcStWaitLd` orders earlier
  Tensor Memory reads: a selected `tcgen05.st` is preceded by an implicit `tcgen05.wait::ld`
  at the same site (THREAD-RUN, trust). `commitInOrder` adds ordering:
  the arrive-on of a `tcgen05.commit` at a selected site completes before the issuing thread's next
  commit's arrive-on at the same rank starts, an edge of the lifetime order (ERR-SHARED-LIFETIME
  `LifetimeStep`, trust). `storeReadsBeforeExit` adds a lifetime edge from the shared source read
  completion of a selected tensor store to its issuer's subsequent exit (ERR-SHARED-LIFETIME,
  trust). `uniPoll` removes a safety rejection: two executions of a selected
  `bra.uni` guarded by the predicate of the `mbarrier.try_wait` right before it, by lanes of one
  warp whose records right before are polls of one mbarrier, are not compared, whatever the polls'
  parities (ERR-NONUNIFORM-GUARD `PollAgreeExempt`, trust). `regSyncExempt` removes a safety
  rejection: a `setmaxnreg` request at a selected site is not required to follow the previous
  request of its warpgroup in the base causality order (ERR-SETMAXNREG, the fourth clause of
  `SetMaxNReg.UnsafeAt`, trust); the direction, count, warpgroup and same-ordinal checks stay.
-/

/-- A kernel's own assumption: a statement of what is assumed about the hardware, and the hooks
through which it refines the core (ASM-INTERFACE). -/
structure Assumption where
  name : String
  /-- What is assumed about the hardware, with the evidence for it. -/
  statement : String
  /-- A rule for the local operations and states it selects, in place of the core's rule; `none`
  keeps the core's rule. -/
  localRule : Launch → Nat → TState → Op → Option (Exec TState) := fun _ _ _ _ => none
  /-- Numerical interpretation of one floating MMA result cell. Inputs are the observed
  operand bytes and an independently justified old accumulator; this grants no visibility. -/
  mmaRule : TcMma.Descriptor → Bool → List (Option Byte) → List (Option Byte) →
    Option Value → Nat → Nat → Option (Exec Value) := fun _ _ _ _ _ _ _ => none
  /-- Numerical interpretation of one floating element of an atomic read-modify-write (`atom`,
  `red`) or of a tensor reduction: the operation, the element type, the old value in memory and
  the operand. This grants no visibility. -/
  rmwRule : AtomOp → DType → Value → Value → Option (Exec Value) := fun _ _ _ _ => none
  /-- Numerical interpretation of one floating result element of a warp-level `mma` or `mma.sp`
  with element types `t`: the A elements of its row, the B elements of its column, paired in
  order, and its C element. This grants no visibility. -/
  matrixMmaRule : MmaTypes → List Value → List Value → Value → Option (Exec Value) :=
    fun _ _ _ _ => none
  /-- The sites (`pc`) where `ld.global.nc` is allowed (the core has no rule for it). -/
  ncLoads : Nat → Bool := fun _ => false
  /-- Extra conditions on possible executions, e.g. what an `nc` read returns. -/
  wf : Launch → Mem0 → Execution → Prop := fun _ _ _ => True
  /-- Extra undefined behaviour, e.g. writing bytes an `nc` read reads. -/
  ub : Launch → Mem0 → Execution → Prop := fun _ _ _ => False
  /-- The sites (`pc`) whose `.cta`-scoped mbarrier release arrivals and acquire waits
  synchronize at cluster scope. -/
  clusterScopeMbar : Nat → Bool := fun _ => false
  /-- At the thread's `pc`, `some r` takes the straight-line code from there as one local step
  with outcome `r` (the state after it, or a fault), before the instruction rules
  (THREAD-LOCAL). -/
  segmentRule : Launch → Nat → TState → Option (Exec TState) := fun _ _ _ => none
  /-- The `tcgen05.ld` sites (`pc`) followed by an implicit `tcgen05.wait::ld` (THREAD-RUN). -/
  tcLdWait : Nat → Bool := fun _ => false
  /-- The `tcgen05.st` sites preceded by an implicit `tcgen05.wait::ld` (THREAD-RUN). -/
  tcStWaitLd : Nat → Bool := fun _ => false
  /-- The `tcgen05.commit` sites whose arrive-on completes before the arrive-on of the issuing
  thread's next commit at the same rank (ERR-SHARED-LIFETIME). -/
  commitInOrder : Nat → Bool := fun _ => false
  /-- The tensor-store sites whose source reads complete before the issuing thread exits
  (ERR-SHARED-LIFETIME). -/
  storeReadsBeforeExit : Nat → Bool := fun _ => false
  /-- The guarded `bra.uni` sites (`pc`) after a poll whose executions by two lanes of a warp are
  not compared when both polls are of one mbarrier, whatever their parities
  (ERR-NONUNIFORM-GUARD). -/
  uniPoll : Nat → Bool := fun _ => false
  /-- The `setmaxnreg` request sites (`pc`) that are exempt from the requirement that the previous
  request of the warpgroup is ordered before them (ERR-SETMAXNREG). -/
  regSyncExempt : Nat → Bool := fun _ => false

end

end PTX
